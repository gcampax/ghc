{-# LANGUAGE CPP #-}

module TcInteract (
     solveSimpleGivens,    -- Solves [EvVar],GivenLoc
     solveSimpleWanteds    -- Solves Cts
  ) where

#include "HsVersions.h"

import BasicTypes ()
import HsTypes ( hsIPNameFS )
import FastString
import TcCanonical
import TcFlatten
import VarSet
import Type
import Kind (isKind)
import Unify
import InstEnv( DFunInstType, lookupInstEnv, instanceDFunId )
import CoAxiom(sfInteractTop, sfInteractInert)

import Var
import TcType
import PrelNames ( knownNatClassName, knownSymbolClassName, ipClassNameKey,
                   callStackTyConKey, typeableClassName )
import Id( idType )
import Class
import TyCon
import FunDeps
import FamInst
import Inst( tyVarsOfCt )

import TcEvidence
import Outputable

import TcRnTypes
import TcErrors
import TcSMonad
import Bag

import Data.List( partition, foldl', deleteFirstsBy )
import SrcLoc
import VarEnv

import Control.Monad
import Maybes( isJust )
import Pair (Pair(..))
import Unique( hasKey )
import DynFlags
import Util

{-
**********************************************************************
*                                                                    *
*                      Main Interaction Solver                       *
*                                                                    *
**********************************************************************

Note [Basic Simplifier Plan]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
1. Pick an element from the WorkList if there exists one with depth
   less than our context-stack depth.

2. Run it down the 'stage' pipeline. Stages are:
      - canonicalization
      - inert reactions
      - spontaneous reactions
      - top-level intreactions
   Each stage returns a StopOrContinue and may have sideffected
   the inerts or worklist.

   The threading of the stages is as follows:
      - If (Stop) is returned by a stage then we start again from Step 1.
      - If (ContinueWith ct) is returned by a stage, we feed 'ct' on to
        the next stage in the pipeline.
4. If the element has survived (i.e. ContinueWith x) the last stage
   then we add him in the inerts and jump back to Step 1.

If in Step 1 no such element exists, we have exceeded our context-stack
depth and will simply fail.

Note [Unflatten after solving the simple wanteds]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We unflatten after solving the wc_simples of an implication, and before attempting
to float. This means that

 * The fsk/fmv flatten-skolems only survive during solveSimples.  We don't
   need to worry about then across successive passes over the constraint tree.
   (E.g. we don't need the old ic_fsk field of an implication.

 * When floating an equality outwards, we don't need to worry about floating its
   associated flattening constraints.

 * Another tricky case becomes easy: Trac #4935
       type instance F True a b = a
       type instance F False a b = b

       [w] F c a b ~ gamma
       (c ~ True) => a ~ gamma
       (c ~ False) => b ~ gamma

   Obviously this is soluble with gamma := F c a b, and unflattening
   will do exactly that after solving the simple constraints and before
   attempting the implications.  Before, when we were not unflattening,
   we had to push Wanted funeqs in as new givens.  Yuk!

   Another example that becomes easy: indexed_types/should_fail/T7786
      [W] BuriedUnder sub k Empty ~ fsk
      [W] Intersect fsk inv ~ s
      [w] xxx[1] ~ s
      [W] forall[2] . (xxx[1] ~ Empty)
                   => Intersect (BuriedUnder sub k Empty) inv ~ Empty

Note [Running plugins on unflattened wanteds]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
There is an annoying mismatch between solveSimpleGivens and
solveSimpleWanteds, because the latter needs to fiddle with the inert
set, unflatten and and zonk the wanteds.  It passes the zonked wanteds
to runTcPluginsWanteds, which produces a replacement set of wanteds,
some additional insolubles and a flag indicating whether to go round
the loop again.  If so, prepareInertsForImplications is used to remove
the previous wanteds (which will still be in the inert set).  Note
that prepareInertsForImplications will discard the insolubles, so we
must keep track of them separately.
-}

solveSimpleGivens :: CtLoc -> [EvVar] -> TcS ()
solveSimpleGivens loc givens
  | null givens  -- Shortcut for common case
  = return ()
  | otherwise
  = go (map mk_given_ct givens)
  where
    mk_given_ct ev_id = mkNonCanonical (CtGiven { ctev_evtm = EvId ev_id
                                                , ctev_pred = evVarPred ev_id
                                                , ctev_loc  = loc })
    go givens = do { solveSimples (listToBag givens)
                   ; new_givens <- runTcPluginsGiven
                   ; when (notNull new_givens) (go new_givens)
                   }

solveSimpleWanteds :: Cts -> TcS WantedConstraints
solveSimpleWanteds = go emptyBag
  where
    go insols0 wanteds
      = do { solveSimples wanteds
           ; (implics, tv_eqs, fun_eqs, insols, others) <- getUnsolvedInerts
           ; unflattened_eqs <- unflatten tv_eqs fun_eqs
              -- See Note [Unflatten after solving the simple wanteds]

           ; zonked <- zonkSimples (others `andCts` unflattened_eqs)
             -- Postcondition is that the wl_simples are zonked

           ; (wanteds', insols', rerun) <- runTcPluginsWanted zonked
              -- See Note [Running plugins on unflattened wanteds]
           ; let all_insols = insols0 `unionBags` insols `unionBags` insols'

           ; if rerun then do { updInertTcS prepareInertsForImplications
                              ; go all_insols wanteds' }
                      else return (WC { wc_simple = wanteds'
                                      , wc_insol  = all_insols
                                      , wc_impl   = implics }) }


-- The main solver loop implements Note [Basic Simplifier Plan]
---------------------------------------------------------------
solveSimples :: Cts -> TcS ()
-- Returns the final InertSet in TcS
-- Has no effect on work-list or residual-iplications
-- The constraints are initially examined in left-to-right order

solveSimples cts
  = {-# SCC "solveSimples" #-}
    do { dyn_flags <- getDynFlags
       ; updWorkListTcS (\wl -> foldrBag extendWorkListCt wl cts)
       ; solve_loop (maxSubGoalDepth dyn_flags) }
  where
    solve_loop max_depth
      = {-# SCC "solve_loop" #-}
        do { sel <- selectNextWorkItem max_depth
           ; case sel of
              NoWorkRemaining     -- Done, successfuly (modulo frozen)
                -> return ()
              MaxDepthExceeded cnt ct -- Failure, depth exceeded
                -> wrapErrTcS $ solverDepthErrorTcS cnt (ctEvidence ct)
              NextWorkItem ct     -- More work, loop around!
                -> do { runSolverPipeline thePipeline ct; solve_loop max_depth } }


-- | Extract the (inert) givens and invoke the plugins on them.
-- Remove solved givens from the inert set and emit insolubles, but
-- return new work produced so that 'solveSimpleGivens' can feed it back
-- into the main solver.
runTcPluginsGiven :: TcS [Ct]
runTcPluginsGiven = do
  (givens,_,_) <- fmap splitInertCans getInertCans
  if null givens
    then return []
    else do
      p <- runTcPlugins (givens,[],[])
      let (solved_givens, _, _) = pluginSolvedCts p
      updInertCans (removeInertCts solved_givens)
      mapM_ emitInsoluble (pluginBadCts p)
      return (pluginNewCts p)

-- | Given a bag of (flattened, zonked) wanteds, invoke the plugins on
-- them and produce an updated bag of wanteds (possibly with some new
-- work) and a bag of insolubles.  The boolean indicates whether
-- 'solveSimpleWanteds' should feed the updated wanteds back into the
-- main solver.
runTcPluginsWanted :: Cts -> TcS (Cts, Cts, Bool)
runTcPluginsWanted zonked_wanteds
  | isEmptyBag zonked_wanteds = return (zonked_wanteds, emptyBag, False)
  | otherwise                 = do
    (given,derived,_) <- fmap splitInertCans getInertCans
    p <- runTcPlugins (given, derived, bagToList zonked_wanteds)
    let (solved_givens, solved_deriveds, solved_wanteds) = pluginSolvedCts p
        (_, _, wanteds) = pluginInputCts p
    updInertCans (removeInertCts $ solved_givens ++ solved_deriveds)
    mapM_ setEv solved_wanteds
    return ( listToBag $ pluginNewCts p ++ wanteds
           , listToBag $ pluginBadCts p
           , notNull (pluginNewCts p) )
  where
    setEv :: (EvTerm,Ct) -> TcS ()
    setEv (ev,ct) = case ctEvidence ct of
      CtWanted {ctev_evar = evar} -> setWantedEvBind evar ev
      _ -> panic "runTcPluginsWanted.setEv: attempt to solve non-wanted!"

-- | A triple of (given, derived, wanted) constraints to pass to plugins
type SplitCts  = ([Ct], [Ct], [Ct])

-- | A solved triple of constraints, with evidence for wanteds
type SolvedCts = ([Ct], [Ct], [(EvTerm,Ct)])

-- | Represents collections of constraints generated by typechecker
-- plugins
data TcPluginProgress = TcPluginProgress
    { pluginInputCts  :: SplitCts
      -- ^ Original inputs to the plugins with solved/bad constraints
      -- removed, but otherwise unmodified
    , pluginSolvedCts :: SolvedCts
      -- ^ Constraints solved by plugins
    , pluginBadCts    :: [Ct]
      -- ^ Constraints reported as insoluble by plugins
    , pluginNewCts    :: [Ct]
      -- ^ New constraints emitted by plugins
    }

-- | Starting from a triple of (given, derived, wanted) constraints,
-- invoke each of the typechecker plugins in turn and return
--
--  * the remaining unmodified constraints,
--  * constraints that have been solved,
--  * constraints that are insoluble, and
--  * new work.
--
-- Note that new work generated by one plugin will not be seen by
-- other plugins on this pass (but the main constraint solver will be
-- re-invoked and they will see it later).  There is no check that new
-- work differs from the original constraints supplied to the plugin:
-- the plugin itself should perform this check if necessary.
runTcPlugins :: SplitCts -> TcS TcPluginProgress
runTcPlugins all_cts = do
    gblEnv <- getGblEnv
    foldM do_plugin initialProgress (tcg_tc_plugins gblEnv)
  where
    do_plugin :: TcPluginProgress -> TcPluginSolver -> TcS TcPluginProgress
    do_plugin p solver = do
        result <- runTcPluginTcS (uncurry3 solver (pluginInputCts p))
        return $ progress p result

    progress :: TcPluginProgress -> TcPluginResult -> TcPluginProgress
    progress p (TcPluginContradiction bad_cts) =
       p { pluginInputCts = discard bad_cts (pluginInputCts p)
         , pluginBadCts   = bad_cts ++ pluginBadCts p
         }
    progress p (TcPluginOk solved_cts new_cts) =
      p { pluginInputCts  = discard (map snd solved_cts) (pluginInputCts p)
        , pluginSolvedCts = add solved_cts (pluginSolvedCts p)
        , pluginNewCts    = new_cts ++ pluginNewCts p
        }

    initialProgress = TcPluginProgress all_cts ([], [], []) [] []

    discard :: [Ct] -> SplitCts -> SplitCts
    discard cts (xs, ys, zs) =
        (xs `without` cts, ys `without` cts, zs `without` cts)

    without :: [Ct] -> [Ct] -> [Ct]
    without = deleteFirstsBy eqCt

    eqCt :: Ct -> Ct -> Bool
    eqCt c c' = case (ctEvidence c, ctEvidence c') of
      (CtGiven   pred _ _, CtGiven   pred' _ _) -> pred `eqType` pred'
      (CtWanted  pred _ _, CtWanted  pred' _ _) -> pred `eqType` pred'
      (CtDerived pred _  , CtDerived pred' _  ) -> pred `eqType` pred'
      (_                 , _                  ) -> False

    add :: [(EvTerm,Ct)] -> SolvedCts -> SolvedCts
    add xs scs = foldl' addOne scs xs

    addOne :: SolvedCts -> (EvTerm,Ct) -> SolvedCts
    addOne (givens, deriveds, wanteds) (ev,ct) = case ctEvidence ct of
      CtGiven  {} -> (ct:givens, deriveds, wanteds)
      CtDerived{} -> (givens, ct:deriveds, wanteds)
      CtWanted {} -> (givens, deriveds, (ev,ct):wanteds)


type WorkItem = Ct
type SimplifierStage = WorkItem -> TcS (StopOrContinue Ct)

data SelectWorkItem
       = NoWorkRemaining      -- No more work left (effectively we're done!)
       | MaxDepthExceeded SubGoalCounter Ct
                              -- More work left to do but this constraint has exceeded
                              -- the maximum depth for one of the subgoal counters and we
                              -- must stop
       | NextWorkItem Ct      -- More work left, here's the next item to look at

selectNextWorkItem :: SubGoalDepth -- Max depth allowed
                   -> TcS SelectWorkItem
selectNextWorkItem max_depth
  = updWorkListTcS_return pick_next
  where
    pick_next :: WorkList -> (SelectWorkItem, WorkList)
    pick_next wl
      = case selectWorkItem wl of
          (Nothing,_)
              -> (NoWorkRemaining,wl)           -- No more work
          (Just ct, new_wl)
              | Just cnt <- subGoalDepthExceeded max_depth (ctLocDepth (ctLoc ct)) -- Depth exceeded
              -> (MaxDepthExceeded cnt ct,new_wl)
          (Just ct, new_wl)
              -> (NextWorkItem ct, new_wl)      -- New workitem and worklist

runSolverPipeline :: [(String,SimplifierStage)] -- The pipeline
                  -> WorkItem                   -- The work item
                  -> TcS ()
-- Run this item down the pipeline, leaving behind new work and inerts
runSolverPipeline pipeline workItem
  = do { initial_is <- getTcSInerts
       ; traceTcS "Start solver pipeline {" $
                  vcat [ ptext (sLit "work item = ") <+> ppr workItem
                       , ptext (sLit "inerts    = ") <+> ppr initial_is]

       ; bumpStepCountTcS    -- One step for each constraint processed
       ; final_res  <- run_pipeline pipeline (ContinueWith workItem)

       ; final_is <- getTcSInerts
       ; case final_res of
           Stop ev s       -> do { traceFireTcS ev s
                                 ; traceTcS "End solver pipeline (discharged) }"
                                       (ptext (sLit "inerts =") <+> ppr final_is)
                                 ; return () }
           ContinueWith ct -> do { traceFireTcS (ctEvidence ct) (ptext (sLit "Kept as inert"))
                                 ; traceTcS "End solver pipeline (not discharged) }" $
                                       vcat [ ptext (sLit "final_item =") <+> ppr ct
                                            , pprTvBndrs (varSetElems $ tyVarsOfCt ct)
                                            , ptext (sLit "inerts     =") <+> ppr final_is]
                                 ; insertInertItemTcS ct }
       }
  where run_pipeline :: [(String,SimplifierStage)] -> StopOrContinue Ct
                     -> TcS (StopOrContinue Ct)
        run_pipeline [] res        = return res
        run_pipeline _ (Stop ev s) = return (Stop ev s)
        run_pipeline ((stg_name,stg):stgs) (ContinueWith ct)
          = do { traceTcS ("runStage " ++ stg_name ++ " {")
                          (text "workitem   = " <+> ppr ct)
               ; res <- stg ct
               ; traceTcS ("end stage " ++ stg_name ++ " }") empty
               ; run_pipeline stgs res }

{-
Example 1:
  Inert:   {c ~ d, F a ~ t, b ~ Int, a ~ ty} (all given)
  Reagent: a ~ [b] (given)

React with (c~d)     ==> IR (ContinueWith (a~[b]))  True    []
React with (F a ~ t) ==> IR (ContinueWith (a~[b]))  False   [F [b] ~ t]
React with (b ~ Int) ==> IR (ContinueWith (a~[Int]) True    []

Example 2:
  Inert:  {c ~w d, F a ~g t, b ~w Int, a ~w ty}
  Reagent: a ~w [b]

React with (c ~w d)   ==> IR (ContinueWith (a~[b]))  True    []
React with (F a ~g t) ==> IR (ContinueWith (a~[b]))  True    []    (can't rewrite given with wanted!)
etc.

Example 3:
  Inert:  {a ~ Int, F Int ~ b} (given)
  Reagent: F a ~ b (wanted)

React with (a ~ Int)   ==> IR (ContinueWith (F Int ~ b)) True []
React with (F Int ~ b) ==> IR Stop True []    -- after substituting we re-canonicalize and get nothing
-}

thePipeline :: [(String,SimplifierStage)]
thePipeline = [ ("canonicalization",        TcCanonical.canonicalize)
              , ("interact with inerts",    interactWithInertsStage)
              , ("top-level reactions",     topReactionsStage) ]

{-
*********************************************************************************
*                                                                               *
                       The interact-with-inert Stage
*                                                                               *
*********************************************************************************

Note [The Solver Invariant]
~~~~~~~~~~~~~~~~~~~~~~~~~~~
We always add Givens first.  So you might think that the solver has
the invariant

   If the work-item is Given,
   then the inert item must Given

But this isn't quite true.  Suppose we have,
    c1: [W] beta ~ [alpha], c2 : [W] blah, c3 :[W] alpha ~ Int
After processing the first two, we get
     c1: [G] beta ~ [alpha], c2 : [W] blah
Now, c3 does not interact with the the given c1, so when we spontaneously
solve c3, we must re-react it with the inert set.  So we can attempt a
reaction between inert c2 [W] and work-item c3 [G].

It *is* true that [Solver Invariant]
   If the work-item is Given,
   AND there is a reaction
   then the inert item must Given
or, equivalently,
   If the work-item is Given,
   and the inert item is Wanted/Derived
   then there is no reaction
-}

-- Interaction result of  WorkItem <~> Ct

type StopNowFlag = Bool    -- True <=> stop after this interaction

interactWithInertsStage :: WorkItem -> TcS (StopOrContinue Ct)
-- Precondition: if the workitem is a CTyEqCan then it will not be able to
-- react with anything at this stage.

interactWithInertsStage wi
  = do { inerts <- getTcSInerts
       ; let ics = inert_cans inerts
       ; case wi of
             CTyEqCan    {} -> interactTyVarEq ics wi
             CFunEqCan   {} -> interactFunEq   ics wi
             CIrredEvCan {} -> interactIrred   ics wi
             CDictCan    {} -> interactDict    ics wi
             _ -> pprPanic "interactWithInerts" (ppr wi) }
                -- CHoleCan are put straight into inert_frozen, so never get here
                -- CNonCanonical have been canonicalised

data InteractResult
   = IRKeep      -- Keep the existing inert constraint in the inert set
   | IRReplace   -- Replace the existing inert constraint with the work item
   | IRDelete    -- Delete the existing inert constraint from the inert set

instance Outputable InteractResult where
  ppr IRKeep    = ptext (sLit "keep")
  ppr IRReplace = ptext (sLit "replace")
  ppr IRDelete  = ptext (sLit "delete")

solveOneFromTheOther :: CtEvidence  -- Inert
                     -> CtEvidence  -- WorkItem
                     -> TcS (InteractResult, StopNowFlag)
-- Preconditions:
-- 1) inert and work item represent evidence for the /same/ predicate
-- 2) ip/class/irred evidence (no coercions) only
solveOneFromTheOther ev_i ev_w
  | isDerived ev_w
  = return (IRKeep, True)

  | isDerived ev_i -- The inert item is Derived, we can just throw it away,
                   -- The ev_w is inert wrt earlier inert-set items,
                   -- so it's safe to continue on from this point
  = return (IRDelete, False)

  | CtWanted { ctev_evar = ev_id } <- ev_w
  = do { setWantedEvBind ev_id (ctEvTerm ev_i)
       ; return (IRKeep, True) }

  | CtWanted { ctev_evar = ev_id } <- ev_i
  = do { setWantedEvBind ev_id (ctEvTerm ev_w)
       ; return (IRReplace, True) }

  -- So they are both Given
  -- See Note [Replacement vs keeping]
  | lvl_i == lvl_w
  = do { binds <- getTcEvBindsMap
       ; if has_binding binds ev_w && not (has_binding binds ev_i)
         then return (IRReplace, True)
         else return (IRKeep,    True) }

   | otherwise   -- Both are Given
   = return (if use_replacement then IRReplace else IRKeep, True)
   where
     pred  = ctEvPred ev_i
     loc_i = ctEvLoc ev_i
     loc_w = ctEvLoc ev_w
     lvl_i = ctLocLevel loc_i
     lvl_w = ctLocLevel loc_w

     has_binding binds ev
       | EvId v <- ctEvTerm ev = isJust (lookupEvBind binds v)
       | otherwise             = True

     use_replacement
       | isIPPred pred = lvl_w > lvl_i
       | otherwise     = lvl_w < lvl_i

{-
Note [Replacement vs keeping]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
When we have two Given constraints both of type (C tys), say, which should
we keep?

  * For implicit parameters we want to keep the innermost (deepest)
    one, so that it overrides the outer one.
    See Note [Shadowing of Implicit Parameters]

  * For everything else, we want to keep the outermost one.  Reason: that
    makes it more likely that the inner one will turn out to be unused,
    and can be reported as redundant.  See Note [Tracking redundant constraints]
    in TcSimplify.

    It transpires that using the outermost one is reponsible for an
    8% performance improvement in nofib cryptarithm2, compared to
    just rolling the dice.  I didn't investigate why.

  * If there is no "outermost" one, we keep the one that has a non-trivial
    evidence binding.  Note [Tracking redundant constraints] again.
    Example:  f :: (Eq a, Ord a) => blah
    then we may find [G] sc_sel (d1::Ord a) :: Eq a
                     [G] d2 :: Eq a
    We want to discard d2 in favour of the superclass selection from
    the Ord dictionary.

  * Finally, when there is still a choice, use IRKeep rather than
    IRReplace, to avoid unnecesary munging of the inert set.

Doing the depth-check for implicit parameters, rather than making the work item
always overrride, is important.  Consider

    data T a where { T1 :: (?x::Int) => T Int; T2 :: T a }

    f :: (?x::a) => T a -> Int
    f T1 = ?x
    f T2 = 3

We have a [G] (?x::a) in the inert set, and at the pattern match on T1 we add
two new givens in the work-list:  [G] (?x::Int)
                                  [G] (a ~ Int)
Now consider these steps
  - process a~Int, kicking out (?x::a)
  - process (?x::Int), the inner given, adding to inert set
  - process (?x::a), the outer given, overriding the inner given
Wrong!  The depth-check ensures that the inner implicit parameter wins.
(Actually I think that the order in which the work-list is processed means
that this chain of events won't happen, but that's very fragile.)

*********************************************************************************
*                                                                               *
                   interactIrred
*                                                                               *
*********************************************************************************
-}

-- Two pieces of irreducible evidence: if their types are *exactly identical*
-- we can rewrite them. We can never improve using this:
-- if we want ty1 :: Constraint and have ty2 :: Constraint it clearly does not
-- mean that (ty1 ~ ty2)
interactIrred :: InertCans -> Ct -> TcS (StopOrContinue Ct)

interactIrred inerts workItem@(CIrredEvCan { cc_ev = ev_w })
  | let pred = ctEvPred ev_w
        (matching_irreds, others) = partitionBag (\ct -> ctPred ct `tcEqType` pred)
                                                 (inert_irreds inerts)
  , (ct_i : rest) <- bagToList matching_irreds
  , let ctev_i = ctEvidence ct_i
  = ASSERT( null rest )
    do { (inert_effect, stop_now) <- solveOneFromTheOther ctev_i ev_w
       ; case inert_effect of
            IRKeep    -> return ()
            IRDelete  -> updInertIrreds (\_ -> others)
            IRReplace -> updInertIrreds (\_ -> others `snocCts` workItem)
                         -- These const upd's assume that solveOneFromTheOther
                         -- has no side effects on InertCans
       ; if stop_now then
            return (Stop ev_w (ptext (sLit "Irred equal") <+> parens (ppr inert_effect)))
       ; else
            continueWith workItem }

  | otherwise
  = continueWith workItem

interactIrred _ wi = pprPanic "interactIrred" (ppr wi)

{-
*********************************************************************************
*                                                                               *
                   interactDict
*                                                                               *
*********************************************************************************
-}

interactDict :: InertCans -> Ct -> TcS (StopOrContinue Ct)
interactDict inerts workItem@(CDictCan { cc_ev = ev_w, cc_class = cls, cc_tyargs = tys })
  -- don't ever try to solve CallStack IPs directly from other dicts,
  -- we always build new dicts instead.
  -- See Note [Overview of implicit CallStacks]
  | [_ip, ty] <- tys
  , isWanted ev_w
  , Just mkEvCs <- isCallStackIP (ctEvLoc ev_w) cls ty
  = do let ev_cs =
             case lookupInertDict inerts (ctEvLoc ev_w) cls tys of
               Just ev | isGiven ev -> mkEvCs (ctEvTerm ev)
               _ -> mkEvCs (EvCallStack EvCsEmpty)

       -- now we have ev_cs :: CallStack, but the evidence term should
       -- be a dictionary, so we have to coerce ev_cs to a
       -- dictionary for `IP ip CallStack`
       let ip_ty = mkClassPred cls tys
       let ev_tm = mkEvCast (EvCallStack ev_cs) (TcCoercion $ wrapIP ip_ty)
       addSolvedDict ev_w cls tys
       setWantedEvBind (ctEvId ev_w) ev_tm
       stopWith ev_w "Wanted CallStack IP"

  | Just ctev_i <- lookupInertDict inerts (ctEvLoc ev_w) cls tys
  = do { (inert_effect, stop_now) <- solveOneFromTheOther ctev_i ev_w
       ; case inert_effect of
           IRKeep    -> return ()
           IRDelete  -> updInertDicts $ \ ds -> delDict ds cls tys
           IRReplace -> updInertDicts $ \ ds -> addDict ds cls tys workItem
       ; if stop_now then
            return (Stop ev_w (ptext (sLit "Dict equal") <+> parens (ppr inert_effect)))
         else
            continueWith workItem }

  | cls `hasKey` ipClassNameKey
  , isGiven ev_w
  = interactGivenIP inerts workItem

  | otherwise
  = do { mapBagM_ (addFunDepWork workItem) 
                  (findDictsByClass (inert_dicts inerts) cls)
               -- Create derived fds and keep on going.
               -- No need to check flavour; fundeps work between
               -- any pair of constraints, regardless of flavour
               -- Importantly we don't throw workitem back in the 
               -- worklist bebcause this can cause loops (see #5236)
       ; continueWith workItem  }

interactDict _ wi = pprPanic "interactDict" (ppr wi)

interactGivenIP :: InertCans -> Ct -> TcS (StopOrContinue Ct)
-- Work item is Given (?x:ty)
-- See Note [Shadowing of Implicit Parameters]
interactGivenIP inerts workItem@(CDictCan { cc_ev = ev, cc_class = cls
                                          , cc_tyargs = tys@(ip_str:_) })
  = do { updInertCans $ \cans -> cans { inert_dicts = addDict filtered_dicts cls tys workItem }
       ; stopWith ev "Given IP" }
  where
    dicts           = inert_dicts inerts
    ip_dicts        = findDictsByClass dicts cls
    other_ip_dicts  = filterBag (not . is_this_ip) ip_dicts
    filtered_dicts  = addDictsByClass dicts cls other_ip_dicts

    -- Pick out any Given constraints for the same implicit parameter
    is_this_ip (CDictCan { cc_ev = ev, cc_tyargs = ip_str':_ })
       = isGiven ev && ip_str `tcEqType` ip_str'
    is_this_ip _ = False

interactGivenIP _ wi = pprPanic "interactGivenIP" (ppr wi)

addFunDepWork :: Ct -> Ct -> TcS ()
-- Add derived constraints from type-class functional dependencies.
addFunDepWork work_ct inert_ct
  = emitFunDepDeriveds $
    improveFromAnother derived_loc inert_pred work_pred
                -- We don't really rewrite tys2, see below _rewritten_tys2, so that's ok
                -- NB: We do create FDs for given to report insoluble equations that arise
                -- from pairs of Givens, and also because of floating when we approximate
                -- implications. The relevant test is: typecheck/should_fail/FDsFromGivens.hs
                -- Also see Note [When improvement happens]
  where
    work_pred  = ctPred work_ct
    inert_pred = ctPred inert_ct
    work_loc   = ctLoc work_ct
    inert_loc  = ctLoc inert_ct
    derived_loc = work_loc { ctl_origin = FunDepOrigin1 work_pred  work_loc
                                                        inert_pred inert_loc }

{-
Note [Shadowing of Implicit Parameters]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Consider the following example:

f :: (?x :: Char) => Char
f = let ?x = 'a' in ?x

The "let ?x = ..." generates an implication constraint of the form:

?x :: Char => ?x :: Char

Furthermore, the signature for `f` also generates an implication
constraint, so we end up with the following nested implication:

?x :: Char => (?x :: Char => ?x :: Char)

Note that the wanted (?x :: Char) constraint may be solved in
two incompatible ways:  either by using the parameter from the
signature, or by using the local definition.  Our intention is
that the local definition should "shadow" the parameter of the
signature, and we implement this as follows: when we add a new
*given* implicit parameter to the inert set, it replaces any existing
givens for the same implicit parameter.

This works for the normal cases but it has an odd side effect
in some pathological programs like this:

-- This is accepted, the second parameter shadows
f1 :: (?x :: Int, ?x :: Char) => Char
f1 = ?x

-- This is rejected, the second parameter shadows
f2 :: (?x :: Int, ?x :: Char) => Int
f2 = ?x

Both of these are actually wrong:  when we try to use either one,
we'll get two incompatible wnated constraints (?x :: Int, ?x :: Char),
which would lead to an error.

I can think of two ways to fix this:

  1. Simply disallow multiple constratits for the same implicit
    parameter---this is never useful, and it can be detected completely
    syntactically.

  2. Move the shadowing machinery to the location where we nest
     implications, and add some code here that will produce an
     error if we get multiple givens for the same implicit parameter.


*********************************************************************************
*                                                                               *
                   interactFunEq
*                                                                               *
*********************************************************************************
-}

interactFunEq :: InertCans -> Ct -> TcS (StopOrContinue Ct)
-- Try interacting the work item with the inert set
interactFunEq inerts workItem@(CFunEqCan { cc_ev = ev, cc_fun = tc
                                         , cc_tyargs = args, cc_fsk = fsk })
  | Just (CFunEqCan { cc_ev = ev_i, cc_fsk = fsk_i }) <- matching_inerts
  = if ev_i `canRewriteOrSame` ev
    then  -- Rewrite work-item using inert
      do { traceTcS "reactFunEq (discharge work item):" $
           vcat [ text "workItem =" <+> ppr workItem
                , text "inertItem=" <+> ppr ev_i ]
         ; reactFunEq ev_i fsk_i ev fsk
         ; stopWith ev "Inert rewrites work item" }
    else  -- Rewrite intert using work-item
      do { traceTcS "reactFunEq (rewrite inert item):" $
           vcat [ text "workItem =" <+> ppr workItem
                , text "inertItem=" <+> ppr ev_i ]
         ; updInertFunEqs $ \ feqs -> insertFunEq feqs tc args workItem
               -- Do the updInertFunEqs before the reactFunEq, so that
               -- we don't kick out the inertItem as well as consuming it!
         ; reactFunEq ev fsk ev_i fsk_i
         ; stopWith ev "Work item rewrites inert" }

  | Just ops <- isBuiltInSynFamTyCon_maybe tc
  = do { let matching_funeqs = findFunEqsByTyCon funeqs tc
       ; let interact = sfInteractInert ops args (lookupFlattenTyVar eqs fsk)
             do_one (CFunEqCan { cc_tyargs = iargs, cc_fsk = ifsk, cc_ev = iev })
                = mapM_ (unifyDerived (ctEvLoc iev) Nominal)
                        (interact iargs (lookupFlattenTyVar eqs ifsk))
             do_one ct = pprPanic "interactFunEq" (ppr ct)
       ; mapM_ do_one matching_funeqs
       ; traceTcS "builtInCandidates 1: " $ vcat [ ptext (sLit "Candidates:") <+> ppr matching_funeqs
                                                 , ptext (sLit "TvEqs:") <+> ppr eqs ]
       ; return (ContinueWith workItem) }

  | otherwise
  = return (ContinueWith workItem)
  where
    eqs    = inert_eqs inerts
    funeqs = inert_funeqs inerts
    matching_inerts = findFunEqs funeqs tc args

interactFunEq _ wi = pprPanic "interactFunEq" (ppr wi)

lookupFlattenTyVar :: TyVarEnv EqualCtList -> TcTyVar -> TcType
-- ^ Look up a flatten-tyvar in the inert nominal TyVarEqs;
-- this is used only when dealing with a CFunEqCan
lookupFlattenTyVar inert_eqs ftv
  = case lookupVarEnv inert_eqs ftv of
      Just (CTyEqCan { cc_rhs = rhs, cc_eq_rel = NomEq } : _) -> rhs
      _                                                       -> mkTyVarTy ftv

reactFunEq :: CtEvidence -> TcTyVar    -- From this  :: F tys ~ fsk1
           -> CtEvidence -> TcTyVar    -- Solve this :: F tys ~ fsk2
           -> TcS ()
reactFunEq from_this fsk1 (CtGiven { ctev_evtm = tm, ctev_loc = loc }) fsk2
  = do { let fsk_eq_co = mkTcSymCo (evTermCoercion tm)
                         `mkTcTransCo` ctEvCoercion from_this
                         -- :: fsk2 ~ fsk1
             fsk_eq_pred = mkTcEqPred (mkTyVarTy fsk2) (mkTyVarTy fsk1)
       ; new_ev <- newGivenEvVar loc (fsk_eq_pred, EvCoercion fsk_eq_co)
       ; emitWorkNC [new_ev] }

reactFunEq from_this fuv1 (CtWanted { ctev_evar = evar }) fuv2
  = dischargeFmv evar fuv2 (ctEvCoercion from_this) (mkTyVarTy fuv1)

reactFunEq _ _ solve_this@(CtDerived {}) _
  = pprPanic "reactFunEq" (ppr solve_this)

{-
Note [Cache-caused loops]
~~~~~~~~~~~~~~~~~~~~~~~~~
It is very dangerous to cache a rewritten wanted family equation as 'solved' in our
solved cache (which is the default behaviour or xCtEvidence), because the interaction
may not be contributing towards a solution. Here is an example:

Initial inert set:
  [W] g1 : F a ~ beta1
Work item:
  [W] g2 : F a ~ beta2
The work item will react with the inert yielding the _same_ inert set plus:
    i)   Will set g2 := g1 `cast` g3
    ii)  Will add to our solved cache that [S] g2 : F a ~ beta2
    iii) Will emit [W] g3 : beta1 ~ beta2
Now, the g3 work item will be spontaneously solved to [G] g3 : beta1 ~ beta2
and then it will react the item in the inert ([W] g1 : F a ~ beta1). So it
will set
      g1 := g ; sym g3
and what is g? Well it would ideally be a new goal of type (F a ~ beta2) but
remember that we have this in our solved cache, and it is ... g2! In short we
created the evidence loop:

        g2 := g1 ; g3
        g3 := refl
        g1 := g2 ; sym g3

To avoid this situation we do not cache as solved any workitems (or inert)
which did not really made a 'step' towards proving some goal. Solved's are
just an optimization so we don't lose anything in terms of completeness of
solving.


Note [Efficient Orientation]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Suppose we are interacting two FunEqCans with the same LHS:
          (inert)  ci :: (F ty ~ xi_i)
          (work)   cw :: (F ty ~ xi_w)
We prefer to keep the inert (else we pass the work item on down
the pipeline, which is a bit silly).  If we keep the inert, we
will (a) discharge 'cw'
     (b) produce a new equality work-item (xi_w ~ xi_i)
Notice the orientation (xi_w ~ xi_i) NOT (xi_i ~ xi_w):
    new_work :: xi_w ~ xi_i
    cw := ci ; sym new_work
Why?  Consider the simplest case when xi1 is a type variable.  If
we generate xi1~xi2, porcessing that constraint will kick out 'ci'.
If we generate xi2~xi1, there is less chance of that happening.
Of course it can and should still happen if xi1=a, xi1=Int, say.
But we want to avoid it happening needlessly.

Similarly, if we *can't* keep the inert item (because inert is Wanted,
and work is Given, say), we prefer to orient the new equality (xi_i ~
xi_w).

Note [Carefully solve the right CFunEqCan]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
   ---- OLD COMMENT, NOW NOT NEEDED
   ---- because we now allow multiple
   ---- wanted FunEqs with the same head
Consider the constraints
  c1 :: F Int ~ a      -- Arising from an application line 5
  c2 :: F Int ~ Bool   -- Arising from an application line 10
Suppose that 'a' is a unification variable, arising only from
flattening.  So there is no error on line 5; it's just a flattening
variable.  But there is (or might be) an error on line 10.

Two ways to combine them, leaving either (Plan A)
  c1 :: F Int ~ a      -- Arising from an application line 5
  c3 :: a ~ Bool       -- Arising from an application line 10
or (Plan B)
  c2 :: F Int ~ Bool   -- Arising from an application line 10
  c4 :: a ~ Bool       -- Arising from an application line 5

Plan A will unify c3, leaving c1 :: F Int ~ Bool as an error
on the *totally innocent* line 5.  An example is test SimpleFail16
where the expected/actual message comes out backwards if we use
the wrong plan.

The second is the right thing to do.  Hence the isMetaTyVarTy
test when solving pairwise CFunEqCan.


*********************************************************************************
*                                                                               *
                   interactTyVarEq
*                                                                               *
*********************************************************************************
-}

interactTyVarEq :: InertCans -> Ct -> TcS (StopOrContinue Ct)
-- CTyEqCans are always consumed, so always returns Stop
interactTyVarEq inerts workItem@(CTyEqCan { cc_tyvar = tv
                                          , cc_rhs = rhs
                                          , cc_ev = ev
                                          , cc_eq_rel = eq_rel })
  | (ev_i : _) <- [ ev_i | CTyEqCan { cc_ev = ev_i, cc_rhs = rhs_i }
                             <- findTyEqs inerts tv
                         , ev_i `canRewriteOrSame` ev
                         , rhs_i `tcEqType` rhs ]
  =  -- Inert:     a ~ b
     -- Work item: a ~ b
    do { setEvBindIfWanted ev (ctEvTerm ev_i)
       ; stopWith ev "Solved from inert" }

  | Just tv_rhs <- getTyVar_maybe rhs
  , (ev_i : _) <- [ ev_i | CTyEqCan { cc_ev = ev_i, cc_rhs = rhs_i }
                             <- findTyEqs inerts tv_rhs
                         , ev_i `canRewriteOrSame` ev
                         , rhs_i `tcEqType` mkTyVarTy tv ]
  =  -- Inert:     a ~ b
     -- Work item: b ~ a
    do { setEvBindIfWanted ev
                   (EvCoercion (mkTcSymCo (ctEvCoercion ev_i)))
       ; stopWith ev "Solved from inert (r)" }

  | otherwise
  = do { tclvl <- getTcLevel
       ; if canSolveByUnification tclvl ev eq_rel tv rhs
         then do { solveByUnification ev tv rhs
                 ; n_kicked <- kickOutRewritable Given NomEq tv
                               -- Given because the tv := xi is given
                               -- NomEq because only nom. equalities are solved
                               -- by unification
                 ; return (Stop ev (ptext (sLit "Spontaneously solved") <+> ppr_kicked n_kicked)) }

         else do { traceTcS "Can't solve tyvar equality"
                       (vcat [ text "LHS:" <+> ppr tv <+> dcolon <+> ppr (tyVarKind tv)
                             , ppWhen (isMetaTyVar tv) $
                               nest 4 (text "TcLevel of" <+> ppr tv
                                       <+> text "is" <+> ppr (metaTyVarTcLevel tv))
                             , text "RHS:" <+> ppr rhs <+> dcolon <+> ppr (typeKind rhs)
                             , text "TcLevel =" <+> ppr tclvl ])
                 ; n_kicked <- kickOutRewritable (ctEvFlavour ev)
                                                 (ctEvEqRel ev)
                                                 tv
                 ; updInertCans (\ ics -> addInertCan ics workItem)
                 ; return (Stop ev (ptext (sLit "Kept as inert") <+> ppr_kicked n_kicked)) } }

interactTyVarEq _ wi = pprPanic "interactTyVarEq" (ppr wi)

-- @trySpontaneousSolve wi@ solves equalities where one side is a
-- touchable unification variable.
-- Returns True <=> spontaneous solve happened
canSolveByUnification :: TcLevel -> CtEvidence -> EqRel
                      -> TcTyVar -> Xi -> Bool
canSolveByUnification tclvl gw eq_rel tv xi
  | ReprEq <- eq_rel   -- we never solve representational equalities this way.
  = False

  | isGiven gw   -- See Note [Touchables and givens]
  = False

  | isTouchableMetaTyVar tclvl tv
  = case metaTyVarInfo tv of
      SigTv -> is_tyvar xi
      _     -> True

  | otherwise    -- Untouchable
  = False
  where
    is_tyvar xi
      = case tcGetTyVar_maybe xi of
          Nothing -> False
          Just tv -> case tcTyVarDetails tv of
                       MetaTv { mtv_info = info }
                                   -> case info of
                                        SigTv -> True
                                        _     -> False
                       SkolemTv {} -> True
                       FlatSkol {} -> False
                       RuntimeUnk  -> True

solveByUnification :: CtEvidence -> TcTyVar -> Xi -> TcS ()
-- Solve with the identity coercion
-- Precondition: kind(xi) is a sub-kind of kind(tv)
-- Precondition: CtEvidence is Wanted or Derived
-- Precondition: CtEvidence is nominal
-- Returns: workItem where
--        workItem = the new Given constraint
--
-- NB: No need for an occurs check here, because solveByUnification always
--     arises from a CTyEqCan, a *canonical* constraint.  Its invariants
--     say that in (a ~ xi), the type variable a does not appear in xi.
--     See TcRnTypes.Ct invariants.
--
-- Post: tv is unified (by side effect) with xi;
--       we often write tv := xi
solveByUnification wd tv xi
  = do { let tv_ty = mkTyVarTy tv
       ; traceTcS "Sneaky unification:" $
                       vcat [text "Unifies:" <+> ppr tv <+> ptext (sLit ":=") <+> ppr xi,
                             text "Coercion:" <+> pprEq tv_ty xi,
                             text "Left Kind is:" <+> ppr (typeKind tv_ty),
                             text "Right Kind is:" <+> ppr (typeKind xi) ]

       ; let xi' = defaultKind xi
               -- We only instantiate kind unification variables
               -- with simple kinds like *, not OpenKind or ArgKind
               -- cf TcUnify.uUnboundKVar

       ; setWantedTyBind tv xi'
       ; setEvBindIfWanted wd (EvCoercion (mkTcNomReflCo xi')) }


ppr_kicked :: Int -> SDoc
ppr_kicked 0 = empty
ppr_kicked n = parens (int n <+> ptext (sLit "kicked out"))

kickOutRewritable :: CtFlavour    -- Flavour of the equality that is
                                  -- being added to the inert set
                  -> EqRel        -- of the new equality
                  -> TcTyVar      -- The new equality is tv ~ ty
                  -> TcS Int
kickOutRewritable new_flavour new_eq_rel new_tv
  | not ((new_flavour, new_eq_rel) `eqCanRewriteFR` (new_flavour, new_eq_rel))
  = return 0  -- If new_flavour can't rewrite itself, it can't rewrite
              -- anything else, so no need to kick out anything
              -- This is a common case: wanteds can't rewrite wanteds

  | otherwise
  = do { ics <- getInertCans
       ; let (kicked_out, ics') = kick_out new_flavour new_eq_rel new_tv ics
       ; setInertCans ics'
       ; updWorkListTcS (appendWorkList kicked_out)

       ; unless (isEmptyWorkList kicked_out) $
         csTraceTcS $
         hang (ptext (sLit "Kick out, tv =") <+> ppr new_tv)
            2 (vcat [ text "n-kicked =" <+> int (workListSize kicked_out)
                    , text "n-kept fun-eqs =" <+> int (sizeFunEqMap (inert_funeqs ics'))
                    , ppr kicked_out ])
       ; return (workListSize kicked_out) }

kick_out :: CtFlavour -> EqRel -> TcTyVar -> InertCans -> (WorkList, InertCans)
kick_out new_flavour new_eq_rel new_tv (IC { inert_eqs      = tv_eqs
                                           , inert_dicts    = dictmap
                                           , inert_funeqs   = funeqmap
                                           , inert_irreds   = irreds
                                           , inert_insols   = insols })
  = (kicked_out, inert_cans_in)
  where
                -- NB: Notice that don't rewrite
                -- inert_solved_dicts, and inert_solved_funeqs
                -- optimistically. But when we lookup we have to
                -- take the substitution into account
    inert_cans_in = IC { inert_eqs      = tv_eqs_in
                       , inert_dicts    = dicts_in
                       , inert_funeqs   = feqs_in
                       , inert_irreds   = irs_in
                       , inert_insols   = insols_in }

    kicked_out = WL { wl_eqs    = tv_eqs_out
                    , wl_funeqs = feqs_out
                    , wl_rest   = bagToList (dicts_out `andCts` irs_out
                                             `andCts` insols_out)
                    , wl_implics = emptyBag }

    (tv_eqs_out, tv_eqs_in) = foldVarEnv kick_out_eqs ([], emptyVarEnv) tv_eqs
    (feqs_out,   feqs_in)   = partitionFunEqs  kick_out_ct funeqmap
    (dicts_out,  dicts_in)  = partitionDicts   kick_out_ct dictmap
    (irs_out,    irs_in)    = partitionBag     kick_out_irred irreds
    (insols_out, insols_in) = partitionBag     kick_out_ct    insols
      -- Kick out even insolubles; see Note [Kick out insolubles]

    can_rewrite :: CtEvidence -> Bool
    can_rewrite = ((new_flavour, new_eq_rel) `eqCanRewriteFR`) . ctEvFlavourRole

    kick_out_ct :: Ct -> Bool
    kick_out_ct ct = kick_out_ctev (ctEvidence ct)

    kick_out_ctev :: CtEvidence -> Bool
    kick_out_ctev ev =  can_rewrite ev
                     && new_tv `elemVarSet` tyVarsOfType (ctEvPred ev)
         -- See Note [Kicking out inert constraints]

    kick_out_irred :: Ct -> Bool
    kick_out_irred ct =  can_rewrite (cc_ev ct)
                      && new_tv `elemVarSet` closeOverKinds (tyVarsOfCt ct)
          -- See Note [Kicking out Irreds]

    kick_out_eqs :: EqualCtList -> ([Ct], TyVarEnv EqualCtList)
                 -> ([Ct], TyVarEnv EqualCtList)
    kick_out_eqs eqs (acc_out, acc_in)
      = (eqs_out ++ acc_out, case eqs_in of
                               []      -> acc_in
                               (eq1:_) -> extendVarEnv acc_in (cc_tyvar eq1) eqs_in)
      where
        (eqs_in, eqs_out) = partition keep_eq eqs

    -- implements criteria K1-K3 in Note [The inert equalities] in TcFlatten
    keep_eq (CTyEqCan { cc_tyvar = tv, cc_rhs = rhs_ty, cc_ev = ev
                      , cc_eq_rel = eq_rel })
      | tv == new_tv
      = not (can_rewrite ev)  -- (K1)

      | otherwise
      = check_k2 && check_k3
      where
        check_k2 = not (ev `eqCanRewrite` ev)
                || not (can_rewrite ev)
                || not (new_tv `elemVarSet` tyVarsOfType rhs_ty)

        check_k3
          | can_rewrite ev
          = case eq_rel of
              NomEq  -> not (rhs_ty `eqType` mkTyVarTy new_tv)
              ReprEq -> not (isTyVarExposed new_tv rhs_ty)

          | otherwise
          = True

    keep_eq ct = pprPanic "keep_eq" (ppr ct)

{-
Note [Kicking out inert constraints]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Given a new (a -> ty) inert, we want to kick out an existing inert
constraint if
  a) the new constraint can rewrite the inert one
  b) 'a' is free in the inert constraint (so that it *will*)
     rewrite it if we kick it out.

For (b) we use tyVarsOfCt, which returns the type variables /and
the kind variables/ that are directly visible in the type. Hence we
will have exposed all the rewriting we care about to make the most
precise kinds visible for matching classes etc. No need to kick out
constraints that mention type variables whose kinds contain this
variable!  (Except see Note [Kicking out Irreds].)

Note [Kicking out Irreds]
~~~~~~~~~~~~~~~~~~~~~~~~~
There is an awkward special case for Irreds.  When we have a
kind-mis-matched equality constraint (a:k1) ~ (ty:k2), we turn it into
an Irred (see Note [Equalities with incompatible kinds] in
TcCanonical). So in this case the free kind variables of k1 and k2
are not visible.  More precisely, the type looks like
   (~) k1 (a:k1) (ty:k2)
because (~) has kind forall k. k -> k -> Constraint.  So the constraint
itself is ill-kinded.  We can "see" k1 but not k2.  That's why we use
closeOverKinds to make sure we see k2.

This is not pretty. Maybe (~) should have kind
   (~) :: forall k1 k1. k1 -> k2 -> Constraint

Note [Kick out insolubles]
~~~~~~~~~~~~~~~~~~~~~~~~~~
Suppose we have an insoluble alpha ~ [alpha], which is insoluble
because an occurs check.  And then we unify alpha := [Int].
Then we really want to rewrite the insouluble to [Int] ~ [[Int]].
Now it can be decomposed.  Otherwise we end up with a "Can't match
[Int] ~ [[Int]]" which is true, but a bit confusing because the
outer type constructors match.


Note [Avoid double unifications]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The spontaneous solver has to return a given which mentions the unified unification
variable *on the left* of the equality. Here is what happens if not:
  Original wanted:  (a ~ alpha),  (alpha ~ Int)
We spontaneously solve the first wanted, without changing the order!
      given : a ~ alpha      [having unified alpha := a]
Now the second wanted comes along, but he cannot rewrite the given, so we simply continue.
At the end we spontaneously solve that guy, *reunifying*  [alpha := Int]

We avoid this problem by orienting the resulting given so that the unification
variable is on the left.  [Note that alternatively we could attempt to
enforce this at canonicalization]

See also Note [No touchables as FunEq RHS] in TcSMonad; avoiding
double unifications is the main reason we disallow touchable
unification variables as RHS of type family equations: F xis ~ alpha.


************************************************************************
*                                                                      *
*          Functional dependencies, instantiation of equations
*                                                                      *
************************************************************************

When we spot an equality arising from a functional dependency,
we now use that equality (a "wanted") to rewrite the work-item
constraint right away.  This avoids two dangers

 Danger 1: If we send the original constraint on down the pipeline
           it may react with an instance declaration, and in delicate
           situations (when a Given overlaps with an instance) that
           may produce new insoluble goals: see Trac #4952

 Danger 2: If we don't rewrite the constraint, it may re-react
           with the same thing later, and produce the same equality
           again --> termination worries.

To achieve this required some refactoring of FunDeps.hs (nicer
now!).
-}

emitFunDepDeriveds :: [FunDepEqn CtLoc] -> TcS ()
emitFunDepDeriveds fd_eqns
  = mapM_ do_one_FDEqn fd_eqns
  where
    do_one_FDEqn (FDEqn { fd_qtvs = tvs, fd_eqs = eqs, fd_loc = loc })
     | null tvs  -- Common shortcut
     = mapM_ (unifyDerived loc Nominal) eqs
     | otherwise
     = do { (subst, _) <- instFlexiTcS tvs  -- Takes account of kind substitution
          ; mapM_ (do_one_eq loc subst) eqs }

    do_one_eq loc subst (Pair ty1 ty2)
       = unifyDerived loc Nominal $
         Pair (Type.substTy subst ty1) (Type.substTy subst ty2)

{-
*********************************************************************************
*                                                                               *
                       The top-reaction Stage
*                                                                               *
*********************************************************************************
-}

topReactionsStage :: WorkItem -> TcS (StopOrContinue Ct)
topReactionsStage wi
 = do { inerts <- getTcSInerts
      ; tir <- doTopReact inerts wi
      ; case tir of
          ContinueWith wi -> return (ContinueWith wi)
          Stop ev s       -> return (Stop ev (ptext (sLit "Top react:") <+> s)) }

doTopReact :: InertSet -> WorkItem -> TcS (StopOrContinue Ct)
-- The work item does not react with the inert set, so try interaction with top-level
-- instances. Note:
--
--   (a) The place to add superclasses in not here in doTopReact stage.
--       Instead superclasses are added in the worklist as part of the
--       canonicalization process. See Note [Adding superclasses].

doTopReact inerts work_item
  = do { traceTcS "doTopReact" (ppr work_item)
       ; case work_item of
           CDictCan {}  -> doTopReactDict inerts work_item
           CFunEqCan {} -> doTopReactFunEq work_item
           _  -> -- Any other work item does not react with any top-level equations
                 return (ContinueWith work_item)  }

--------------------
doTopReactDict :: InertSet -> Ct -> TcS (StopOrContinue Ct)
-- Try to use type-class instance declarations to simplify the constraint
doTopReactDict inerts work_item@(CDictCan { cc_ev = fl, cc_class = cls
                                          , cc_tyargs = xis })
  | not (isWanted fl)   -- Never use instances for Given or Derived constraints
  = try_fundeps_and_return

  | Just ev <- lookupSolvedDict inerts dict_loc cls xis   -- Cached
  = do { setWantedEvBind dict_id (ctEvTerm ev);
       ; stopWith fl "Dict/Top (cached)" }

  | otherwise  -- Not cached
   = do { lkup_inst_res <- matchClassInst inerts cls xis dict_loc
         ; case lkup_inst_res of
               GenInst wtvs ev_term -> do { addSolvedDict fl cls xis
                                          ; solve_from_instance wtvs ev_term }
               NoInstance -> try_fundeps_and_return }
   where
     dict_id = ASSERT( isWanted fl ) ctEvId fl
     dict_pred = mkClassPred cls xis
     dict_loc = ctEvLoc fl
     dict_origin = ctLocOrigin dict_loc
     deeper_loc = bumpCtLocDepth CountConstraints dict_loc

     solve_from_instance :: [CtEvidence] -> EvTerm -> TcS (StopOrContinue Ct)
      -- Precondition: evidence term matches the predicate workItem
     solve_from_instance evs ev_term
        | null evs
        = do { traceTcS "doTopReact/found nullary instance for" $
               ppr dict_id
             ; setWantedEvBind dict_id ev_term
             ; stopWith fl "Dict/Top (solved, no new work)" }
        | otherwise
        = do { traceTcS "doTopReact/found non-nullary instance for" $
               ppr dict_id
             ; setWantedEvBind dict_id ev_term
             ; let mk_new_wanted ev
                     = mkNonCanonical (ev {ctev_loc = deeper_loc })
             ; updWorkListTcS (extendWorkListCts (map mk_new_wanted evs))
             ; stopWith fl "Dict/Top (solved, more work)" }

     -- We didn't solve it; so try functional dependencies with
     -- the instance environment, and return
     -- NB: even if there *are* some functional dependencies against the
     -- instance environment, there might be a unique match, and if
     -- so we make sure we get on and solve it first. See Note [Weird fundeps]
     try_fundeps_and_return
       = do { instEnvs <- getInstEnvs
            ; emitFunDepDeriveds $
              improveFromInstEnv instEnvs mk_ct_loc dict_pred
            ; continueWith work_item }

     mk_ct_loc :: PredType   -- From instance decl
               -> SrcSpan    -- also from instance deol
               -> CtLoc
     mk_ct_loc inst_pred inst_loc
       = dict_loc { ctl_origin = FunDepOrigin2 dict_pred dict_origin
                                               inst_pred inst_loc }

doTopReactDict _ w = pprPanic "doTopReactDict" (ppr w)

--------------------
doTopReactFunEq :: Ct -> TcS (StopOrContinue Ct)
-- Note [Short cut for top-level reaction]
doTopReactFunEq work_item@(CFunEqCan { cc_ev = old_ev, cc_fun = fam_tc
                                     , cc_tyargs = args , cc_fsk = fsk })
  = ASSERT(isTypeFamilyTyCon fam_tc) -- No associated data families
                                     -- have reached this far
    ASSERT( not (isDerived old_ev) )   -- CFunEqCan is never Derived
    -- Look up in top-level instances, or built-in axiom
    do { match_res <- matchFam fam_tc args   -- See Note [MATCHING-SYNONYMS]
       ; case match_res of {
           Nothing -> do { try_improvement; continueWith work_item } ;
           Just (ax_co, rhs_ty)

    -- Found a top-level instance

    | Just (tc, tc_args) <- tcSplitTyConApp_maybe rhs_ty
    , isTypeFamilyTyCon tc
    , tc_args `lengthIs` tyConArity tc    -- Short-cut
    -> shortCutReduction old_ev fsk ax_co tc tc_args
         -- Try shortcut; see Note [Short cut for top-level reaction]

    | isGiven old_ev  -- Not shortcut
    -> do { let final_co = mkTcSymCo (ctEvCoercion old_ev) `mkTcTransCo` ax_co
                -- final_co :: fsk ~ rhs_ty
          ; new_ev <- newGivenEvVar deeper_loc (mkTcEqPred (mkTyVarTy fsk) rhs_ty,
                                                EvCoercion final_co)
          ; emitWorkNC [new_ev]   -- Non-cannonical; that will mean we flatten rhs_ty
          ; stopWith old_ev "Fun/Top (given)" }

    | not (fsk `elemVarSet` tyVarsOfType rhs_ty)
    -> do { dischargeFmv (ctEvId old_ev) fsk ax_co rhs_ty
          ; traceTcS "doTopReactFunEq" $
            vcat [ text "old_ev:" <+> ppr old_ev
                 , nest 2 (text ":=") <+> ppr ax_co ]
          ; stopWith old_ev "Fun/Top (wanted)" }

    | otherwise -- We must not assign ufsk := ...ufsk...!
    -> do { alpha_ty <- newFlexiTcSTy (tyVarKind fsk)
          ; new_ev <- newWantedEvVarNC loc (mkTcEqPred alpha_ty rhs_ty)
          ; emitWorkNC [new_ev]
              -- By emitting this as non-canonical, we deal with all
              -- flattening, occurs-check, and ufsk := ufsk issues
          ; let final_co = ax_co `mkTcTransCo` mkTcSymCo (ctEvCoercion new_ev)
              --    ax_co :: fam_tc args ~ rhs_ty
              --   new_ev :: alpha ~ rhs_ty
              --     ufsk := alpha
              -- final_co :: fam_tc args ~ alpha
          ; dischargeFmv (ctEvId old_ev) fsk final_co alpha_ty
          ; traceTcS "doTopReactFunEq (occurs)" $
            vcat [ text "old_ev:" <+> ppr old_ev
                 , nest 2 (text ":=") <+> ppr final_co
                 , text "new_ev:" <+> ppr new_ev ]
          ; stopWith old_ev "Fun/Top (wanted)" } } }
  where
    loc = ctEvLoc old_ev
    deeper_loc = bumpCtLocDepth CountTyFunApps loc

    try_improvement
      | Just ops <- isBuiltInSynFamTyCon_maybe fam_tc
      = do { inert_eqs <- getInertEqs
           ; let eqns = sfInteractTop ops args (lookupFlattenTyVar inert_eqs fsk)
           ; mapM_ (unifyDerived loc Nominal) eqns }
      | otherwise
      = return ()

doTopReactFunEq w = pprPanic "doTopReactFunEq" (ppr w)

shortCutReduction :: CtEvidence -> TcTyVar -> TcCoercion
                  -> TyCon -> [TcType] -> TcS (StopOrContinue Ct)
-- See Note [Top-level reductions for type functions]
shortCutReduction old_ev fsk ax_co fam_tc tc_args
  | isGiven old_ev
  = ASSERT( ctEvEqRel old_ev == NomEq )
    runFlatten $
    do { (xis, cos) <- flattenManyNom old_ev tc_args
               -- ax_co :: F args ~ G tc_args
               -- cos   :: xis ~ tc_args
               -- old_ev :: F args ~ fsk
               -- G cos ; sym ax_co ; old_ev :: G xis ~ fsk

       ; new_ev <- newGivenEvVar deeper_loc
                         ( mkTcEqPred (mkTyConApp fam_tc xis) (mkTyVarTy fsk)
                         , EvCoercion (mkTcTyConAppCo Nominal fam_tc cos
                                        `mkTcTransCo` mkTcSymCo ax_co
                                        `mkTcTransCo` ctEvCoercion old_ev) )

       ; let new_ct = CFunEqCan { cc_ev = new_ev, cc_fun = fam_tc, cc_tyargs = xis, cc_fsk = fsk }
       ; emitFlatWork new_ct
       ; stopWith old_ev "Fun/Top (given, shortcut)" }

  | otherwise
  = ASSERT( not (isDerived old_ev) )   -- Caller ensures this
    ASSERT( ctEvEqRel old_ev == NomEq )
    do { (xis, cos) <- flattenManyNom old_ev tc_args
               -- ax_co :: F args ~ G tc_args
               -- cos   :: xis ~ tc_args
               -- G cos ; sym ax_co ; old_ev :: G xis ~ fsk
               -- new_ev :: G xis ~ fsk
               -- old_ev :: F args ~ fsk := ax_co ; sym (G cos) ; new_ev

       ; new_ev <- newWantedEvVarNC deeper_loc
                                    (mkTcEqPred (mkTyConApp fam_tc xis) (mkTyVarTy fsk))
       ; setWantedEvBind (ctEvId old_ev)
                   (EvCoercion (ax_co `mkTcTransCo` mkTcSymCo (mkTcTyConAppCo Nominal fam_tc cos)
                                      `mkTcTransCo` ctEvCoercion new_ev))

       ; let new_ct = CFunEqCan { cc_ev = new_ev, cc_fun = fam_tc, cc_tyargs = xis, cc_fsk = fsk }
       ; emitFlatWork new_ct
       ; stopWith old_ev "Fun/Top (wanted, shortcut)" }
  where
    loc = ctEvLoc old_ev
    deeper_loc = bumpCtLocDepth CountTyFunApps loc

dischargeFmv :: EvVar -> TcTyVar -> TcCoercion -> TcType -> TcS ()
-- (dischargeFmv x fmv co ty)
--     [W] x :: F tys ~ fuv
--        co :: F tys ~ ty
-- Precondition: fuv is not filled, and fuv `notElem` ty
--
-- Then set fuv := ty,
--      set x := co
--      kick out any inert things that are now rewritable
dischargeFmv evar fmv co xi
  = ASSERT2( not (fmv `elemVarSet` tyVarsOfType xi), ppr evar $$ ppr fmv $$ ppr xi )
    do { setWantedTyBind fmv xi
       ; setWantedEvBind evar (EvCoercion co)
       ; n_kicked <- kickOutRewritable Given NomEq fmv
       ; traceTcS "dischargeFuv" (ppr fmv <+> equals <+> ppr xi $$ ppr_kicked n_kicked) }

{- Note [Top-level reductions for type functions]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
c.f. Note [The flattening story] in TcFlatten

Suppose we have a CFunEqCan  F tys ~ fmv/fsk, and a matching axiom.
Here is what we do, in four cases:

* Wanteds: general firing rule
    (work item) [W]        x : F tys ~ fmv
    instantiate axiom: ax_co : F tys ~ rhs

   Then:
      Discharge   fmv := alpha
      Discharge   x := ax_co ; sym x2
      New wanted  [W] x2 : alpha ~ rhs  (Non-canonical)
   This is *the* way that fmv's get unified; even though they are
   "untouchable".

   NB: it can be the case that fmv appears in the (instantiated) rhs.
   In that case the new Non-canonical wanted will be loopy, but that's
   ok.  But it's good reason NOT to claim that it is canonical!

* Wanteds: short cut firing rule
  Applies when the RHS of the axiom is another type-function application
      (work item)        [W] x : F tys ~ fmv
      instantiate axiom: ax_co : F tys ~ G rhs_tys

  It would be a waste to create yet another fmv for (G rhs_tys).
  Instead (shortCutReduction):
      - Flatten rhs_tys (cos : rhs_tys ~ rhs_xis)
      - Add G rhs_xis ~ fmv to flat cache  (note: the same old fmv)
      - New canonical wanted   [W] x2 : G rhs_xis ~ fmv  (CFunEqCan)
      - Discharge x := ax_co ; G cos ; x2

* Givens: general firing rule
      (work item)        [G] g : F tys ~ fsk
      instantiate axiom: ax_co : F tys ~ rhs

   Now add non-canonical given (since rhs is not flat)
      [G] (sym g ; ax_co) : fsk ~ rhs  (Non-canonical)

* Givens: short cut firing rule
  Applies when the RHS of the axiom is another type-function application
      (work item)        [G] g : F tys ~ fsk
      instantiate axiom: ax_co : F tys ~ G rhs_tys

  It would be a waste to create yet another fsk for (G rhs_tys).
  Instead (shortCutReduction):
     - Flatten rhs_tys: flat_cos : tys ~ flat_tys
     - Add new Canonical given
          [G] (sym (G flat_cos) ; co ; g) : G flat_tys ~ fsk   (CFunEqCan)

Note [Cached solved FunEqs]
~~~~~~~~~~~~~~~~~~~~~~~~~~~
When trying to solve, say (FunExpensive big-type ~ ty), it's important
to see if we have reduced (FunExpensive big-type) before, lest we
simply repeat it.  Hence the lookup in inert_solved_funeqs.  Moreover
we must use `canRewriteOrSame` because both uses might (say) be Wanteds,
and we *still* want to save the re-computation.

Note [MATCHING-SYNONYMS]
~~~~~~~~~~~~~~~~~~~~~~~~
When trying to match a dictionary (D tau) to a top-level instance, or a
type family equation (F taus_1 ~ tau_2) to a top-level family instance,
we do *not* need to expand type synonyms because the matcher will do that for us.


Note [RHS-FAMILY-SYNONYMS]
~~~~~~~~~~~~~~~~~~~~~~~~~~
The RHS of a family instance is represented as yet another constructor which is
like a type synonym for the real RHS the programmer declared. Eg:
    type instance F (a,a) = [a]
Becomes:
    :R32 a = [a]      -- internal type synonym introduced
    F (a,a) ~ :R32 a  -- instance

When we react a family instance with a type family equation in the work list
we keep the synonym-using RHS without expansion.

Note [FunDep and implicit parameter reactions]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Currently, our story of interacting two dictionaries (or a dictionary
and top-level instances) for functional dependencies, and implicit
paramters, is that we simply produce new Derived equalities.  So for example

        class D a b | a -> b where ...
    Inert:
        d1 :g D Int Bool
    WorkItem:
        d2 :w D Int alpha

    We generate the extra work item
        cv :d alpha ~ Bool
    where 'cv' is currently unused.  However, this new item can perhaps be
    spontaneously solved to become given and react with d2,
    discharging it in favour of a new constraint d2' thus:
        d2' :w D Int Bool
        d2 := d2' |> D Int cv
    Now d2' can be discharged from d1

We could be more aggressive and try to *immediately* solve the dictionary
using those extra equalities, but that requires those equalities to carry
evidence and derived do not carry evidence.

If that were the case with the same inert set and work item we might dischard
d2 directly:

        cv :w alpha ~ Bool
        d2 := d1 |> D Int cv

But in general it's a bit painful to figure out the necessary coercion,
so we just take the first approach. Here is a better example. Consider:
    class C a b c | a -> b
And:
     [Given]  d1 : C T Int Char
     [Wanted] d2 : C T beta Int
In this case, it's *not even possible* to solve the wanted immediately.
So we should simply output the functional dependency and add this guy
[but NOT its superclasses] back in the worklist. Even worse:
     [Given] d1 : C T Int beta
     [Wanted] d2: C T beta Int
Then it is solvable, but its very hard to detect this on the spot.

It's exactly the same with implicit parameters, except that the
"aggressive" approach would be much easier to implement.

Note [When improvement happens]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We fire an improvement rule when

  * Two constraints match (modulo the fundep)
      e.g. C t1 t2, C t1 t3    where C a b | a->b
    The two match because the first arg is identical

Note that we *do* fire the improvement if one is Given and one is Derived (e.g. a
superclass of a Wanted goal) or if both are Given.

Example (tcfail138)
    class L a b | a -> b
    class (G a, L a b) => C a b

    instance C a b' => G (Maybe a)
    instance C a b  => C (Maybe a) a
    instance L (Maybe a) a

When solving the superclasses of the (C (Maybe a) a) instance, we get
  Given:  C a b  ... and hance by superclasses, (G a, L a b)
  Wanted: G (Maybe a)
Use the instance decl to get
  Wanted: C a b'
The (C a b') is inert, so we generate its Derived superclasses (L a b'),
and now we need improvement between that derived superclass an the Given (L a b)

Test typecheck/should_fail/FDsFromGivens also shows why it's a good idea to
emit Derived FDs for givens as well.

Note [Weird fundeps]
~~~~~~~~~~~~~~~~~~~~
Consider   class Het a b | a -> b where
              het :: m (f c) -> a -> m b

           class GHet (a :: * -> *) (b :: * -> *) | a -> b
           instance            GHet (K a) (K [a])
           instance Het a b => GHet (K a) (K b)

The two instances don't actually conflict on their fundeps,
although it's pretty strange.  So they are both accepted. Now
try   [W] GHet (K Int) (K Bool)
This triggers fudeps from both instance decls; but it also
matches a *unique* instance decl, and we should go ahead and
pick that one right now.  Otherwise, if we don't, it ends up
unsolved in the inert set and is reported as an error.

Trac #7875 is a case in point.

Note [Overriding implicit parameters]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Consider
   f :: (?x::a) -> Bool -> a

   g v = let ?x::Int = 3
         in (f v, let ?x::Bool = True in f v)

This should probably be well typed, with
   g :: Bool -> (Int, Bool)

So the inner binding for ?x::Bool *overrides* the outer one.
Hence a work-item Given overrides an inert-item Given.
-}

data LookupInstResult
  = NoInstance
  | GenInst [CtEvidence] EvTerm

instance Outputable LookupInstResult where
  ppr NoInstance = text "NoInstance"
  ppr (GenInst ev t) = text "GenInst" <+> ppr ev <+> ppr t


matchClassInst :: InertSet -> Class -> [Type] -> CtLoc -> TcS LookupInstResult

matchClassInst _ clas [ ty ] _
  | className clas == knownNatClassName
  , Just n <- isNumLitTy ty = makeDict (EvNum n)

  | className clas == knownSymbolClassName
  , Just s <- isStrLitTy ty = makeDict (EvStr s)

  where
  {- This adds a coercion that will convert the literal into a dictionary
     of the appropriate type.  See Note [KnownNat & KnownSymbol and EvLit]
     in TcEvidence.  The coercion happens in 2 steps:

     Integer -> SNat n     -- representation of literal to singleton
     SNat n  -> KnownNat n -- singleton to dictionary

     The process is mirrored for Symbols:
     String    -> SSymbol n
     SSymbol n -> KnownSymbol n
  -}
  makeDict evLit
    | Just (_, co_dict) <- tcInstNewTyCon_maybe (classTyCon clas) [ty]
          -- co_dict :: KnownNat n ~ SNat n
    , [ meth ]   <- classMethods clas
    , Just tcRep <- tyConAppTyCon_maybe -- SNat
                      $ funResultTy         -- SNat n
                      $ dropForAlls         -- KnownNat n => SNat n
                      $ idType meth         -- forall n. KnownNat n => SNat n
    , Just (_, co_rep) <- tcInstNewTyCon_maybe tcRep [ty]
          -- SNat n ~ Integer
    = return (GenInst [] $ mkEvCast (EvLit evLit) (mkTcSymCo (mkTcTransCo co_dict co_rep)))

    | otherwise
    = panicTcS (text "Unexpected evidence for" <+> ppr (className clas)
                     $$ vcat (map (ppr . idType) (classMethods clas)))

matchClassInst _ clas [k,t] loc
  | className clas == typeableClassName = matchTypeableClass clas k t loc

matchClassInst inerts clas tys loc
   = do { dflags <- getDynFlags
        ; tclvl <- getTcLevel
        ; traceTcS "matchClassInst" $ vcat [ text "pred =" <+> ppr pred
                                           , text "inerts=" <+> ppr inerts
                                           , text "untouchables=" <+> ppr tclvl ]
        ; instEnvs <- getInstEnvs
        ; case lookupInstEnv instEnvs clas tys of
            ([], _, _)               -- Nothing matches
                -> do { traceTcS "matchClass not matching" $
                        vcat [ text "dict" <+> ppr pred ]
                      ; return NoInstance }

            ([(ispec, inst_tys)], [], _) -- A single match
                | not (xopt Opt_IncoherentInstances dflags)
                , given_overlap tclvl
                -> -- See Note [Instance and Given overlap]
                   do { traceTcS "Delaying instance application" $
                          vcat [ text "Workitem=" <+> pprType (mkClassPred clas tys)
                               , text "Relevant given dictionaries=" <+> ppr givens_for_this_clas ]
                      ; return NoInstance  }

                | otherwise
                -> do   { let dfun_id = instanceDFunId ispec
                        ; traceTcS "matchClass success" $
                          vcat [text "dict" <+> ppr pred,
                                text "witness" <+> ppr dfun_id
                                               <+> ppr (idType dfun_id) ]
                                  -- Record that this dfun is needed
                        ; match_one dfun_id inst_tys }

            (matches, _, _)    -- More than one matches
                               -- Defer any reactions of a multitude
                               -- until we learn more about the reagent
                -> do   { traceTcS "matchClass multiple matches, deferring choice" $
                          vcat [text "dict" <+> ppr pred,
                                text "matches" <+> ppr matches]
                        ; return NoInstance } }
   where
     pred = mkClassPred clas tys

     match_one :: DFunId -> [DFunInstType] -> TcS LookupInstResult
                  -- See Note [DFunInstType: instantiating types] in InstEnv
     match_one dfun_id mb_inst_tys
       = do { checkWellStagedDFun pred dfun_id loc
            ; (tys, theta) <- instDFunType dfun_id mb_inst_tys
            ; evc_vars <- mapM (newWantedEvVar loc) theta
            ; let new_ev_vars = freshGoals evc_vars
                      -- new_ev_vars are only the real new variables that can be emitted
                  dfun_app = EvDFunApp dfun_id tys (map (ctEvTerm . fst) evc_vars)
            ; return $ GenInst new_ev_vars dfun_app }

     givens_for_this_clas :: Cts
     givens_for_this_clas
         = filterBag isGivenCt (findDictsByClass (inert_dicts $ inert_cans inerts) clas)

     given_overlap :: TcLevel -> Bool
     given_overlap tclvl = anyBag (matchable tclvl) givens_for_this_clas

     matchable tclvl (CDictCan { cc_class = clas_g, cc_tyargs = sys
                               , cc_ev = fl })
       | isGiven fl
       = ASSERT( clas_g == clas )
         case tcUnifyTys (\tv -> if isTouchableMetaTyVar tclvl tv &&
                                    tv `elemVarSet` tyVarsOfTypes tys
                                 then BindMe else Skolem) tys sys of
       -- We can't learn anything more about any variable at this point, so the only
       -- cause of overlap can be by an instantiation of a touchable unification
       -- variable. Hence we only bind touchable unification variables. In addition,
       -- we use tcUnifyTys instead of tcMatchTys to rule out cyclic substitutions.
            Nothing -> False
            Just _  -> True
       | otherwise = False -- No overlap with a solved, already been taken care of
                           -- by the overlap check with the instance environment.
     matchable _tys ct = pprPanic "Expecting dictionary!" (ppr ct)

{-
Note [Instance and Given overlap]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Example, from the OutsideIn(X) paper:
       instance P x => Q [x]
       instance (x ~ y) => R y [x]

       wob :: forall a b. (Q [b], R b a) => a -> Int

       g :: forall a. Q [a] => [a] -> Int
       g x = wob x

This will generate the impliation constraint:
            Q [a] => (Q [beta], R beta [a])
If we react (Q [beta]) with its top-level axiom, we end up with a
(P beta), which we have no way of discharging. On the other hand,
if we react R beta [a] with the top-level we get  (beta ~ a), which
is solvable and can help us rewrite (Q [beta]) to (Q [a]) which is
now solvable by the given Q [a].

The solution is that:
  In matchClassInst (and thus in topReact), we return a matching
  instance only when there is no Given in the inerts which is
  unifiable to this particular dictionary.

The end effect is that, much as we do for overlapping instances, we delay choosing a
class instance if there is a possibility of another instance OR a given to match our
constraint later on. This fixes bugs #4981 and #5002.

This is arguably not easy to appear in practice due to our aggressive prioritization
of equality solving over other constraints, but it is possible. I've added a test case
in typecheck/should-compile/GivenOverlapping.hs

We ignore the overlap problem if -XIncoherentInstances is in force: see
Trac #6002 for a worked-out example where this makes a difference.

Moreover notice that our goals here are different than the goals of the top-level
overlapping checks. There we are interested in validating the following principle:

    If we inline a function f at a site where the same global instance environment
    is available as the instance environment at the definition site of f then we
    should get the same behaviour.

But for the Given Overlap check our goal is just related to completeness of
constraint solving.
-}

-- | Is the constraint for an implicit CallStack parameter?
isCallStackIP :: CtLoc -> Class -> Type -> Maybe (EvTerm -> EvCallStack)
isCallStackIP loc cls ty
  | Just (tc, []) <- splitTyConApp_maybe ty
  , cls `hasKey` ipClassNameKey && tc `hasKey` callStackTyConKey
  = occOrigin (ctLocOrigin loc)
  where
  -- We only want to grab constraints that arose due to the use of an IP or a
  -- function call. See Note [Overview of implicit CallStacks]
  occOrigin (OccurrenceOf n)
    = Just (EvCsPushCall n locSpan)
  occOrigin (IPOccOrigin n)
    = Just (EvCsTop ('?' `consFS` hsIPNameFS n) locSpan)
  occOrigin _
    = Nothing
  locSpan
    = ctLocSpan loc
isCallStackIP _ _ _
  = Nothing



-- | Assumes that we've checked that this is the 'Typeable' class,
-- and it was applied to the correc arugment.
matchTypeableClass :: Class -> Kind -> Type -> CtLoc -> TcS LookupInstResult
matchTypeableClass clas k t loc
  | isForAllTy k                               = return NoInstance
  | Just (tc, ks) <- splitTyConApp_maybe t
  , all isKind ks                              = doTyCon tc ks
  | Just (f,kt)       <- splitAppTy_maybe t    = doTyApp f kt
  | Just _            <- isNumLitTy t          = mkSimpEv (EvTypeableTyLit t)
  | Just _            <- isStrLitTy t          = mkSimpEv (EvTypeableTyLit t)
  | otherwise                                  = return NoInstance

  where
  -- Representation for type constructor applied to some kinds
  doTyCon tc ks =
    case mapM kindRep ks of
      Nothing    -> return NoInstance
      Just kReps -> mkSimpEv (EvTypeableTyCon tc kReps)

  {- Representation for an application of a type to a type-or-kind.
  This may happen when the type expression starts with a type variable.
  Example (ignoring kind parameter):
    Typeable (f Int Char)                      -->
    (Typeable (f Int), Typeable Char)          -->
    (Typeable f, Typeable Int, Typeable Char)  --> (after some simp. steps)
    Typeable f
  -}
  doTyApp f tk
    | isKind tk = return NoInstance -- We can't solve until we know the ctr.
    | otherwise =
      do ct1 <- subGoal f
         ct2 <- subGoal tk
         let realSubs = [ c | (c,Fresh) <- [ct1,ct2] ]
         return $ GenInst realSubs
                $ EvTypeable $ EvTypeableTyApp (getEv ct1,f) (getEv ct2,tk)


  -- Representation for concrete kinds.  We just use the kind itself,
  -- but first check to make sure that it is "simple" (i.e., made entirely
  -- out of kind constructors).
  kindRep ki = do (_,ks) <- splitTyConApp_maybe ki
                  mapM_ kindRep ks
                  return ki

  getEv (ct,_fresh) = ctEvTerm ct

  -- Emit a `Typeable` constraint for the given type.
  subGoal ty = do let goal = mkClassPred clas [ typeKind ty, ty ]
                  newWantedEvVar loc goal

  mkSimpEv ev = return (GenInst [] (EvTypeable ev))

