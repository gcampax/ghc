{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Compact.Serialized
-- Copyright   :  (c) The University of Glasgow 2001-2009
--                (c) Giovanni Campagna <gcampagn@cs.stanford.edu> 2015
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  libraries@haskell.org
-- Stability   :  unstable
-- Portability :  non-portable (GHC Extensions)
--
-- This module provides a data structure, called a Compact, for
-- holding fully evaluated data in a consecutive block of memory.
--
-- This module contains support for serializing a Compact for network
-- transmission and on-disk storage.
--
-- /Since: 1.0.0/

module Data.Compact.Serialized(
  SerializedCompact(..),
  withSerializedCompact,
  importCompact,
  importCompactByteStrings,
) where

-- Write down all GHC.Prim deps explicitly to keep them at minimum
import GHC.Prim (Compact#,
                 compactGetFirstBlock#,
                 compactGetNextBlock#,
                 compactAllocateBlockAt#,
                 compactFixupPointers#,
                 touch#,
                 Addr#,
                 nullAddr#,
                 eqAddr#,
                 addrToAny#,
                 anyToAddr#,
                 State#,
                 RealWorld,
                 Word#,
                 )

-- We need to import Word from GHC.Types to see the representation
-- and to able to access the Word# to pass down the primops
import GHC.Types (IO(..), Word(..), isTrue#)
import GHC.Word (Word8)

import GHC.Ptr (Ptr(..), plusPtr)

import qualified Data.ByteString as ByteString
import Data.ByteString.Internal(toForeignPtr)
import Data.IORef(newIORef, readIORef, writeIORef)
import Foreign.ForeignPtr(withForeignPtr)
import Foreign.Marshal.Utils(copyBytes)
import Control.DeepSeq(NFData, force)

import Data.Compact.Internal(Compact(..))

-- |A serialized version of the 'Compact' metadata (each block with
-- address and size and the address of the root). This structure is
-- meant to be sent alongside the actual 'Compact' data. It can be
-- sent out of band in advance if the data is to be sent over RDMA
-- (which requires both sender and receiver to have pinned buffers).
data SerializedCompact a = SerializedCompact {
  serializedCompactBlockList :: [(Ptr a, Word)],
  serializedCompactRoot :: Ptr a
  }

addrIsNull :: Addr# -> Bool
addrIsNull addr = isTrue# (nullAddr# `eqAddr#` addr)


compactGetFirstBlock :: Compact# -> IO (Ptr a, Word)
compactGetFirstBlock buffer =
  IO (\s -> case compactGetFirstBlock# buffer s of
         (# s', addr, size #) -> (# s', (Ptr addr, W# size) #) )

compactGetNextBlock :: Compact# -> Addr# -> IO (Ptr a, Word)
compactGetNextBlock buffer block =
  IO (\s -> case compactGetNextBlock# buffer block s of
         (# s', addr, size #) -> (# s', (Ptr addr, W# size) #) )

mkBlockList :: Compact# -> IO [(Ptr a, Word)]
mkBlockList buffer = compactGetFirstBlock buffer >>= go
  where
    go :: (Ptr a, Word) -> IO [(Ptr a, Word)]
    go (Ptr block, _) | addrIsNull block = return []
    go item@(Ptr block, _) = do
      next <- compactGetNextBlock buffer block
      rest <- go next
      return $ item : rest

-- We MUST mark withSerializedCompact as NOINLINE
-- Otherwise the compiler will eliminate the call to touch#
-- causing the Compact# to be potentially GCed too eagerly,
-- before func had a chance to copy everything into its own
-- buffers/sockets/whatever

-- |Serialize the 'Compact', and call the provided function with
-- with the 'Compact' serialized representation. The resulting
-- action will be executed synchronously before this function
-- completes.
{-# NOINLINE withSerializedCompact #-}
withSerializedCompact :: NFData c => Compact a ->
                         (SerializedCompact a -> IO c) -> IO c
withSerializedCompact (Compact buffer root) func = do
  let rootPtr = case anyToAddr# root of
        (# rootAddr #) -> Ptr rootAddr
  blockList <- mkBlockList buffer
  let serialized = SerializedCompact blockList rootPtr
  -- we must be strict, to avoid smart uses of ByteStrict.Lazy that
  -- return a thunk instead of a ByteString (but the thunk references
  -- the Ptr, not the Compact#, so it will point to garbage if GC
  -- happens)
  !r <- fmap force $ func serialized
  IO (\s -> case touch# buffer s of
         s' -> (# s', r #) )

fixupPointers :: Addr# -> Addr# -> State# RealWorld ->
                 (# State# RealWorld, Maybe (Compact a) #)
fixupPointers firstBlock rootAddr s =
  case compactFixupPointers# firstBlock rootAddr s of
    (# s', buffer, adjustedRoot #) ->
      if addrIsNull adjustedRoot then (# s', Nothing #)
      else case addrToAny# adjustedRoot of
        (# root #) -> (# s', Just $ Compact buffer root #)

-- |Deserialize a 'SerializedCompact' into a in-memory 'Compact'. The
-- provided function will be called with the address and size of each
-- newly allocated block in succession, and should fill the memory
-- from the external source (eg. by reading from a socket or from disk)
-- 'importCompact' can return Nothing if the 'Compact' was corrupt
-- or it had pointers that could not be adjusted.
importCompact :: SerializedCompact a -> (Ptr b -> Word -> IO ()) ->
                 IO (Maybe (Compact a))

-- what we would like is
{-
 importCompactPtrs ((firstAddr, firstSize):rest) = do
   (firstBlock, compact) <- compactAllocateAt firstAddr firstSize
 #nullAddr
   fillBlock firstBlock firstAddr firstSize
   let go prev [] = return ()
       go prev ((addr, size):rest) = do
         (block, _) <- compactAllocateAt addr size prev
         fillBlock block addr size
         go block rest
   go firstBlock rest
   if isTrue# (compactFixupPointers compact) then
     return $ Just compact
     else
     return Nothing

But we can't do that because IO Addr# is not valid (kind mismatch)
This check exists to prevent a polymorphic data constructor from using
an unlifted type (which would break GC) - it would not a problem for IO
because IO stores a function, not a value, but the kind check is there
anyway.
Note that by the reasoning, we cannot do IO (# Addr#, Word# #), nor
we can do IO (Addr#, Word#) (that would break the GC for real!)

And therefore we need to do everything with State# explicitly.
-}

-- just do shut up GHC
importCompact (SerializedCompact [] _) _ = return Nothing
importCompact (SerializedCompact blocks root) filler = do
  -- I'm not sure why we need a bang pattern here, given that
  -- these are obviously strict lets, but ghc complains otherwise
  let !((Ptr firstAddr, W# firstSize):otherBlocks) = blocks
  let !(Ptr rootAddr) = root
  IO (\s0 -> case compactAllocateBlockAt# firstAddr firstSize nullAddr# s0 of
         (# s1, firstBlock #) ->
           case fillBlock firstBlock firstSize s1 of
             s2 -> case go firstBlock otherBlocks s2 of
               s3-> fixupPointers firstBlock rootAddr s3 )
  where
    -- note that the case statements above are strict even though
    -- they don't seem to inspect their argument because State#
    -- is an unlifted type
    fillBlock :: Addr# -> Word# -> State# RealWorld -> State# RealWorld
    fillBlock addr size s = case filler (Ptr addr) (W# size) of
      IO action -> case action s of
        (# s', _ #) -> s'

    go :: Addr# -> [(Ptr a, Word)] -> State# RealWorld -> State# RealWorld
    go _ [] s = s
    go previous ((Ptr addr, W# size):rest) s =
      case compactAllocateBlockAt# addr size previous s of
        (# s', block #) -> case fillBlock block size s' of
          s'' -> go block rest s''

sanityCheckByteStrings :: SerializedCompact a -> [ByteString.ByteString] -> Bool
sanityCheckByteStrings (SerializedCompact scl _) bsl = go scl bsl
  where
    go [] [] = True
    go (_:_) [] = False
    go [] (_:_) = False
    go ((_, size):scs) (bs:bss) =
      fromIntegral size == ByteString.length bs && go scs bss

importCompactByteStrings :: SerializedCompact a -> [ByteString.ByteString] ->
                            IO (Maybe (Compact a))
importCompactByteStrings serialized stringList =
  -- sanity check stringList first - if we throw an exception later we leak
  -- memory!
  if not (sanityCheckByteStrings serialized stringList) then
    return Nothing
  else do
    state <- newIORef stringList
    let filler :: Ptr Word8 -> Word -> IO ()
        filler to size = do
          -- this pattern match will never fail
          (next:rest) <- readIORef state
          let (fp, off, _) = toForeignPtr next
          withForeignPtr fp $ \from -> do
            copyBytes to (from `plusPtr` off) (fromIntegral size)
          writeIORef state rest
    importCompact serialized filler
