/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team 1998-2008
 *
 * The block allocator and free list manager.
 *
 * This is the architecture independent part of the block allocator.
 * It requires only the following support from the operating system:
 *
 *    void *getMBlock(nat n);
 *
 * returns the address of an n*MBLOCK_SIZE region of memory, aligned on
 * an MBLOCK_SIZE boundary.  There are no other restrictions on the
 * addresses of memory returned by getMBlock().
 *
 * ---------------------------------------------------------------------------*/

#include "PosixSource.h"
#include "Rts.h"

#include "Storage.h"
#include "RtsUtils.h"
#include "BlockAlloc.h"
#include "OSMem.h"

#include <string.h>

static void  initMBlock(void *mblock);

/* -----------------------------------------------------------------------------

  Implementation notes
  ~~~~~~~~~~~~~~~~~~~~

  Terminology:
    - bdescr = block descriptor
    - bgroup = block group (1 or more adjacent blocks)
    - mblock = mega block
    - mgroup = mega group (1 or more adjacent mblocks)

   Invariants on block descriptors
   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
   bd->start always points to the start of the block.

   bd->free is either:
      - zero for a non-group-head; bd->link points to the head
      - (-1) for the head of a free block group
      - or it points within the block (group)

   bd->blocks is either:
      - zero for a non-group-head; bd->link points to the head
      - number of blocks in this group otherwise

   bd->link either points to a block descriptor or is NULL

   The following fields are not used by the allocator:
     bd->flags
     bd->gen_no
     bd->gen
     bd->dest

  Exceptions: we don't maintain invariants for all the blocks within a
  group on the free list, because it is expensive to modify every
  bdescr in a group when coalescing.  Just the head and last bdescrs
  will be correct for a group on the free list.


  Free lists
  ~~~~~~~~~~

  Preliminaries:
    - most allocations are for a small number of blocks
    - sometimes the OS gives us new memory backwards in the address
      space, sometimes forwards, so we should not be biased towards
      any particular layout in the address space
    - We want to avoid fragmentation
    - We want allocation and freeing to be O(1) or close.

  Coalescing trick: when a bgroup is freed (freeGroup()), we can check
  whether it can be coalesced with other free bgroups by checking the
  bdescrs for the blocks on either side of it.  This means that we can
  coalesce in O(1) time.  Every free bgroup must have its head and tail
  bdescrs initialised, the rest don't matter.

  We keep the free list in buckets, using a heap-sort strategy.
  Bucket N contains blocks with sizes 2^N - 2^(N+1)-1.  The list of
  blocks in each bucket is doubly-linked, so that if a block is
  coalesced we can easily remove it from its current free list.

  To allocate a new block of size S, grab a block from bucket
  log2ceiling(S) (i.e. log2() rounded up), in which all blocks are at
  least as big as S, and split it if necessary.  If there are no
  blocks in that bucket, look at bigger buckets until a block is found
  Allocation is therefore O(logN) time.

  To free a block:
    - coalesce it with neighbours.
    - remove coalesced neighbour(s) from free list(s)
    - add the new (coalesced) block to the front of the appropriate
      bucket, given by log2(S) where S is the size of the block.

  Free is O(1).

  Megablocks
  ~~~~~~~~~~

  Separately from the free list of block groups, which are smaller than
  an mblock, we maintain a free list of mblock groups.  This is the unit
  of memory the operating system gives us, and we may either split mblocks
  into blocks or allocate them directly (when very large contiguous regions
  of memory).  mblocks have a different set of invariants than blocks:

  bd->start points to the start of the block IF the block is in the first mblock
  bd->blocks and bd->link are only valid IF this block is the first block
    of the first mblock
  No other fields are used (in particular, free is not used, meaning that
    space that is not used by the (single) object is wasted.

  This has implications for the free list as well:
  We cannot play the coalescing trick with mblocks, because there is
  no requirement that the bdescrs in the second and subsequent mblock
  of an mgroup are initialised (the mgroup might be filled with a
  large array, overwriting the bdescrs for example).

  The separate free list for megablocks is thus sorted in *address*
  order, so that we can coalesce.  Allocation in this list is best-fit
  by traversing the whole list: we don't expect this list to be long,
  and allocation/freeing of large blocks is rare; avoiding
  fragmentation is more important than performance here.

  freeGroup() might end up moving a block from free_list to
  free_mblock_list, if after coalescing we end up with a full mblock.

  checkFreeListSanity() checks all the invariants on the free lists.

  Megablock bitmap
  ~~~~~~~~~~~~~~~~

  In addition to the previous code, we have a bitmap for each chunk
  != 0, which is 1 if the megablock is a normally allocated megablock
  (ie, one where the block descriptors are readable and valid), and 0
  otherwise. We only keep the bitmap for the chunks we use, to avoid
  using excessive memory, and we never create the bitmap for chunk 0
  (which is private), which means that there is no memory overhead if
  the striped allocator is disabled.
  The bitmap is used for allocGroupAt(), to verify if it can read the
  block descriptor and check if a block is allocated.

  --------------------------------------------------------------------------- */

/* ---------------------------------------------------------------------------
   WATCH OUT FOR OVERFLOW

   Be very careful with integer overflow here.  If you have an
   expression like (n_blocks * BLOCK_SIZE), and n_blocks is an int or
   a nat, then it will very likely overflow on a 64-bit platform.
   Always cast to StgWord (or W_ for short) first: ((W_)n_blocks * BLOCK_SIZE).

  --------------------------------------------------------------------------- */

#define MAX_FREE_LIST 9

// In THREADED_RTS mode, the free list is protected by sm_mutex.

#ifndef USE_STRIPED_ALLOCATOR
#define MBLOCK_NUM_CHUNKS 0
#endif

static bdescr *free_lists[MBLOCK_NUM_CHUNKS + 1][MAX_FREE_LIST];
static bdescr *free_mblock_lists[MBLOCK_NUM_CHUNKS + 1];

enum {
    MBLOCK_INVALID, // not read/writable - has to be 0
    MBLOCK_FREE,    // alloced but in the free_mblock_lists
    MBLOCK_ALLOCED, // alloced and in use as head of a mblock group
    MBLOCK_ALLOCED_TAIL // alloced and in use as tail of a mblock group
};

#ifdef USE_STRIPED_ALLOCATOR
#define MBLOCK_BITMAP_SIZE (MBLOCK_CHUNK_SIZE / MBLOCK_SIZE / 8 * 2) // 32 KB
// If the mblock is read/writable
static StgWord8 *mblock_bitmaps[MBLOCK_NUM_CHUNKS + 1];

STATIC_INLINE StgWord
mblock_bitmap_get_bit (void *addr, nat chunk)
{
    StgWord mblock_counter;

    mblock_counter = ((W_)addr - (MBLOCK_SPACE_BEGIN + MBLOCK_NORMAL_SPACE_SIZE +
                                  (chunk-1) * MBLOCK_CHUNK_SIZE));
    mblock_counter /= MBLOCK_SIZE;

    return 2 * mblock_counter;
}

STATIC_INLINE StgWord
mblock_bitmap_get (void *addr, nat i)
{
    nat chunk;
    W_ bit;

    chunk = mblock_address_get_chunk (addr);
    ASSERT (chunk != 0);

    if (mblock_bitmaps[chunk] == NULL)
        return MBLOCK_INVALID;

    bit = mblock_bitmap_get_bit (addr, chunk);
    bit += 2 * i;

    return ((mblock_bitmaps[chunk][bit / 8] >>
             (bit % 8))) & 0x3;
}

static rtsBool
mblock_bitmap_test_any_valid (void *addr, nat n)
{
    nat i;

    for (i = 0; i < n; i++) {
        if (mblock_bitmap_get(addr, i) != MBLOCK_INVALID)
            return rtsTrue;
    }
    return rtsFalse;
}

static rtsBool
mblock_bitmap_test_any_alloced (void *addr, nat n)
{
    nat i;

    for (i = 0; i < n; i++) {
        if (mblock_bitmap_get(addr, i) >= MBLOCK_ALLOCED)
            return rtsTrue;
    }
    return rtsFalse;
}

static nat
mblock_bitmap_find_first_valid (void *addr, nat n)
{
    nat i;

    for (i = 0; i < n; i++) {
        if (mblock_bitmap_get(addr, i) > MBLOCK_INVALID)
            return i;
    }
    return -1;
}

static void
mblock_bitmap_mark (void *addr, nat n, StgWord val)
{
    W_ base, bit;
    nat chunk;
    nat i;

    chunk = mblock_address_get_chunk (addr);
    if (chunk == 0)
        return;

    if (mblock_bitmaps[chunk] == NULL) {
        mblock_bitmaps[chunk] = stgCallocBytes(MBLOCK_BITMAP_SIZE, 1,
                                        "mblock_bitmap_mark");
    }

    val = val & 0x3;
    base = mblock_bitmap_get_bit (addr, chunk);
    for (i = 0; i < n; i++) {
        bit = base + 2 * i;

        mblock_bitmaps[chunk][bit / 8] &= ~(0x3 << (bit % 8));
        mblock_bitmaps[chunk][bit / 8] |= val << (bit % 8);
    }
}
#else // USE_STRIPED_ALLOCATOR
STATIC_INLINE void
mblock_bitmap_mark(void* addr, nat n, StgWord val)
{
    (void)addr;
    (void)n;
    (void)val;
}
#endif

// free_list[i] contains blocks that are at least size 2^i, and at
// most size 2^(i+1) - 1.
//
// To find the free list in which to place a block, use log_2(size).
// To find a free block of the right size, use log_2_ceil(size).

W_ n_alloc_blocks;   // currently allocated blocks
W_ hw_alloc_blocks;  // high-water allocated blocks

/* -----------------------------------------------------------------------------
   Initialisation
   -------------------------------------------------------------------------- */

void initBlockAllocator(void)
{
    nat i, j;

    for (j=0; j <= MBLOCK_NUM_CHUNKS; j++) {
        for (i=0; i < MAX_FREE_LIST; i++) {
            free_lists[j][i] = NULL;
        }
        free_mblock_lists[j] = NULL;
    }
    n_alloc_blocks = 0;
    hw_alloc_blocks = 0;
}

/* -----------------------------------------------------------------------------
   Allocation
   -------------------------------------------------------------------------- */

STATIC_INLINE void
initGroup(bdescr *head)
{
  // If this block group fits in a single megablock, initialize
  // all of the block descriptors.  Otherwise, initialize *only*
  // the first block descriptor, since for large allocations we don't
  // need to give the invariant that Bdescr(p) is valid for any p in the
  // block group. (This is because it is impossible to do, as the
  // block descriptor table for the second mblock will get overwritten
  // by contiguous user data.)
  //
  // The above is true unless we're in a chunk != 0, because then
  // the invariant is that all block descriptors for the first megablock
  // are allocate - otherwise allocGroupAt() will not work

  head->free   = head->start;
  head->link   = NULL;

#ifdef USE_STRIPED_ALLOCATOR
  {
      bdescr *bd;
      nat chunk;
      W_ i, n;

      chunk = mblock_address_get_chunk(head);
      n = head->blocks > BLOCKS_PER_MBLOCK ?
          (chunk == 0 ? 1 : BLOCKS_PER_MBLOCK) : head->blocks;

      for (i=1, bd = head+1; i < n; i++, bd++) {
          bd->free = 0;
          bd->blocks = 0;
          bd->link = head;
      }
  }
#else

  // If this is a block group (but not a megablock group), we
  // make the last block of the group point to the head.  This is used
  // when coalescing blocks in freeGroup().  We don't do this for
  // megablock groups because blocks in the second and subsequent
  // mblocks don't have bdescrs; freeing these is handled in a
  // different way by free_mblock_group().
  if (head->blocks > 1 && head->blocks <= BLOCKS_PER_MBLOCK) {
      bdescr *last = head + head->blocks-1;
      last->blocks = 0;
      last->link = head;
  }
#endif
}

// There are quicker non-loopy ways to do log_2, but we expect n to be
// usually small, and MAX_FREE_LIST is also small, so the loop version
// might well be the best choice here.
STATIC_INLINE nat
log_2_ceil(W_ n)
{
    W_ i, x;
    x = 1;
    for (i=0; i < MAX_FREE_LIST; i++) {
        if (x >= n) return i;
        x = x << 1;
    }
    return MAX_FREE_LIST;
}

STATIC_INLINE nat
log_2(W_ n)
{
    W_ i, x;
    x = n;
    for (i=0; i < MAX_FREE_LIST; i++) {
        x = x >> 1;
        if (x == 0) return i;
    }
    return MAX_FREE_LIST;
}

STATIC_INLINE void
free_list_insert (nat chunk, bdescr *bd)
{
    nat ln;

    ASSERT(bd->blocks < BLOCKS_PER_MBLOCK);
    ln = log_2(bd->blocks);

    dbl_link_onto(bd, &free_lists[chunk][ln]);
}


STATIC_INLINE bdescr *
tail_of (bdescr *bd)
{
    return bd + bd->blocks - 1;
}

// After splitting a group, the last block of each group must have a
// tail that points to the head block, to keep our invariants for
// coalescing.
STATIC_INLINE void
setup_tail (bdescr *bd)
{
    bdescr *tail;
    tail = tail_of(bd);
    if (tail != bd) {
        tail->blocks = 0;
        tail->free = 0;
        tail->link = bd;
    }
}


// Take a free block group bd, and split off a group of size n from
// it.  Adjust the free list as necessary, and return the new group.
static bdescr *
split_free_block (bdescr *bd, W_ n, nat chunk, nat ln)
{
    bdescr *fg; // free group

    ASSERT(bd->blocks > n);
    dbl_link_remove(bd, &free_lists[chunk][ln]);
    fg = bd + bd->blocks - n; // take n blocks off the end
    fg->blocks = n;
    bd->blocks -= n;
    setup_tail(bd);
    ln = log_2(bd->blocks);
    dbl_link_onto(bd, &free_lists[chunk][ln]);
    return fg;
}

/* Only initializes the start pointers on the first megablock and the
 * blocks field of the first bdescr; callers are responsible for calling
 * initGroup afterwards.
 */
static bdescr *
alloc_mega_group (nat chunk, StgWord mblocks)
{
    bdescr *best, *bd, *prev;
    StgWord n;
    void *mblock;

    n = MBLOCK_GROUP_BLOCKS(mblocks);

    best = NULL;
    prev = NULL;
    for (bd = free_mblock_lists[chunk]; bd != NULL; prev = bd, bd = bd->link)
    {
        if (bd->blocks == n)
        {
            if (prev) {
                prev->link = bd->link;
            } else {
                free_mblock_lists[chunk] = bd->link;
            }
            return bd;
        }
        else if (bd->blocks > n)
        {
            if (!best || bd->blocks < best->blocks)
            {
                best = bd;
            }
        }
    }

    if (best)
    {
        // we take our chunk off the end here.
        StgWord best_mblocks  = BLOCKS_TO_MBLOCKS(best->blocks);
        bd = FIRST_BDESCR((StgWord8*)MBLOCK_ROUND_DOWN(best) +
                          (best_mblocks-mblocks)*MBLOCK_SIZE);

        best->blocks = MBLOCK_GROUP_BLOCKS(best_mblocks - mblocks);
        mblock = MBLOCK_ROUND_DOWN(bd);
        initMBlock(mblock);
    }
    else
    {
#ifdef USE_STRIPED_ALLOCATOR
        mblock = getMBlocksInChunk(chunk, mblocks);
#else
        ASSERT (chunk == 0);
        mblock = getMBlocks(mblocks);
#endif
        initMBlock(mblock);             // only need to init the 1st one
        bd = FIRST_BDESCR(mblock);
    }
    bd->blocks = MBLOCK_GROUP_BLOCKS(mblocks);
    mblock_bitmap_mark(mblock, 1, MBLOCK_ALLOCED);
    mblock_bitmap_mark((void*)((W_)mblock + MBLOCK_SIZE),
                       mblocks - 1, MBLOCK_ALLOCED_TAIL);
    return bd;
}

bdescr *
allocGroupInChunk (nat chunk, W_ n)
{
    bdescr *bd, *rem;
    StgWord ln;

    if (n == 0) barf("allocGroup: requested zero blocks");

    if (n >= BLOCKS_PER_MBLOCK)
    {
        StgWord mblocks;

        mblocks = BLOCKS_TO_MBLOCKS(n);

        n_alloc_blocks += mblocks * BLOCKS_PER_MBLOCK;
        if (n_alloc_blocks > hw_alloc_blocks) hw_alloc_blocks = n_alloc_blocks;

        bd = alloc_mega_group(chunk, mblocks);
        // only the bdescrs of the first MB are required to be initialised
        initGroup(bd);
        goto finish;
    }

    n_alloc_blocks += n;
    if (n_alloc_blocks > hw_alloc_blocks) hw_alloc_blocks = n_alloc_blocks;

    ln = log_2_ceil(n);

    while (ln < MAX_FREE_LIST && free_lists[chunk][ln] == NULL) {
        ln++;
    }

    if (ln == MAX_FREE_LIST) {
#if 0  /* useful for debugging fragmentation */
        if ((W_)mblocks_allocated * BLOCKS_PER_MBLOCK * BLOCK_SIZE_W
             - (W_)((n_alloc_blocks - n) * BLOCK_SIZE_W) > (2*1024*1024)/sizeof(W_)) {
            debugBelch("Fragmentation, wanted %d blocks, %ld MB free\n", n, ((mblocks_allocated * BLOCKS_PER_MBLOCK) - n_alloc_blocks) / BLOCKS_PER_MBLOCK);
            RtsFlags.DebugFlags.block_alloc = 1;
            checkFreeListSanity();
        }
#endif

        bd = alloc_mega_group(chunk, 1);
        bd->blocks = n;
        initGroup(bd);                   // we know the group will fit
        rem = bd + n;
        rem->blocks = BLOCKS_PER_MBLOCK-n;
        initGroup(rem); // init the slop
        n_alloc_blocks += rem->blocks;
        freeGroup(rem);                  // add the slop on to the free list
        goto finish;
    }

    bd = free_lists[chunk][ln];

    if (bd->blocks == n)                // exactly the right size!
    {
        dbl_link_remove(bd, &free_lists[chunk][ln]);
        initGroup(bd);
    }
    else if (bd->blocks >  n)            // block too big...
    {
        bd = split_free_block(bd, n, chunk, ln);
        ASSERT(bd->blocks == n);
        initGroup(bd);
    }
    else
    {
        barf("allocGroup: free list corrupted");
    }

finish:
    IF_DEBUG(sanity, memset(bd->start, 0xaa, bd->blocks * BLOCK_SIZE));
    IF_DEBUG(sanity, checkFreeListSanity());
    return bd;
}

bdescr *
allocGroup (W_ n)
{
    return allocGroupInChunk(0, n);
}

#ifdef USE_STRIPED_ALLOCATOR
static bdescr *
alloc_mega_group_at (void *mblock, StgWord mblocks)
{
    bdescr *bd, *result;
    nat chunk;
    void *r;

    chunk = mblock_address_get_chunk(mblock);

    // Test if any mblock is already in use
    if (mblock_bitmap_test_any_alloced(mblock, mblocks))
        return NULL;

    // Test if all mblocks are free - if so, fast path to asking
    // the MBlock layer directly
    if (!mblock_bitmap_test_any_valid(mblock, mblocks)) {
        // This will not fail because we know the mblocks are not
        // valid
        r = getMBlocksAt(mblock, mblocks);
        ASSERT (r == mblock);
        initMBlock(r);
    } else {
        nat first;
        StgWord n;
        void *addr;
        bdescr *state, *iter, *prev;
        // Slow path walking the free list

        addr = mblock;
        n = mblocks;
        state = free_mblock_lists[chunk];

        // Find the first block that is valid
        while (n > 0) {
            first = mblock_bitmap_find_first_valid(addr, n);
            ASSERT (first != (nat)-1);

            if (first != 0) {
                // Allocate all mblocks up to the first valid one directly from
                // the MBlock layer
                r = getMBlocksAt(addr, first);
                ASSERT (r == addr);
                addr = (void*)((W_)r + first*MBLOCK_SIZE);
                n -= first;
                continue;
            }

            bd = FIRST_BDESCR (addr);
            ASSERT (bd->free == (P_)-1);

            // Find the right place in the free list
            prev = NULL;
            iter = state;
            while (iter != bd) {
                ASSERT (iter);
                prev = iter;

                // If iter crosses into bd area, we need to split iter
                if ((W_)MBLOCK_ROUND_DOWN(iter) +
                    (W_)BLOCKS_TO_MBLOCKS(iter->blocks) * MBLOCK_SIZE >
                    (W_)MBLOCK_ROUND_DOWN(bd)) {
                    nat mblock_total;
                    nat mblock_diff;

                    mblock_total = BLOCKS_TO_MBLOCKS(iter->blocks);
                    mblock_diff = ((W_)MBLOCK_ROUND_DOWN(bd) -
                                   (W_)MBLOCK_ROUND_DOWN(iter)) / MBLOCK_SIZE;
                    ASSERT (mblock_diff > 0);
                    iter->blocks = MBLOCK_GROUP_BLOCKS(mblock_diff);
                    bd->link = iter->link;
                    bd->blocks = MBLOCK_GROUP_BLOCKS(mblock_total-mblock_diff);
                    break;
                } else {
                    iter = iter->link;
                }
            }

            if (bd->blocks > MBLOCK_GROUP_BLOCKS(n)) {
                // Allocate the first part of this free list item
                // and replace it with iter, which used to point in the
                // middle
                iter = FIRST_BDESCR ((W_)MBLOCK_ROUND_DOWN(bd) +
                                     n * MBLOCK_SIZE);
                if (prev)
                    prev->link = iter;
                else
                    free_mblock_lists[chunk] = iter;

                if (prev) {
                    ASSERT (prev->link != prev);
                    ASSERT (MBLOCK_ROUND_DOWN(prev->link) !=
                            (StgWord8*)MBLOCK_ROUND_DOWN(prev) +
                            BLOCKS_TO_MBLOCKS(prev->blocks) * MBLOCK_SIZE);
                }

                iter->link = bd->link;
                iter->blocks = MBLOCK_GROUP_BLOCKS(BLOCKS_TO_MBLOCKS(bd->blocks) - n);
                ASSERT (iter->link != iter);
                if (iter->link) {
                    ASSERT (MBLOCK_ROUND_DOWN(iter->link) !=
                            (StgWord8*)MBLOCK_ROUND_DOWN(iter) +
                            BLOCKS_TO_MBLOCKS(iter->blocks) * MBLOCK_SIZE);
                }

                ASSERT(BLOCKS_TO_MBLOCKS(bd->blocks) - n > 0);
                n = 0;
            } else {
                // Allocate the entirety of this free list item
                if (prev)
                    prev->link = bd->link;
                else
                    free_mblock_lists[chunk] = bd->link;

                if (prev) {
                    ASSERT (MBLOCK_ROUND_DOWN(prev->link) !=
                            (StgWord8*)MBLOCK_ROUND_DOWN(prev) +
                            BLOCKS_TO_MBLOCKS(prev->blocks) * MBLOCK_SIZE);
                }

                addr = (void*)((W_)addr + BLOCKS_TO_MBLOCKS(bd->blocks) *
                               MBLOCK_SIZE);
                n -= BLOCKS_TO_MBLOCKS(bd->blocks);
            }
        }
    }

    result = FIRST_BDESCR(mblock);
    initMBlock(mblock);
    result->blocks = MBLOCK_GROUP_BLOCKS(mblocks);
    mblock_bitmap_mark(mblock, 1, MBLOCK_ALLOCED);
    mblock_bitmap_mark((void*)((W_)mblock + MBLOCK_SIZE),
                       mblocks - 1, MBLOCK_ALLOCED_TAIL);

    IF_DEBUG(sanity, checkFreeListSanity());

    return result;
}

static bdescr *
find_group_head (bdescr *bd)
{
    if (bd->blocks != 0)
        return bd;

    // Adjust the link to remove the history of coalesces
    // that happened
    return bd->link = find_group_head(bd->link);
}

bdescr *
allocGroupAt (void *addr, W_ n)
{
    bdescr *bd, *head, *rem;
    StgWord ln;
    nat chunk;
    void *mblock;
    StgWord32 blocks;

    if (n == 0) barf("allocGroupAt: requested zero blocks");

    ASSERT (addr == BLOCK_ROUND_DOWN (addr));

    chunk = mblock_address_get_chunk (addr);
    ASSERT (chunk != 0 && chunk < MBLOCK_NUM_CHUNKS);

    mblock = MBLOCK_ROUND_DOWN(addr);

    if (n >= BLOCKS_PER_MBLOCK)
    {
        StgWord mblocks;

        ASSERT (addr == FIRST_BLOCK(mblock));

        mblocks = BLOCKS_TO_MBLOCKS(n);
        bd = alloc_mega_group_at(mblock, mblocks);
        if (bd == NULL)
            return NULL;

        n_alloc_blocks += mblocks * BLOCKS_PER_MBLOCK;
        if (n_alloc_blocks > hw_alloc_blocks) hw_alloc_blocks = n_alloc_blocks;

        // only the bdescrs of the first MB are required to be initialised
        initGroup(bd);
        goto finish;
    }

    ASSERT (MBLOCK_ROUND_DOWN(addr) ==
            MBLOCK_ROUND_DOWN((W_)addr + n * BLOCK_SIZE - 1));

    // Fast path if the corresponding megablock is not allocated
    if ((head = alloc_mega_group_at(mblock, 1))) {
        n_alloc_blocks += BLOCKS_PER_MBLOCK;
        if (n_alloc_blocks > hw_alloc_blocks) hw_alloc_blocks = n_alloc_blocks;

        bd = Bdescr((P_) addr);
        bd->blocks = n;
        ASSERT (n + (bd - head) <= BLOCKS_PER_MBLOCK);
        initGroup(bd);                   // we know the group will fit

        if (head != bd) {
            head->blocks = bd - head;
            initGroup(head);
            freeGroup(head);
        }

        if (BLOCKS_PER_MBLOCK - (n + (bd - head)) > 0) {
            rem = bd + n;
            rem->blocks = BLOCKS_PER_MBLOCK - (n + (bd - head));
            initGroup(rem); // init the slop
            freeGroup(rem); // add the slop on to the free list
        }
        goto finish;
    }

    ASSERT (mblock_bitmap_test_any_alloced(mblock, 1));

    if (mblock_bitmap_get(mblock, 0) == MBLOCK_ALLOCED_TAIL) {
        // In the middle of a mega group
        return NULL;
    }

    bd = Bdescr((P_) addr);

    head = find_group_head(bd);
    ASSERT (bd >= head && bd < head + head->blocks);

    if (head->free != (P_)-1 ||
        head->blocks < n + (bd-head)) {
        // This group is allocated (or there is not enough space)
        return NULL;
    }

    // Yay, we can finally allocate!
    n_alloc_blocks += n;
    if (n_alloc_blocks > hw_alloc_blocks) hw_alloc_blocks = n_alloc_blocks;

    // Find on which free list this block lives
    blocks = head->blocks;
    ln = log_2(blocks);
    dbl_link_remove(head, &free_lists[chunk][ln]);

    if (head != bd) {
        head->blocks = bd - head;
        setup_tail(head);
        ln = log_2(head->blocks);
        dbl_link_onto(head, &free_lists[chunk][ln]);
    }

    if (head + blocks > bd + n) {
        rem = bd + n;
        rem->blocks = blocks - n - (bd - head);
        // we must init all the slop afterwards, otherwise it might
        // keep pointing to the old head
        initGroup(rem);
        rem->free = (void*)-1;
        ln = log_2(rem->blocks);
        dbl_link_onto(rem, &free_lists[chunk][ln]);
    }

    bd->blocks = n;
    initGroup(bd);

finish:
    IF_DEBUG(sanity, memset(bd->start, 0xaa, bd->blocks * BLOCK_SIZE));
    IF_DEBUG(sanity, checkFreeListSanity());
    return bd;
}
#endif

//
// Allocate a chunk of blocks that is at least min and at most max
// blocks in size. This API is used by the nursery allocator that
// wants contiguous memory preferably, but doesn't require it.  When
// memory is fragmented we might have lots of chunks that are
// less than a full megablock, so allowing the nursery allocator to
// use these reduces fragmentation considerably.  e.g. on a GHC build
// with +RTS -H, I saw fragmentation go from 17MB down to 3MB on a
// single compile.
//
// Further to this: in #7257 there is a program that creates serious
// fragmentation such that the heap is full of tiny <4 block chains.
// The nursery allocator therefore has to use single blocks to avoid
// fragmentation, but we make sure that we allocate large blocks
// preferably if there are any.
//
bdescr *
allocLargeChunk (W_ min, W_ max)
{
    bdescr *bd;
    StgWord ln, lnmax;
    nat chunk = 0;

    if (min >= BLOCKS_PER_MBLOCK) {
        return allocGroup(max);
    }

    ln = log_2_ceil(min);
    lnmax = log_2_ceil(max); // tops out at MAX_FREE_LIST

    while (ln < lnmax && free_lists[chunk][ln] == NULL) {
        ln++;
    }
    if (ln == lnmax) {
        return allocGroup(max);
    }
    bd = free_lists[chunk][ln];

    if (bd->blocks <= max)              // exactly the right size!
    {
        dbl_link_remove(bd, &free_lists[chunk][ln]);
        initGroup(bd);
    }
    else   // block too big...
    {
        bd = split_free_block(bd, max, chunk, ln);
        ASSERT(bd->blocks == max);
        initGroup(bd);
    }

    n_alloc_blocks += bd->blocks;
    if (n_alloc_blocks > hw_alloc_blocks) hw_alloc_blocks = n_alloc_blocks;

    IF_DEBUG(sanity, memset(bd->start, 0xaa, bd->blocks * BLOCK_SIZE));
    IF_DEBUG(sanity, checkFreeListSanity());
    return bd;
}

bdescr *
allocGroup_lock(W_ n)
{
    bdescr *bd;
    ACQUIRE_SM_LOCK;
    bd = allocGroup(n);
    RELEASE_SM_LOCK;
    return bd;
}

bdescr *
allocBlock(void)
{
    return allocGroup(1);
}

bdescr *
allocBlockInChunk(nat chunk)
{
    return allocGroupInChunk(chunk, 1);
}

bdescr *
allocBlock_lock(void)
{
    bdescr *bd;
    ACQUIRE_SM_LOCK;
    bd = allocBlock();
    RELEASE_SM_LOCK;
    return bd;
}

/* -----------------------------------------------------------------------------
   De-Allocation
   -------------------------------------------------------------------------- */

STATIC_INLINE bdescr *
coalesce_mblocks (bdescr *p)
{
    bdescr *q;

    q = p->link;
    if (q != NULL &&
        MBLOCK_ROUND_DOWN(q) ==
        (StgWord8*)MBLOCK_ROUND_DOWN(p) +
        BLOCKS_TO_MBLOCKS(p->blocks) * MBLOCK_SIZE) {
        // can coalesce
        p->blocks  = MBLOCK_GROUP_BLOCKS(BLOCKS_TO_MBLOCKS(p->blocks) +
                                         BLOCKS_TO_MBLOCKS(q->blocks));
        p->link = q->link;
        return p;
    }
    return q;
}

static void
free_mega_group (nat chunk, bdescr *mg)
{
    bdescr *bd, *prev;

    mblock_bitmap_mark(MBLOCK_ROUND_DOWN(mg), BLOCKS_TO_MBLOCKS(mg->blocks),
                       MBLOCK_FREE);

    // Find the right place in the free list.  free_mblock_list is
    // sorted by *address*, not by size as the free_list is.
    prev = NULL;
    bd = free_mblock_lists[chunk];
    while (bd && bd->start < mg->start) {
        prev = bd;
        bd = bd->link;
    }

    // coalesce backwards
    if (prev)
    {
        mg->link = prev->link;
        prev->link = mg;
        mg = coalesce_mblocks(prev);
    }
    else
    {
        mg->link = free_mblock_lists[chunk];
        free_mblock_lists[chunk] = mg;
    }
    // coalesce forwards
    coalesce_mblocks(mg);

    IF_DEBUG(sanity, checkFreeListSanity());
}


void
freeGroup(bdescr *p)
{
  StgWord ln;
  nat chunk;

  // Todo: not true in multithreaded GC
  // ASSERT_SM_LOCK();

  ASSERT(p->free != (P_)-1);

  // Tricky: the chunk of a block descriptor is the same as the
  // chunk of the block it describes (because they live in the same
  // mblock)
  chunk = mblock_address_get_chunk (p);

  p->free = (void *)-1;  /* indicates that this block is free */
  p->gen = NULL;
  p->gen_no = 0;
  /* fill the block group with garbage if sanity checking is on */
  IF_DEBUG(sanity,memset(p->start, 0xaa, (W_)p->blocks * BLOCK_SIZE));

  if (p->blocks == 0) barf("freeGroup: block size is zero");

  if (p->blocks >= BLOCKS_PER_MBLOCK)
  {
      StgWord mblocks;

      mblocks = BLOCKS_TO_MBLOCKS(p->blocks);
      // If this is an mgroup, make sure it has the right number of blocks
      ASSERT(p->blocks == MBLOCK_GROUP_BLOCKS(mblocks));

      n_alloc_blocks -= mblocks * BLOCKS_PER_MBLOCK;

      free_mega_group(chunk, p);
      return;
  }

  ASSERT(n_alloc_blocks >= p->blocks);
  n_alloc_blocks -= p->blocks;

  // coalesce forwards
  {
      bdescr *next;
      next = p + p->blocks;
      if (next <= LAST_BDESCR(MBLOCK_ROUND_DOWN(p)) && next->free == (P_)-1)
      {
          p->blocks += next->blocks;
          ln = log_2(next->blocks);
          dbl_link_remove(next, &free_lists[chunk][ln]);
          if (p->blocks == BLOCKS_PER_MBLOCK)
          {
              free_mega_group(chunk, p);
              return;
          }
          setup_tail(p);
          // Set up links to the new head (for allocGroupAt,
          // which wants to look at an arbitrary point in the heap
          // and find the head of a free group)
          next->blocks = 0;
          next->link = p;
      }
  }

  // coalesce backwards
  if (p != FIRST_BDESCR(MBLOCK_ROUND_DOWN(p)))
  {
      bdescr *prev;
      prev = p - 1;
      if (prev->blocks == 0) prev = prev->link; // find the head

      if (prev->free == (P_)-1)
      {
          ln = log_2(prev->blocks);
          dbl_link_remove(prev, &free_lists[chunk][ln]);
          prev->blocks += p->blocks;
          if (prev->blocks >= BLOCKS_PER_MBLOCK)
          {
              free_mega_group(chunk, prev);
              return;
          }
          p->blocks = 0;
          p->link = prev;
          p = prev;
      }
  }

  setup_tail(p);
  free_list_insert(chunk, p);

  IF_DEBUG(sanity, checkFreeListSanity());
}

void
freeGroup_lock(bdescr *p)
{
    ACQUIRE_SM_LOCK;
    freeGroup(p);
    RELEASE_SM_LOCK;
}

void
freeChain(bdescr *bd)
{
  bdescr *next_bd;
  while (bd != NULL) {
    next_bd = bd->link;
    freeGroup(bd);
    bd = next_bd;
  }
}

void
freeChain_lock(bdescr *bd)
{
    ACQUIRE_SM_LOCK;
    freeChain(bd);
    RELEASE_SM_LOCK;
}

static void
initMBlock(void *mblock)
{
    bdescr *bd;
    StgWord8 *block;

    /* the first few Bdescr's in a block are unused, so we don't want to
     * put them all on the free list.
     */
    block = FIRST_BLOCK(mblock);
    bd    = FIRST_BDESCR(mblock);

    /* Initialise the start field of each block descriptor
     */
    for (; block <= (StgWord8*)LAST_BLOCK(mblock); bd += 1,
             block += BLOCK_SIZE) {
        bd->start = (void*)block;
    }
}

/* -----------------------------------------------------------------------------
   Stats / metrics
   -------------------------------------------------------------------------- */

W_
countBlocks(bdescr *bd)
{
    W_ n;
    for (n=0; bd != NULL; bd=bd->link) {
        n += bd->blocks;
    }
    return n;
}

// (*1) Just like countBlocks, except that we adjust the count for a
// megablock group so that it doesn't include the extra few blocks
// that would be taken up by block descriptors in the second and
// subsequent megablock.  This is so we can tally the count with the
// number of blocks allocated in the system, for memInventory().
W_
countAllocdBlocks(bdescr *bd)
{
    W_ n;
    for (n=0; bd != NULL; bd=bd->link) {
        n += bd->blocks;

        // hack for megablock groups: see (*1) above
        if (bd->blocks > BLOCKS_PER_MBLOCK) {
            n -= (MBLOCK_SIZE / BLOCK_SIZE - BLOCKS_PER_MBLOCK)
                * (bd->blocks/(MBLOCK_SIZE/BLOCK_SIZE));
        }
    }
    return n;
}

void returnMemoryToOS(nat n /* megablocks */)
{
    static bdescr *bd;
    StgWord size;
    nat i;

    for (i = 0; i <= MBLOCK_NUM_CHUNKS; i++) {
        bd = free_mblock_lists[i];
        while ((n > 0) && (bd != NULL)) {
            size = BLOCKS_TO_MBLOCKS(bd->blocks);
            if (size > n) {
                StgWord newSize = size - n;
                char *freeAddr = MBLOCK_ROUND_DOWN(bd->start);
                freeAddr += newSize * MBLOCK_SIZE;
                bd->blocks = MBLOCK_GROUP_BLOCKS(newSize);
                freeMBlocks(freeAddr, n);
                mblock_bitmap_mark((void*)freeAddr, n, MBLOCK_INVALID);
                n = 0;
            }
            else {
                char *freeAddr = MBLOCK_ROUND_DOWN(bd->start);
                n -= size;
                bd = bd->link;
                freeMBlocks(freeAddr, size);
                mblock_bitmap_mark((void*)freeAddr, size, MBLOCK_INVALID);
            }
        }

        free_mblock_lists[i] = bd;
    }

    // Ask the OS to release any address space portion
    // that was associated with the just released MBlocks
    //
    // Historically, we used to ask the OS directly (via
    // osReleaseFreeMemory()) - now the MBlock layer might
    // have a reason to preserve the address space range,
    // so we keep it
    releaseFreeMemory();

    IF_DEBUG(gc,
        if (n != 0) {
            debugBelch("Wanted to free %d more MBlocks than are freeable\n",
                       n);
        }
    );
}

/* -----------------------------------------------------------------------------
   Debugging
   -------------------------------------------------------------------------- */

#ifdef DEBUG
static void
check_tail (bdescr *bd)
{
    bdescr *tail = tail_of(bd);

    if (tail != bd)
    {
        ASSERT(tail->blocks == 0);
        ASSERT(tail->free == 0);
        ASSERT(tail->link == bd);
    }
}

static void
checkFreeListSanityInChunk(nat chunk)
{
    bdescr *bd, *prev;
    StgWord ln, min;


    min = 1;
    for (ln = 0; ln < MAX_FREE_LIST; ln++) {
        IF_DEBUG(block_alloc,
                 debugBelch("free block list [%" FMT_Word "]:\n", ln));

        prev = NULL;
        for (bd = free_lists[chunk][ln]; bd != NULL; prev = bd, bd = bd->link)
        {
            IF_DEBUG(block_alloc,
                     debugBelch("group at %p, length %ld blocks\n",
                                bd->start, (long)bd->blocks));
            ASSERT(bd->free == (P_)-1);
            ASSERT(bd->blocks > 0 && bd->blocks < BLOCKS_PER_MBLOCK);
            ASSERT(bd->blocks >= min && bd->blocks <= (min*2 - 1));
            ASSERT(bd->link != bd); // catch easy loops

            check_tail(bd);

            if (prev)
                ASSERT(bd->u.back == prev);
            else
                ASSERT(bd->u.back == NULL);

            {
                bdescr *next;
                next = bd + bd->blocks;
                if (next <= LAST_BDESCR(MBLOCK_ROUND_DOWN(bd)))
                {
                    ASSERT(next->free != (P_)-1);
                }
            }
        }
        min = min << 1;
    }

    prev = NULL;
    for (bd = free_mblock_lists[chunk]; bd != NULL; prev = bd, bd = bd->link)
    {
        IF_DEBUG(block_alloc,
                 debugBelch("mega group at %p, length %ld blocks\n",
                            bd->start, (long)bd->blocks));

        ASSERT(bd->link != bd); // catch easy loops

        if (bd->link != NULL)
        {
            // make sure the list is sorted
            ASSERT(bd->start < bd->link->start);
        }

        ASSERT(bd->blocks >= BLOCKS_PER_MBLOCK);
        ASSERT(MBLOCK_GROUP_BLOCKS(BLOCKS_TO_MBLOCKS(bd->blocks))
               == bd->blocks);

        // make sure we're fully coalesced
        if (bd->link != NULL)
        {
            ASSERT(MBLOCK_ROUND_DOWN(bd->link) !=
                   (StgWord8*)MBLOCK_ROUND_DOWN(bd) +
                   BLOCKS_TO_MBLOCKS(bd->blocks) * MBLOCK_SIZE);
        }
    }
}

void
checkFreeListSanity(void)
{
    nat i;

    for (i = 0; i <= MBLOCK_NUM_CHUNKS; i++)
        checkFreeListSanityInChunk(i);
}

static W_ /* BLOCKS */
countFreeListInChunk(nat chunk)
{
  bdescr *bd;
  W_ total_blocks = 0;
  StgWord ln;

  for (ln=0; ln < MAX_FREE_LIST; ln++) {
      for (bd = free_lists[chunk][ln]; bd != NULL; bd = bd->link) {
          total_blocks += bd->blocks;
      }
  }
  for (bd = free_mblock_lists[chunk]; bd != NULL; bd = bd->link) {
      total_blocks += BLOCKS_PER_MBLOCK * BLOCKS_TO_MBLOCKS(bd->blocks);
      // The caller of this function, memInventory(), expects to match
      // the total number of blocks in the system against mblocks *
      // BLOCKS_PER_MBLOCK, so we must subtract the space for the
      // block descriptors from *every* mblock.
  }
  return total_blocks;
}

W_
countFreeList(void)
{
    nat i;
    W_ v;

    v = 0;
    for (i = 0; i <= MBLOCK_NUM_CHUNKS; i++)
        v += countFreeListInChunk(i);

    return v;
}

void
markBlocks (bdescr *bd)
{
    for (; bd != NULL; bd = bd->link) {
        bd->flags |= BF_KNOWN;
    }
}

void
reportUnmarkedBlocks (void)
{
    void *mblock;
    bdescr *bd;

    debugBelch("Unreachable blocks:\n");
    for (mblock = getFirstMBlock(); mblock != NULL;
         mblock = getNextMBlock(mblock)) {
        for (bd = FIRST_BDESCR(mblock); bd <= LAST_BDESCR(mblock); ) {
            if (!(bd->flags & BF_KNOWN) && bd->free != (P_)-1) {
                debugBelch("  %p\n",bd);
            }
            if (bd->blocks >= BLOCKS_PER_MBLOCK) {
                mblock = (StgWord8*)mblock +
                    (BLOCKS_TO_MBLOCKS(bd->blocks) - 1) * MBLOCK_SIZE;
                break;
            } else {
                bd += bd->blocks;
            }
        }
    }
}

#endif
