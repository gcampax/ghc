/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team 1998-2008
 *
 * MegaBlock Allocator Interface.  This file contains all the dirty
 * architecture-dependent hackery required to get a chunk of aligned
 * memory from the operating system.
 *
 * ---------------------------------------------------------------------------*/

#include "PosixSource.h"
#include "Rts.h"

#include "RtsUtils.h"
#include "BlockAlloc.h"
#include "Trace.h"
#include "OSMem.h"

#include <string.h>

W_ peak_mblocks_allocated = 0;
W_ mblocks_allocated = 0;
W_ mpc_misses = 0;

/* -----------------------------------------------------------------------------
   The MBlock Map: provides our implementation of HEAP_ALLOCED() and the
   utilities to walk the really allocated (thus accessible without risk of
   segfault) heap
   -------------------------------------------------------------------------- */

/*
  There are two different cases here: either we use "large address
  space" (which really means two-step allocation), so we have to
  manage which memory is good (= accessible without fear of segfault)
  and which is not owned by us, or we use the older method and get
  good memory straight from the system.

  Both code paths need to provide:

  void *getFirstMBlock(void)
      return the first (lowest address) mblock
      that was actually committed

  void *getNextMBlock(void * mblock)
      return the first (lowest address) mblock
      that was committed, after the given one

  The calls should only be used in an interation fashion.

  void *getCommittedMBlocks(nat n)
      return @n new mblocks, ready to be used (reserved and committed)

  void *decommitMBlocks(char *addr, nat n)
      release memory for @n mblocks, starting at the given address

  void releaseFreeMemory()
      potentially release any address space that was associated
      with recently decommitted blocks
*/

#ifdef USE_LARGE_ADDRESS_SPACE

// Large address space means we use two-step allocation: reserve
// something large upfront, and then commit as needed
// (This is normally only useful on 64-bit, where we can assume
// that reserving 1TB is possible)
//
// There is no block map in this case, but there is a free list
// of blocks that were committed and decommitted at least once,
// which we use to choose which block to commit next in the already
// reserved space.
//
// We cannot let the OS choose it as we do in the
// non large address space case, because the committing wants to
// know the exact address upfront.
//
// The free list is coalesced and ordered, which means that
// allocate and free are worst-case O(n), but benchmarks have shown
// that this is not a significant problem, because large (>=2MB)
// allocations are infrequent and their time is mostly insignificant
// compared to the time to use that memory.
//
// The free list is stored in malloc()'d memory, unlike the other free
// lists in BlockAlloc.c which are stored in block descriptors,
// because we cannot touch the contents of decommitted mblocks.

typedef struct free_list {
    struct free_list *prev;
    struct free_list *next;
    W_ address;
    W_ size;
} free_list;

#ifndef USE_STRIPED_ALLOCATOR
#define MBLOCK_NUM_CHUNKS 0
W_ mblock_address_space_begin = 0;
#define MBLOCK_SPACE_BEGIN mblock_address_space_begin
#define MBLOCK_NORMAL_SPACE_SIZE MBLOCK_SPACE_SIZE
#define MBLOCK_CHUNK_SIZE 0
#endif

// Note that chunk 0 is special because it is larger (it contains
// the normal Haskell heap)
static free_list *free_list_heads[MBLOCK_NUM_CHUNKS + 1];
static W_         mblock_high_watermarks[MBLOCK_NUM_CHUNKS + 1];

static struct {
    free_list *iter;
    nat        chunk_no;
} iter_state;

static void *getAllocatedMBlock(free_list **start_iter,
                                W_          mblock_high_watermark,
                                W_          startingAt)
{
    free_list *iter;
    W_ p = startingAt;

    for (iter = *start_iter; iter != NULL; iter = iter->next)
    {
        if (p < iter->address)
            break;

        if (p == iter->address)
            p += iter->size;
    }

    *start_iter = iter;

    if (p >= mblock_high_watermark)
        return NULL;

    return (void*)p;
}

static void *iterateFindMBlock(W_ startingAt)
{
    void *p;

    if (iter_state.chunk_no == 0) {
        p = getAllocatedMBlock(&iter_state.iter,
                               mblock_high_watermarks[0],
                               startingAt);
        if (p != NULL)
            return p;

        iter_state.iter = free_list_heads[1];
        iter_state.chunk_no = 1;
        startingAt = MBLOCK_SPACE_BEGIN + MBLOCK_NORMAL_SPACE_SIZE;
    }

    while (iter_state.chunk_no <= MBLOCK_NUM_CHUNKS) {
        p = getAllocatedMBlock(&iter_state.iter,
                               mblock_high_watermarks[iter_state.chunk_no],
                               startingAt);
        if (p != NULL)
            return p;

        iter_state.chunk_no ++;
        iter_state.iter = free_list_heads[iter_state.chunk_no];
        startingAt = MBLOCK_SPACE_BEGIN + MBLOCK_NORMAL_SPACE_SIZE +
            (iter_state.chunk_no - 1) * MBLOCK_CHUNK_SIZE;
    }

    return NULL;
}

void * getFirstMBlock(void)
{
    iter_state.iter = free_list_heads[0];
    iter_state.chunk_no = 0;

    return iterateFindMBlock(MBLOCK_SPACE_BEGIN);
}

void * getNextMBlock(void *mblock)
{
    return iterateFindMBlock((W_)mblock + MBLOCK_SIZE);
}

static void *getReusableMBlocks(free_list **free_list_head,
                                nat         n)
{
    struct free_list *iter;
    W_ size = MBLOCK_SIZE * (W_)n;

    for (iter = *free_list_head; iter != NULL; iter = iter->next)
    {
        void *addr;

        if (iter->size < size)
            continue;

        addr = (void*)iter->address;
        iter->address += size;
        iter->size -= size;
        if (iter->size == 0) {
            struct free_list *prev, *next;

            prev = iter->prev;
            next = iter->next;

            if (prev == NULL)
            {
                ASSERT(*free_list_head == iter);
                *free_list_head = next;
            }
            else
            {
                prev->next = next;
            }
            if (next != NULL) {
                next->prev = prev;
            }
            stgFree(iter);
        }

        osCommitMemory(addr, size);
        return addr;
    }

    return NULL;
}

static void *getFreshMBlocks(W_  *mblock_high_watermark,
                             W_   mblock_alloc_max,
                             nat  n)
{
    W_ size = MBLOCK_SIZE * (W_)n;
    void *addr = (void*)(*mblock_high_watermark);

    if (*mblock_high_watermark + size > mblock_alloc_max)
    {
        // whoa, 1 TB of heap?
        errorBelch("out of memory");
        stg_exit(EXIT_HEAPOVERFLOW);
    }

    osCommitMemory(addr, size);
    *mblock_high_watermark += size;
    return addr;
}

static void *getCommittedMBlocksInChunk(nat chunk, nat n)
{
    W_ *mblock_high_watermark;
    free_list **free_list_head;
    W_ mblock_alloc_max;
    void *p;

    mblock_high_watermark = &mblock_high_watermarks[chunk];
    mblock_alloc_max = MBLOCK_SPACE_BEGIN + MBLOCK_NORMAL_SPACE_SIZE
        + chunk * MBLOCK_CHUNK_SIZE;
    free_list_head = &free_list_heads[chunk];

    p = getReusableMBlocks(free_list_head, n);
    if (p == NULL)
        p = getFreshMBlocks(mblock_high_watermark, mblock_alloc_max, n);

    ASSERT(p != NULL && p != (void*)-1);
    return p;
}

static void *getCommittedMBlocks(nat n)
{
    return getCommittedMBlocksInChunk(0, n);
}

#ifdef USE_STRIPED_ALLOCATOR
static void *getCommittedMBlocksAt(char *addr, nat n)
{
    nat chunk;
    free_list **free_list_head;
    W_ *mblock_high_watermark;
    free_list *iter, *last;
    free_list *new_iter;
    W_ size = MBLOCK_SIZE * (W_)n;
    W_ address = (W_)addr;

    chunk = mblock_address_get_chunk((void*)addr);

    free_list_head = &free_list_heads[chunk];
    mblock_high_watermark = &mblock_high_watermarks[chunk];

    last = NULL;
    for (iter = *free_list_head; iter != NULL; iter = iter->next)
    {
        last = iter;

        // If we walk past the given address, we have no hope of
        // finding a free range for this address
        if (iter->address > address)
            return NULL;

        // If the free block ends exactly at address we have no
        // hope of finding a free range (because the next byte
        // is allocated, as the free list is compacted)
        if (iter->address + iter->size == address)
            return NULL;

        // If the free block ends before the required address,
        // try with the next free block
        if (iter->address + iter->size < address)
            continue;

        // Cool, so address falls exactly in this free block
        // Check that we have enough space
        if (iter->address + iter->size < address + size)
            return NULL;

        // Awesome, we can use this block

        // We want to allocate at the beginning, move the free block forward
        if (iter->address == address) {
            iter->address = address + size;
            iter->size -= size;
            if (iter->size == 0) {
                if (iter->prev)
                    iter->prev->next = iter->next;
                else
                    *free_list_head = iter->next;
                if (iter->next)
                    iter->next->prev = iter->prev;
                stgFree(iter);
            }
            goto success;
        }

        // We want to allocate at the end, cut the free block at the end
        if (iter->address + iter->size == address + size) {
            iter->size -= size;
            if (iter->size == 0) {
                if (iter->prev)
                    iter->prev->next = iter->next;
                else
                    *free_list_head = iter->next;
                if (iter->next)
                    iter->next->prev = iter->prev;
                stgFree(iter);
            }
            goto success;
        }

        // We need to split!
        new_iter = stgMallocBytes(sizeof(struct free_list), "getCommittedMBlocksAt");
        new_iter->address = address + size;
        new_iter->size = iter->address + iter->size - new_iter->address;
        new_iter->next = iter->next;
        new_iter->prev = iter;
        if (new_iter->next)
            new_iter->next->prev = new_iter;
        iter->size = address - iter->address;
        iter->next = new_iter;
        goto success;
    }

    // The address is not in the free list, check the high_watermark
    if (address < *mblock_high_watermark)
        return NULL;

    if (address == *mblock_high_watermark) {
        *mblock_high_watermark += size;
        goto success;
    }

    // Need to create a new free block
    new_iter = stgMallocBytes(sizeof(struct free_list), "getCommittedMBlocksAt");
    new_iter->address = *mblock_high_watermark;
    *mblock_high_watermark = address + size;
    new_iter->size = address - new_iter->address;
    new_iter->next = NULL;
    new_iter->prev = last;
    if (last)
        last->next = new_iter;
    else
        *free_list_head = new_iter;

 success:
    osCommitMemory((void*)address, size);

    return (void*)address;
}
#endif

static void decommitMBlocksInChunk(nat chunk, char *addr, nat n)
{
    free_list **free_list_head;
    W_ *mblock_high_watermark;
    struct free_list *iter, *prev;
    W_ size = MBLOCK_SIZE * (W_)n;
    W_ address = (W_)addr;

    osDecommitMemory(addr, size);

    free_list_head = &free_list_heads[chunk];
    mblock_high_watermark = &mblock_high_watermarks[chunk];

    prev = NULL;
    for (iter = *free_list_head; iter != NULL; iter = iter->next)
    {
        prev = iter;

        if (iter->address + iter->size < address)
            continue;

        if (iter->address + iter->size == address) {
            iter->size += size;

            if (address + size == *mblock_high_watermark) {
                *mblock_high_watermark -= iter->size;
                if (iter->prev) {
                    iter->prev->next = NULL;
                } else {
                    ASSERT(iter == *free_list_head);
                    free_list_head = NULL;
                }
                stgFree(iter);
                return;
            }

            if (iter->next &&
                iter->next->address == iter->address + iter->size) {
                struct free_list *next;

                next = iter->next;
                iter->size += next->size;
                iter->next = next->next;

                if (iter->next) {
                    iter->next->prev = iter;

                    /* We don't need to consolidate more */
                    ASSERT(iter->next->address > iter->address + iter->size);
                }

                stgFree(next);
            }
            return;
        } else if (address + size == iter->address) {
            iter->address = address;
            iter->size += size;

            /* We don't need to consolidate backwards
               (because otherwise it would have been handled by
               the previous iteration) */
            if (iter->prev) {
                ASSERT(iter->prev->address + iter->prev->size < iter->address);
            }
            return;
        } else {
            struct free_list *new_iter;

            /* All other cases have been handled */
            ASSERT(iter->address > address + size);

            new_iter = stgMallocBytes(sizeof(struct free_list), "freeMBlocks");
            new_iter->address = address;
            new_iter->size = size;
            new_iter->next = iter;
            new_iter->prev = iter->prev;
            if (new_iter->prev)
            {
                new_iter->prev->next = new_iter;
            }
            else
            {
                ASSERT(iter == *free_list_head);
                *free_list_head = new_iter;
            }
            iter->prev = new_iter;
            return;
        }
    }

    if (iter == NULL)
    {
        /* We're past the last free list entry, so we must
           be the highest allocation so far
        */
        ASSERT(address + size <= *mblock_high_watermark);

        /* Fast path the case of releasing high or all memory */
        if (address + size == *mblock_high_watermark)
        {
            *mblock_high_watermark -= size;
        }
        else
        {
            struct free_list *new_iter;

            new_iter = stgMallocBytes(sizeof(struct free_list), "freeMBlocks");
            new_iter->address = address;
            new_iter->size = size;
            new_iter->next = NULL;
            new_iter->prev = prev;
            if (new_iter->prev)
            {
                ASSERT(new_iter->prev->next == NULL);
                new_iter->prev->next = new_iter;
            }
            else
            {
                ASSERT(*free_list_head == NULL);
                *free_list_head = new_iter;
            }
        }
    }
}

static void decommitMBlocks(char *addr, nat n)
{
    nat chunk;

    chunk = mblock_address_get_chunk ((void*)addr);
    return decommitMBlocksInChunk(chunk, addr, n);
}

void releaseFreeMemory(void)
{
    // This function exists for releasing address space
    // on Windows 32 bit
    //
    // Do nothing if USE_LARGE_ADDRESS_SPACE, we never want
    // to release address space

    debugTrace(DEBUG_gc, "mblock_high_watermark: %p\n", mblock_high_watermarks[0]);
}

static void freeOneFreeList(nat chunk)
{
    struct free_list *iter, *next;

    for (iter = free_list_heads[chunk]; iter != NULL; iter = next)
    {
        next = iter->next;
        stgFree(iter);
    }
    free_list_heads[chunk] = NULL;
    mblock_high_watermarks[chunk] = (W_)-1;
}

static void freeAllFreeLists(void)
{
    nat i;

    for (i = 0; i <= MBLOCK_NUM_CHUNKS; i++)
        freeOneFreeList(i);
}

#else // USE_LARGE_ADDRESS_SPACE

#if SIZEOF_VOID_P == 4
StgWord8 mblock_map[MBLOCK_MAP_SIZE]; // initially all zeros

static void
setHeapAlloced(void *p, StgWord8 i)
{
    mblock_map[MBLOCK_MAP_ENTRY(p)] = i;
}

#elif SIZEOF_VOID_P == 8

MBlockMap **mblock_maps = NULL;

nat mblock_map_count = 0;

MbcCacheLine mblock_cache[MBC_ENTRIES];

static MBlockMap *
findMBlockMap(void *p)
{
    nat i;
    StgWord32 hi = (StgWord32) (((StgWord)p) >> 32);
    for( i = 0; i < mblock_map_count; i++ )
    {
        if(mblock_maps[i]->addrHigh32 == hi)
        {
            return mblock_maps[i];
        }
    }
    return NULL;
}

StgBool HEAP_ALLOCED_miss(StgWord mblock, void *p)
{
    MBlockMap *map;
    MBlockMapLine value;
    nat entry_no;

    entry_no = mblock & (MBC_ENTRIES-1);

    map = findMBlockMap(p);
    if (map)
    {
        mpc_misses++;
        value = map->lines[MBLOCK_MAP_LINE(p)];
        mblock_cache[entry_no] = (mblock<<1) | value;
        return value;
    }
    else
    {
        mblock_cache[entry_no] = (mblock<<1);
        return 0;
    }
}

static void
setHeapAlloced(void *p, StgWord8 i)
{
    MBlockMap *map = findMBlockMap(p);
    if(map == NULL)
    {
        mblock_map_count++;
        mblock_maps = stgReallocBytes(mblock_maps,
                                      sizeof(MBlockMap*) * mblock_map_count,
                                      "markHeapAlloced(1)");
        map = mblock_maps[mblock_map_count-1] =
            stgMallocBytes(sizeof(MBlockMap),"markHeapAlloced(2)");
        memset(map,0,sizeof(MBlockMap));
        map->addrHigh32 = (StgWord32) (((StgWord)p) >> 32);
    }

    map->lines[MBLOCK_MAP_LINE(p)] = i;

    {
        StgWord mblock;
        nat entry_no;

        mblock   = (StgWord)p >> MBLOCK_SHIFT;
        entry_no = mblock & (MBC_ENTRIES-1);
        mblock_cache[entry_no] = (mblock << 1) + i;
    }
}

#endif

static void
markHeapAlloced(void *p)
{
    setHeapAlloced(p, 1);
}

static void
markHeapUnalloced(void *p)
{
    setHeapAlloced(p, 0);
}

#if SIZEOF_VOID_P == 4

STATIC_INLINE
void * mapEntryToMBlock(nat i)
{
    return (void *)((StgWord)i << MBLOCK_SHIFT);
}

void * getFirstMBlock(void)
{
    nat i;

    for (i = 0; i < MBLOCK_MAP_SIZE; i++) {
        if (mblock_map[i]) return mapEntryToMBlock(i);
    }
    return NULL;
}

void * getNextMBlock(void *mblock)
{
    nat i;

    for (i = MBLOCK_MAP_ENTRY(mblock) + 1; i < MBLOCK_MAP_SIZE; i++) {
        if (mblock_map[i]) return mapEntryToMBlock(i);
    }
    return NULL;
}

#elif SIZEOF_VOID_P == 8

void * getNextMBlock(void *p)
{
    MBlockMap *map;
    nat off, j;
    nat line_no;
    MBlockMapLine line;

    for (j = 0; j < mblock_map_count; j++)  {
        map = mblock_maps[j];
        if (map->addrHigh32 == (StgWord)p >> 32) break;
    }
    if (j == mblock_map_count) return NULL;

    for (; j < mblock_map_count; j++) {
        map = mblock_maps[j];
        if (map->addrHigh32 == (StgWord)p >> 32) {
            line_no = MBLOCK_MAP_LINE(p);
            off  = (((StgWord)p >> MBLOCK_SHIFT) & (MBC_LINE_SIZE-1)) + 1;
            // + 1 because we want the *next* mblock
        } else {
            line_no = 0; off = 0;
        }
        for (; line_no < MBLOCK_MAP_ENTRIES; line_no++) {
            line = map->lines[line_no];
            for (; off < MBC_LINE_SIZE; off++) {
                if (line & (1<<off)) {
                    return (void*)(((StgWord)map->addrHigh32 << 32) +
                                   line_no * MBC_LINE_SIZE * MBLOCK_SIZE +
                                   off * MBLOCK_SIZE);
                }
            }
            off = 0;
        }
    }
    return NULL;
}

void * getFirstMBlock(void)
{
    MBlockMap *map = mblock_maps[0];
    nat line_no, off;
    MbcCacheLine line;

    for (line_no = 0; line_no < MBLOCK_MAP_ENTRIES; line_no++) {
        line = map->lines[line_no];
        if (line) {
            for (off = 0; off < MBC_LINE_SIZE; off++) {
                if (line & (1<<off)) {
                    return (void*)(((StgWord)map->addrHigh32 << 32) +
                                   line_no * MBC_LINE_SIZE * MBLOCK_SIZE +
                                   off * MBLOCK_SIZE);
                }
            }
        }
    }
    return NULL;
}

#endif // SIZEOF_VOID_P == 8

static void *getCommittedMBlocks(nat n)
{
    // The OS layer returns committed memory directly
    void *ret = osGetMBlocks(n);
    nat i;

    // fill in the table
    for (i = 0; i < n; i++) {
        markHeapAlloced( (StgWord8*)ret + i * MBLOCK_SIZE );
    }

    return ret;
}

static void decommitMBlocks(void *p, nat n)
{
    osFreeMBlocks(p, n);
    nat i;

    for (i = 0; i < n; i++) {
        markHeapUnalloced( (StgWord8*)p + i * MBLOCK_SIZE );
    }
}

void releaseFreeMemory(void)
{
    osReleaseFreeMemory();
}

#endif /* !USE_LARGE_ADDRESS_SPACE */

/* -----------------------------------------------------------------------------
   Allocate new mblock(s)
   -------------------------------------------------------------------------- */

void *
getMBlock(void)
{
  return getMBlocks(1);
}

// The external interface: allocate 'n' mblocks, and return the
// address.

void *
getMBlocks(nat n)
{
    void *ret;

    ret = getCommittedMBlocks(n);

    debugTrace(DEBUG_gc, "allocated %d megablock(s) at %p",n,ret);

    mblocks_allocated += n;
    peak_mblocks_allocated = stg_max(peak_mblocks_allocated, mblocks_allocated);

    return ret;
}

#ifdef USE_STRIPED_ALLOCATOR
void * getMBlocksAt(void *addr, nat n)
{
    void *ret;

    ret = getCommittedMBlocksAt(addr, n);
    if (ret == NULL)
        return ret;

    debugTrace(DEBUG_gc, "allocated %d megablock(s) at %p",n,ret);

    mblocks_allocated += n;
    peak_mblocks_allocated = stg_max(peak_mblocks_allocated, mblocks_allocated);

    return ret;
}

void *
getMBlockInChunk(nat chunk)
{
    return getMBlocksInChunk(chunk, 1);
}

// The external interface: allocate 'n' mblocks, and return the
// address.

void *
getMBlocksInChunk(nat chunk, nat n)
{
    void *ret;

    ret = getCommittedMBlocksInChunk(chunk, n);

    debugTrace(DEBUG_gc, "allocated %d megablock(s) at %p",n,ret);

    mblocks_allocated += n;
    peak_mblocks_allocated = stg_max(peak_mblocks_allocated, mblocks_allocated);

    return ret;
}
#endif

void
freeMBlocks(void *addr, nat n)
{
    debugTrace(DEBUG_gc, "freeing %d megablock(s) at %p",n,addr);

    mblocks_allocated -= n;

    decommitMBlocks(addr, n);
}

void
freeAllMBlocks(void)
{
    debugTrace(DEBUG_gc, "freeing all megablocks");

#ifdef USE_LARGE_ADDRESS_SPACE
    freeAllFreeLists();
    osReleaseHeapMemory();
#else
    osFreeAllMBlocks();

#if SIZEOF_VOID_P == 8
    nat n;
    for (n = 0; n < mblock_map_count; n++) {
        stgFree(mblock_maps[n]);
    }
    stgFree(mblock_maps);
#endif

#endif
}

void
initMBlocks(void)
{
    osMemInit();

#ifdef USE_LARGE_ADDRESS_SPACE
    {
#ifdef USE_STRIPED_ALLOCATOR
        nat i;

        osReserveHeapMemory();

        mblock_high_watermarks[0] = MBLOCK_SPACE_BEGIN;
        for (i = 0; i < MBLOCK_NUM_CHUNKS; i++) {
            mblock_high_watermarks[i+1] = MBLOCK_SPACE_BEGIN +
                MBLOCK_NORMAL_SPACE_SIZE + i * MBLOCK_CHUNK_SIZE;
        }
#else
        void *addr = osReserveHeapMemory();

        mblock_address_space_begin = (W_)addr;
        mblock_high_watermarks[0] = (W_)addr;
#endif
    }
#elif SIZEOF_VOID_P == 8
    memset(mblock_cache,0xff,sizeof(mblock_cache));
#endif
}
