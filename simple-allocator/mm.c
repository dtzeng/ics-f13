/*
 * mm.c
 *
 * Derek Tzeng
 * dtzeng
 *
 * This dynamic storage allocator supports malloc, free, realloc, calloc.
 *
 * This implementation uses a segregated storage strategy for keeping track of
 * free blocks.  The 5 segregated lists are partitioned by powers of six:
 * {6^0, (6^1)-1}, ... , {6^3, (6^4)-1}, {6^4, infinity}.
 *
 * In this implementation, all returned pointers are 8-byte aligned.
 *
 * mm_init: Allocates the initial heap area and initialize the segregated
 * lists.
 *
 * malloc: Returns a pointer to an allocated block payload of at least the
 * requested size if enough memory, otherwise returns NULL.
 *
 * free: Frees the requested block. Only works if the requested block was
 * returned by an earlier call to malloc, realloc, or calloc.
 * free(NULL) has no effect.
 *
 * realloc: If requested pointer is NULL, return malloc(size).
 *          If requested size is 0, equivalent to free(ptr), returns NULL.
 *          Otherwise, returns address of a new block with payload of at least
 *          the requested size, with the same contents of the old block. *
 *
 * calloc: Returns a pointer to an allocated block payload (memory set to zero)
 * of at least the requested size if enough memory, other returns NULL.
 *
 * This implementation also includes a heap consistency checker (mm_checkheap).
 * To run the heap consistency checker, uncomment the "#define DEBUG" line.
 * The heap consistency checker scans through the heap and segregated lists,
 * to check for any invariant violations.
 *
 * Internal helper functions:
 *
 * place: Allocates a block at the requested address, and splits if the
 * size of the remainder equals or exceeds the minimum block size.

 * find_fit: Uses a "first best fit policy" where it finds the first 10 fits
 * and uses the best fit out of the 10.
 *
 * coalesce: Uses a LIFO policy by coalescing the requested block
 * with adjacent blocks if necessary and adding it to the beginning
 * of the appropriate seg list.
 *
 * hascycle: Checks if a given free list contains a cycle by using
 * the tortoise hare algorithm.
 *
 * bucket: Determines which size class the requested block size is in,
 * and returns the offset from the beginning of the array of
 * segregated free lists.
 *
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
//#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT - 1)) & ~0x7)

/* Basic constants and macros */
#define WSIZE 4 /* Word and header/footer size (bytes) */
#define DSIZE 8 /* Double word size (bytes) */
#define QSIZE 16 /* Quadruple word size (bytes) */
#define CHUNKSIZE (260)

#define SEGS 5 /* Number of segregated lists */
#define RATIO 6 /* Power ratio of size classes */
#define LASTCLASS 1296 /* Lower limit of last size class, RATIO^(SEGS-1) */

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned long *)(p))
#define PUT(p, val) (*(unsigned long *)(p) = (val))

/* Read and write a pointer at address p */
#define GET_ADDRESS(p) ((char *)(GET(p)))
#define PUT_ADDRESS(p, ptr) (PUT(p, (unsigned long)(ptr)))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - DSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - QSIZE)

/* Given block ptr bp, compute address of adjacent next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - DSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - QSIZE)))

/* Given free block ptr bp,
   compute address of its next and previous pointers */
#define NEXT_PTR(bp) ((char *)(bp))
#define PREV_PTR(bp) ((char *)(bp) + DSIZE)

/* Given free block ptr bp,
   compute address of next and previous free blocks */
#define NEXT_FREEBLKP(bp) (GET_ADDRESS(NEXT_PTR(bp)))
#define PREV_FREEBLKP(bp) (GET_ADDRESS(PREV_PTR(bp)))

/* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */
static char *seg_listp = 0;  /* Pointer to segregated free lists */
static char *last_segp = 0;  /* Pointer to last segregated list */

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void splice_together(void *bp_prev, void *bp_next, size_t size);
static void printblock(void *bp);
static void checkblock(void *bp, int verbose);
static int in_heap(const void *p);
static int aligned(const void *p);
static int hascycle(void *bp);
static inline size_t bucket(size_t num);


/*
 * mm_init - Allocates initial heap area, initializes segregated lists.
 *           Return -1 on failure, 0 on success.
 */
int mm_init(void) {
  /* Create the initial empty heap */
  if((heap_listp = mem_sbrk(4 * DSIZE + SEGS * DSIZE)) == (void *)-1)
    return -1;
  PUT(heap_listp, 0); /* Alignment padding */
  for(size_t x = 1; x <= SEGS; x++) /* Segregated free lists */
    PUT_ADDRESS(heap_listp + (x * DSIZE), NULL);
  PUT(heap_listp + ((SEGS + 1) * DSIZE), PACK(QSIZE, 1)); /* Prologue header */
  PUT(heap_listp + ((SEGS + 2) * DSIZE), PACK(QSIZE, 1)); /* Prologue footer */
  PUT(heap_listp + ((SEGS + 3) * DSIZE), PACK(0, 1)); /* Epilogue header */

  seg_listp = heap_listp + DSIZE;
  last_segp = heap_listp + (SEGS * DSIZE);
  heap_listp += ((SEGS + 2) * DSIZE);

  /* Extend the empty heap with a free block of CHUNKSIZE bytes */
  if(extend_heap(CHUNKSIZE/WSIZE) == NULL)
    return -1;

  return 0;
}

/*
 * malloc - Return pointer to allocated block payload of at least size bytes.
 *          Pointer is aligned to (ALIGNMENT) bytes.
 *          Returns NULL if not enough memory.
 */
void *malloc (size_t size) {
  size_t asize; /* Adjusted block size */
  size_t extendsize; /* Amount to extend heap if no fit */
  char *bp;

  if(heap_listp == 0) {
    mm_init();
  }

  /* Ignore spurious requests */
  if(size == 0)
    return NULL;

  /* Adjust block size to include overhead and alignment reqs. */
  if(size <= QSIZE)
    asize = 2 * QSIZE;
  else
    asize = ALIGN(size + QSIZE);

  /* Search the free list for a fit */
  if((bp = find_fit(asize)) != NULL) {
    place(bp, asize);
    return bp;
  }

  /* No fit found. Get more memory and place the block */
  extendsize = MAX(asize, CHUNKSIZE);
  if((bp = extend_heap(extendsize/WSIZE)) == NULL) {
    return NULL;
  }
  place(bp, asize);

#ifdef DEBUG
  mm_checkheap(0);
#endif

  return bp;
}

/*
 * free - Frees the block at ptr.
 */
void free (void *ptr) {
  if(ptr == 0)
    return;

  size_t size = GET_SIZE(HDRP(ptr));
  if(heap_listp == 0) {
    mm_init();
  }

  PUT(HDRP(ptr), PACK(size, 0));
  PUT(FTRP(ptr), PACK(size, 0));
  coalesce(ptr);

#ifdef DEBUG
  mm_checkheap(0);
#endif
}

/*
 * realloc - If oldptr == NULL, equivalent to malloc(size).
 *           If size == 0, equivalent to free(ptr).
 *           Otherwise, allocate new block. If call does not fail,
 *           copy MIN(old size, new size) bytes to new block. Free old block.
 */
void *realloc(void *oldptr, size_t size) {
  size_t oldsize;
  void *newptr;

  /* If size == 0 then this is just free, and we return NULL. */
  if(size == 0) {
    mm_free(oldptr);
    return 0;
  }

  /* If oldptr is NULL, then this is just malloc. */
  if(oldptr == NULL) {
    return mm_malloc(size);
  }

  size_t asize;
  if(size <= QSIZE)
    asize = 2 * QSIZE;
  else
    asize = ALIGN(size + QSIZE);

  oldsize = GET_SIZE(HDRP(oldptr));

  /* If asize <= oldsize, make necessary changes, and return same address */
  if(asize == oldsize) {
    return oldptr;
  }
  else if(asize < oldsize) {
    if((oldsize - asize) >= (2 * QSIZE)) {
      PUT(HDRP(oldptr), PACK(asize, 1));
      PUT(FTRP(oldptr), PACK(asize, 1));
      void *bp = NEXT_BLKP(oldptr);
      PUT(HDRP(bp), PACK(oldsize - asize, 0));
      PUT(FTRP(bp), PACK(oldsize - asize, 0));
      coalesce(bp);
    }
    return oldptr;
  }

  /* If old block and next block have enough free space combined,
     extend the old block and return same address
  */
  void *next_block = NEXT_BLKP(oldptr);
  if((next_block != NULL) && !GET_ALLOC(HDRP(next_block))) {
    char *succ_next = NEXT_FREEBLKP(next_block);
    char *succ_prev = PREV_FREEBLKP(next_block);
    size_t nextsize = GET_SIZE(HDRP(next_block));
    if(asize <= (oldsize + nextsize)) {
      PUT(HDRP(oldptr), PACK(oldsize + nextsize, 1));
      PUT(FTRP(oldptr), PACK(oldsize + nextsize, 1));
      splice_together(succ_prev, succ_next, nextsize);
      return oldptr;
    }
  }

  newptr = mm_malloc(size);

  /* If realloc() fails the original block is left untouched  */
  if(!newptr) {
    return 0;
  }

  /* Copy the old data. */
  if(size < oldsize) oldsize = size;
  memcpy(newptr, oldptr, oldsize);

  /* Free the old block. */
  mm_free(oldptr);

  return newptr;
}

/*
 * calloc - Allocate and return array of nmemb elemnts of size bytes.
 *          Memory is set to zero.
 */
void *calloc (size_t nmemb, size_t size) {
  size_t bytes = nmemb * size;
  void *newptr;

  newptr = malloc(bytes);
  memset(newptr, 0, bytes);

  return newptr;
}

/*
 * mm_checkheap - Checks the heap for consistency.
 *                Prints extra information if verbose is requested.
 */
void mm_checkheap(int verbose) {
  char *bp = heap_listp;

  if(verbose)
    printf("Heap (%p):\n", heap_listp);

  /* Check prologue block */
  if((GET_SIZE(HDRP(heap_listp)) != (QSIZE)) || !GET_ALLOC(HDRP(heap_listp))) {
    printf("Bad prologue header\n");
  }
  checkblock(heap_listp, verbose);

  int heap_free_count = 0;
  int seg_free_count = 0;

  /* Check each block on heap count number of free blocks */
  for(bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
    if(verbose)
      printblock(bp);
    checkblock(bp, verbose);
    if(!(GET_ALLOC(HDRP(bp))))
       heap_free_count++;
    if(!(GET_ALLOC(HDRP(bp))) && !(GET_ALLOC(HDRP(NEXT_BLKP(bp)))))
      printf("Freed blocks not properly coalesced\n");
  }

  /* Check epilogue block */
  if(verbose)
    printblock(bp);
  if((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
    printf("Error: bad epilogue header\n");

  char *b_ptr = seg_listp;
  unsigned long max_addr = (unsigned long)(last_segp);

  /* Loop through each segregated list:
     1. check for cycles
     2. count number of free blocks
     3. check all blocks are free
     4. check consistency of next/previous pointers
     5. check all pointers are in heap
     6. check each block is in current seg list
  */
  for( ; (unsigned long)(b_ptr) <= max_addr; b_ptr += DSIZE) {
    bp = GET_ADDRESS(b_ptr);
    if(hascycle(bp)) {
      if(verbose)
        printblock(bp);
      printf("Error: bucket %zu has a cycle\n",
             bucket(GET_SIZE(HDRP(bp)))/WSIZE);
    }
    for( ; bp != NULL; bp = GET_ADDRESS(bp)) {
      if(verbose)
        printblock(bp);

      seg_free_count++;

      if(GET_ALLOC(HDRP(bp)))
        printf("Error: %p in seglist is not free\n", bp);

      char *next_free = GET_ADDRESS(bp);
      if(next_free != NULL && PREV_FREEBLKP(next_free) != bp)
        printf("Error: next/prev pointers of %p are not consistent\n", bp);

      if(!in_heap(bp))
        printf("Error: seglist pointer %p in heap\n", bp);

      size_t asize = GET_SIZE(HDRP(bp));
      if((unsigned long)(b_ptr) != (unsigned long)(seg_listp + bucket(asize)))
        printf("Error: %p not in correct bucket size range\n", bp);
    }
  }

  /* Check that the total free blocks on heap is consistent with
     total blocks in the seg lists
  */
  if(heap_free_count != seg_free_count)
    printf("Error: number of free blocks is inconsistent\n");
}

/*
 * The remaining routines are internal helper routines.
 */

/*
 * splice_together - Given 2 block pointers in the same size class as size,
 *                   splice them together in the appropriate seg list.
 */
static void splice_together(void *bp_prev, void *bp_next, size_t size) {
  char *bucket_ptr = seg_listp + bucket(size);

  if(bp_prev == NULL && bp_next == NULL) {
    PUT_ADDRESS(bucket_ptr, NULL);
  }
  else if(bp_prev == NULL && bp_next != NULL) {
    PUT_ADDRESS(bucket_ptr, bp_next);
    PUT_ADDRESS(PREV_PTR(bp_next), NULL);
  }
  else if(bp_prev != NULL && bp_next == NULL) {
    PUT_ADDRESS(NEXT_PTR(bp_prev), NULL);
  }
  else {
    PUT_ADDRESS(NEXT_PTR(bp_prev), bp_next);
    PUT_ADDRESS(PREV_PTR(bp_next), bp_prev);
  }
}

/*
 * extend_heap - Extend the heap by the given number of words.
 */
static void *extend_heap(size_t words)
{
  char *bp;
  size_t size;

  /* Allocate an even number of words to maintain alignment */
  size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
  if((long)(bp = mem_sbrk(size)) == -1)
    return NULL;

  /* Initialize free block header/footer and the epilogue header */
  PUT(HDRP(bp), PACK(size, 0)); /* Free block header */
  PUT(FTRP(bp), PACK(size, 0)); /* Free block footer */
  PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

  /* Coalesce if the previous block was free */
  return coalesce(bp);
}

/*
 * coalesce - Coalesce the given block with adjacent blocks if necessary,
 *            then insert the coalesced block at the beginning of the
 *            appropriate seg list.
 */
static void *coalesce(void *bp)
{
  size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t size = GET_SIZE(HDRP(bp));

  if(prev_alloc && next_alloc) { /* Case 1 */
    /* Insert coalesced block at root */
    char *bucket_ptr = seg_listp + bucket(size);
    char *seg_bucket = GET_ADDRESS(bucket_ptr);
    PUT_ADDRESS(NEXT_PTR(bp), seg_bucket);
    PUT_ADDRESS(PREV_PTR(bp), NULL);
    if(seg_bucket != NULL)
      PUT_ADDRESS(PREV_PTR(seg_bucket), bp);
    PUT_ADDRESS(bucket_ptr, bp);
    return bp;
  }

  else if(prev_alloc && !next_alloc) { /* Case 2 */
    /* Splice out successor block */
    char *next_adjblock = NEXT_BLKP(bp);
    char *succ_next = NEXT_FREEBLKP(next_adjblock);
    char *succ_prev = PREV_FREEBLKP(next_adjblock);
    splice_together(succ_prev, succ_next, GET_SIZE(HDRP(next_adjblock)));

    /* Coalesce current and successor block */
    size += GET_SIZE(HDRP(next_adjblock));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    /* Insert coalesced block at root */
    char *bucket_ptr = seg_listp + bucket(size);
    char *seg_bucket = GET_ADDRESS(bucket_ptr);
    PUT_ADDRESS(NEXT_PTR(bp), seg_bucket);
    PUT_ADDRESS(PREV_PTR(bp), NULL);
    if(seg_bucket != NULL)
      PUT_ADDRESS(PREV_PTR(seg_bucket), bp);
    PUT_ADDRESS(bucket_ptr, bp);
    return bp;
  }

  else if(!prev_alloc && next_alloc) { /* Case 3 */
    /* Splice out predecessor block */
    char *prev_adjblock = PREV_BLKP(bp);
    char *pred_next = NEXT_FREEBLKP(prev_adjblock);
    char *pred_prev = PREV_FREEBLKP(prev_adjblock);
    splice_together(pred_prev, pred_next, GET_SIZE(HDRP(prev_adjblock)));

    /* Coalesce current and predecessor block */
    size += GET_SIZE(HDRP(prev_adjblock));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(prev_adjblock), PACK(size, 0));
    bp = prev_adjblock;

    /* Insert coalesced block at root */
    char *bucket_ptr = seg_listp + bucket(size);
    char *seg_bucket = GET_ADDRESS(bucket_ptr);
    PUT_ADDRESS(NEXT_PTR(bp), seg_bucket);
    PUT_ADDRESS(PREV_PTR(bp), NULL);
    if(seg_bucket != NULL)
      PUT_ADDRESS(PREV_PTR(seg_bucket), bp);
    PUT_ADDRESS(bucket_ptr, bp);
    return bp;
  }

  else { /* Case 4 */
    /* Splice out successor and predecessor blocks */
    char *next_adjblock = NEXT_BLKP(bp);
    char *succ_next = NEXT_FREEBLKP(next_adjblock);
    char *succ_prev = PREV_FREEBLKP(next_adjblock);
    splice_together(succ_prev, succ_next, GET_SIZE(HDRP(next_adjblock)));

    char *prev_adjblock = PREV_BLKP(bp);
    char *pred_next = NEXT_FREEBLKP(prev_adjblock);
    char *pred_prev = PREV_FREEBLKP(prev_adjblock);
    splice_together(pred_prev, pred_next, GET_SIZE(HDRP(prev_adjblock)));

    /*Coalesce all 3 memory blocks */
    size += (GET_SIZE(HDRP(prev_adjblock)) + GET_SIZE(FTRP(next_adjblock)));
    PUT(HDRP(prev_adjblock), PACK(size, 0));
    PUT(FTRP(next_adjblock), PACK(size, 0));
    bp = prev_adjblock;

    /* Insert coalesced block at root */
    char *bucket_ptr = seg_listp + bucket(size);
    char *seg_bucket = GET_ADDRESS(bucket_ptr);
    PUT_ADDRESS(NEXT_PTR(bp), seg_bucket);
    PUT_ADDRESS(PREV_PTR(bp), NULL);
    if(seg_bucket != NULL)
      PUT_ADDRESS(PREV_PTR(seg_bucket), bp);
    PUT_ADDRESS(bucket_ptr, bp);
    return bp;
  }
  return bp;
}

/*
 * place - Allocate a block of requested size at bp.
 *         Splits if remainder equals or exceeds minimum block size.
 */
static void place(void *bp, size_t asize) {
  size_t csize = GET_SIZE(HDRP(bp));
  char *next_free = NEXT_FREEBLKP(bp);
  char *prev_free = PREV_FREEBLKP(bp);
  if((csize - asize) >= (2 * QSIZE)) {
    PUT(HDRP(bp), PACK(asize, 1));
    PUT(FTRP(bp), PACK(asize, 1));
    bp = NEXT_BLKP(bp);

    PUT(HDRP(bp), PACK(csize - asize, 0));
    PUT(FTRP(bp), PACK(csize - asize, 0));
    splice_together(prev_free, next_free, csize);
    coalesce(bp);
  }
  else {
    PUT(HDRP(bp), PACK(csize, 1));
    PUT(FTRP(bp), PACK(csize, 1));
    splice_together(prev_free, next_free, csize);
  }
}

/*
 * find_fit - Finds the first best fit starting from the appropriate seg list,
 *            in increasing order of size class.  Uses the best fit out of
 *            first 10 fits. If no fit is found, returns NULL.
 */
static void *find_fit(size_t asize) {
  char *b_ptr = seg_listp + bucket(asize);
  unsigned long max_addr = (unsigned long)(last_segp);
  void *bp;
  /* Loop through each seglist in ascending size class order
     starting from appropriate size class
  */
  for(; (unsigned long)(b_ptr) <= max_addr; b_ptr += DSIZE) {
    void *result = 0;
    size_t smallest = (size_t)(-1);
    size_t count = 0;
    bp = GET_ADDRESS(b_ptr);
    for( ; bp != NULL && count < 10; bp = GET_ADDRESS(bp)) {
      if(asize <= GET_SIZE(HDRP(bp))) {
        if(result == NULL || GET_SIZE(HDRP(bp)) < smallest) {
          result = bp;
          smallest = GET_SIZE(HDRP(bp));
          if(smallest == asize)
            return result;
        }
        count++;
      }
    }
    if(result != 0)
      return result;
  }
  return NULL;
}

/*
 * printblock - Prints information of a given block.
 */
static void printblock(void *bp)
{
  size_t hsize, halloc, fsize, falloc;

  hsize = GET_SIZE(HDRP(bp));
  halloc = GET_ALLOC(HDRP(bp));
  fsize = GET_SIZE(FTRP(bp));
  falloc = GET_ALLOC(FTRP(bp));

  if(hsize == 0) {
    printf("%p: EOL\n", bp);
    return;
  }

  /*  printf("%p: header: [%p:%c] footer: [%p:%c]\n", bp,
      hsize, (halloc ? 'a' : 'f'),
      fsize, (falloc ? 'a' : 'f')); */
}

/*
 * checkblock - Check if a given block is:
 *              1. aligned correctly
 *              2. in the heap
 *              3. has matching header and footers
 *              4. at least the minimum size
 */
static void checkblock(void *bp, int verbose)
{
  if(!aligned(bp)) {
    if(verbose)
      printblock(bp);
    printf("Error: %p is not aligned correctly\n", bp);
  }
  if(!in_heap(bp)) {
    if(verbose)
      printblock(bp);
    printf("Error: %p is not in heap\n", bp);
  }
  if(GET(HDRP(bp)) != GET(FTRP(bp))) {
    if(verbose)
      printblock(bp);
    printf("Error: %p header does not match footer\n", bp);
  }
  if((long)(bp) != (long)(heap_listp) && GET_SIZE(HDRP(bp)) < (2 * QSIZE)) {
    if(verbose)
      printblock(bp);
    printf("Error: %p is below minimum size\n", bp);
  }

}

/*
 * in_heap - Return whether the pointer is in the heap.
 */
static int in_heap(const void *p) {
  return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * aligned - Return whether the pointer is aligned correctly.
 */
static int aligned(const void *p) {
  return (size_t)ALIGN(p) == (size_t)p;
}

/*
 * hascycle - Return whether the free list has a cycle.
 */
static int hascycle(void *bp) {
  void *tortoise = bp;
  void *hare = bp;
  while(tortoise != NULL && hare != NULL) {
    tortoise = NEXT_FREEBLKP(tortoise);
    hare = NEXT_FREEBLKP(hare);
    if(hare == NULL)
      return 0;
    else
      hare = NEXT_FREEBLKP(hare);

    if(tortoise == hare)
      return 1;
  }
  return 0;
}

/*
 * bucket - Computes bucket offset from seg_listp with given block size.
 */
static inline size_t bucket(size_t num) {
  num = num/(2 * QSIZE);
  if(num >= LASTCLASS) {
    return (SEGS - 1) * DSIZE;
  }
  int log = 0;
  num /= RATIO;
  while(num != 0) {
    log++;
    num /= RATIO;
  }
  return log * DSIZE;
}
