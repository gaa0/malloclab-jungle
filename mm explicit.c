/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

// If NEXT_FIT defined use next fit search, else use first fit search
#define NEXT_FITx
#define BEST_FITx
#define EXPLICIT

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "jungle",
    /* First member's full name */
    "king",
    /* First member's email address */
    "fighting@fighting.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
// #define ALIGNMENT 8

/* Basic constants and macros */
#define WSIZE 4  // Word and header/footer size (bytes)
#define DSIZE 8  // Double word size (bytes)
#define CHUNKSIZE (1<<12)  // Extend heap by this amount (bytes)
#define MINIMUM 24  // 최소 블록 크기

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

// 가용블록 리스트의 이전 포인터와 다음 포인터
#define PREV_FLP(bp) (*((char **)(bp)))
#define NEXT_FLP(bp) (*((char **)(bp) + 1))  // 1의 의미: sizeof(int) * 1 = 4

/* rounds up to the nearest multiple of ALIGNMENT */
// #define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
// #define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

static char *heap_listp;
static char *free_listp;  // 가용블록 리스트의 시작점을 가리키는 포인터
#ifdef NEXT_FIT
static char *rover;  // Next fit rover
#endif

static void *extend_heap(size_t);
static void *coalesce(void *);
static void *find_fit(size_t);
static void place(void *, size_t);
static void add_free(void *);
static void del_free(void *);

/* 
 * mm_init - initialize the malloc package.

 * 초기 힙 상태
 *   padding   hdr    pred   succ   ftr  epilogue
 * +---------+------+------+------+------+-----+
 * | padding | 16/1 | NULL | NULL | 16/1 | 0/1 |
 * +---------+------+------+------+------+-----+
 */
int mm_init(void)
{
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(6 * WSIZE)) == (void *) - 1)  // explicit - 최소 블록 크기 커짐
        return -1;
    PUT(heap_listp, 0);  // Alignment padding
    PUT(heap_listp + (1 * WSIZE), PACK(2 * DSIZE, 1));  // Prologue header
    PUT(heap_listp + (2 * WSIZE), NULL);  // predecessor
    PUT(heap_listp + (3 * WSIZE), NULL);  // successor
    PUT(heap_listp + (4 * WSIZE), PACK(2 * DSIZE, 1));  // Prologue footer
    PUT(heap_listp + (5 * WSIZE), PACK(0, 1));  // Epilogue header
    // heap_listp += (2 * WSIZE);
    free_listp = heap_listp + DSIZE;  // 가용블록 리스트의 포인터 초기화
    
    #ifdef NEXT_FIT
    rover = heap_listp;
    #endif

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;

    if (size < MINIMUM)
        size = MINIMUM;

    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epliogue header */
    PUT(HDRP(bp), PACK(size, 0));  // Free block header
    PUT(FTRP(bp), PACK(size, 0));  // Free block footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));  // New epilogue header

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;  // Adjusted block size
    size_t extendsize;  // Amount to extend heap if no fit
    char *bp;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;
    
    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= MINIMUM - DSIZE)
        asize = MINIMUM;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory ans place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    // last_bp = bp;
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && !next_alloc)
    {  // Case 2
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        del_free(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    else if (!prev_alloc && next_alloc)
    {  // Case 3
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        del_free(PREV_BLKP(bp));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else if (!prev_alloc && !next_alloc)
    {  // Case 4
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        del_free(PREV_BLKP(bp));
        del_free(NEXT_BLKP(bp));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    add_free(bp);
    #ifdef NEXT_FIT
    if ((rover > (char *)bp) && (rover < NEXT_BLKP(bp)))
        rover = bp;
    #endif
    // last_bp = bp;
    return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    // copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

static void *find_fit(size_t asize)
{
    #ifdef NEXT_FIT
    char *oldrover = rover;

    // Search from the rover to the end of list
    for (; GET_SIZE(HDRP(rover)) > 0; rover = NEXT_BLKP(rover)) {
        if (!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover))))
            return rover;
    }
    // search from start of list to old rover
    for (rover = heap_listp; rover < oldrover; rover = NEXT_BLKP(rover)) {
        if (!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover))))
            return rover;
    }
    #elif defined(BEST_FIT)
    void *bp;
    void *best = NULL;
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize < GET_SIZE(HDRP(bp))) && (best == NULL || GET_SIZE(HDRP(bp)) < GET_SIZE(HDRP(best)))) {
            best = bp;
            if (asize == GET_SIZE(HDRP(bp))) {
                return best;
            }
        }
    }
    return best;
    #elif defined(EXPLICIT)
    void *bp = free_listp;
    while (!GET_ALLOC(HDRP(bp))) {
        if (asize <= GET_SIZE(HDRP(bp))) {
            return bp;
        }
        bp = NEXT_FLP(bp);
    }
    return NULL;
    #else

    // First-fit search
    void *bp;
    
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            return bp;
        }
    }
    
    #endif
    return NULL;  // No fit
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    
    del_free(bp);

    // 크기 차이가 24바이트 이상이면 블록 할당 후 남는 부분을 분할하여 가용블록 리스트에 추가
    if ((csize - asize) >= MINIMUM) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        coalesce(bp);
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

static void add_free(void *bp) {
    NEXT_FLP(bp) = free_listp;  // 현재 bp의 succ이 가용블록 리스트의 처음을 가리키도록
    PREV_FLP(bp) = NULL;  // 현재 bp의 pred가 NULL이 되도록
    PREV_FLP(free_listp) = bp;  // 현재 free_listp의 pred가 현재 bp를 가리키도록
    free_listp = bp;  // 가용블록 리스트의 처음을 bp로 변경
}

static void del_free(void *bp) {
    if (bp == free_listp) {
        PREV_FLP(NEXT_FLP(bp)) = PREV_FLP(bp);
        free_listp = NEXT_FLP(bp);
        return;
    }
    NEXT_FLP(PREV_FLP(bp)) = NEXT_FLP(bp);
    PREV_FLP(NEXT_FLP(bp)) = PREV_FLP(bp);
}



