/*
 * mm.c - malloc using segregated list
 * 
 * In this approach, 
 * Every block has a header and a footer 
 * in which header contains reallocation information, size, and allocation info
 * and footer contains size and allocation info.
 * Free list are tagged to the segregated list.
 * Therefore all free block contains pointer to the predecessor and successor.
 * The segregated list headers are organized by 2^k size.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

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
#define ALIGNMENT 8

/* Basic constants and macros */
#define WSIZE 4  // Word and header/footer size (bytes)
#define DSIZE 8  // Double word size (bytes)
#define INITCHUNKSIZE (1<<6)
#define CHUNKSIZE (1<<12)  // Extend heap by this amount (bytes)

#define LISTLIMIT 20
#define REALLOC_BUFFER (1<<7)

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define MIN(x, y) ((x) < (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val) | GET_TAG(p))
#define PUT_NOTAG(p, val) (*(unsigned int *)(p) = (val))

// Store predecessor or successor pointer for free blocks
#define SET_PTR(p, ptr) (*(unsigned int *)(p) = (unsigned int)(ptr))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define GET_TAG(p) (GET(p) & 0x2)
#define REMOVE_RATAG(p) (GET(p) &= ~0x2)
#define SET_RATAG(p)  (GET(p) |= 0x2)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE((char *)(bp) - WSIZE))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE))

#define PRED_PTR(ptr) ((char *)(ptr))
#define SUCC_PTR(ptr) ((char *)(ptr) + WSIZE)

// 가용블록 리스트의 이전 포인터와 다음 포인터
#define PRED(bp) (*(char **)(bp))
#define SUCC(ptr) (*(char **)(SUCC_PTR(ptr)))
// #define NEXT_FLP(bp) (*((char **)(bp) + 1))  // 1의 의미: sizeof(int) * 1 = 4

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
// #define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

void *segregated_free_lists[LISTLIMIT];

// static char *heap_listp;
// static char *free_listp;  // 가용블록 리스트의 시작점을 가리키는 포인터

static void *extend_heap(size_t);
static void *coalesce(void *);
static void *place(void *, size_t);
static void insert_node(void *, size_t);
static void delete_node(void *);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    int list;
    char *heap_start;  // Pointer to beginning of heap

    // Initialize segregated free lists
    for (list = 0; list < LISTLIMIT; list++) {
        segregated_free_lists[list] = NULL;
    }

    /* Allocate memory for the initial empty heap */
    if ((long)(heap_start = mem_sbrk(4 * WSIZE)) == -1)
        return -1;

    PUT_NOTAG(heap_start, 0);  // Alignment padding
    PUT_NOTAG(heap_start + (1 * WSIZE), PACK(DSIZE, 1));  // Prologue header
    PUT_NOTAG(heap_start + (2 * WSIZE), PACK(DSIZE, 1));  // Prologue footer
    PUT_NOTAG(heap_start + (3 * WSIZE), PACK(0, 1));  // Epilogue header

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(INITCHUNKSIZE) == NULL)
        return -1;
        
    return 0;
}

static void *extend_heap(size_t size)
{
    char *bp;
    size_t asize;

    asize = ALIGN(size);

    if ((bp = mem_sbrk(asize)) == (void *)-1)
        return NULL;

    /* Initialize free block header/footer and the epliogue header */
    PUT_NOTAG(HDRP(bp), PACK(asize, 0));  // Free block header
    PUT_NOTAG(FTRP(bp), PACK(asize, 0));  // Free block footer
    PUT_NOTAG(HDRP(NEXT_BLKP(bp)), PACK(0, 1));  // New epilogue header
    // insert_node(bp, asize);

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

static void insert_node(void *ptr, size_t size) {
    int list = 0;
    void *search_ptr = ptr;
    void *insert_ptr = NULL;

    // Select degregated list
    while ((list < LISTLIMIT - 1) && (size > 1)) {
        size >>= 1;
        list++;
    }

    // Keep size ascending order and search
    search_ptr = segregated_free_lists[list];
    while (search_ptr != NULL) {
        insert_ptr = search_ptr;  // 들어갈 자리의 이전 포인터
        search_ptr = PRED(search_ptr);  // 들어갈 자리의 다음 포인터
    }

    // Set predecessor and successor
    if (search_ptr != NULL) {
        if (insert_ptr != NULL) {
            SET_PTR(PRED_PTR(ptr), search_ptr);
            SET_PTR(SUCC_PTR(search_ptr), ptr);
            SET_PTR(SUCC_PTR(ptr), insert_ptr);
            SET_PTR(PRED_PTR(insert_ptr), ptr);
        } else {
            SET_PTR(PRED_PTR(ptr), search_ptr);
            SET_PTR(SUCC_PTR(search_ptr), ptr);
            SET_PTR(SUCC_PTR(ptr), NULL);
            segregated_free_lists[list] = ptr;
        }
    } else {
        if (insert_ptr != NULL) {
            SET_PTR(PRED_PTR(ptr), NULL);
            SET_PTR(SUCC_PTR(ptr), insert_ptr);
            SET_PTR(PRED_PTR(insert_ptr), ptr);
        } else {
            SET_PTR(PRED_PTR(ptr), NULL);
            SET_PTR(SUCC_PTR(ptr), NULL);
            segregated_free_lists[list] = ptr;
        }
    }
    return;
}

static void delete_node(void *ptr) {
    int list = 0;
    size_t size = GET_SIZE(HDRP(ptr));

    // Select segregated list
    while ((list < LISTLIMIT - 1) && (size > 1)) {
        size >>= 1;
        list++;
    }

    if (PRED(ptr) != NULL) {
        if (SUCC(ptr) != NULL) {
            SET_PTR(SUCC_PTR(PRED(ptr)), SUCC(ptr));
            SET_PTR(PRED_PTR(SUCC(ptr)), PRED(ptr));
        } else {
            SET_PTR(SUCC_PTR(PRED(ptr)), NULL);
            segregated_free_lists[list] = PRED(ptr);
        }
    } else {
        if (SUCC(ptr) != NULL) {
            SET_PTR(PRED_PTR(SUCC(ptr)), NULL);
        } else {
            segregated_free_lists[list] = NULL;
        }
    }
    return;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;  // Adjusted block size
    size_t extendsize;  // Amount to extend heap if no fit
    void *bp = NULL;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;
    
    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = ALIGN(size + DSIZE);

    int list = 0;
    size_t searchsize = asize;
    /* Search for free block in segregated list */
    while (list < LISTLIMIT) {
        if ((list == LISTLIMIT - 1) || ((searchsize <= 1) && (segregated_free_lists[list] != NULL))) {
            bp = segregated_free_lists[list];
            // Ignore blocks that are too small or mared with the reallocation bit
            while ((bp != NULL) && ((asize > GET_SIZE(HDRP(bp))) || (GET_TAG(HDRP(bp))))) {
                bp = PRED(bp);
            }
            if (bp != NULL)
                break;
        }
        searchsize >>= 1;
        list++;
    }

    /* If free block is not found, extend the heap */
    if (bp == NULL) {
        extendsize = MAX(asize, CHUNKSIZE);

        if ((bp = extend_heap(extendsize)) == NULL)
            return NULL;
    }
    
    // Place and divice block
    bp = place(bp, asize);
    // last_bp = bp;
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    
    REMOVE_RATAG(HDRP(NEXT_BLKP(bp)));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    // insert_node(bp, size);
    coalesce(bp);

    return;
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    // Do not coalesce with previous block if the previous block is tagged with Reallocation tag
    if (GET_TAG(HDRP(PREV_BLKP(bp))))
        prev_alloc = 1;
    
    // if (prev_alloc && next_alloc) {
    //     return bp;
    // }

    if (prev_alloc && !next_alloc)
    {  // Case 2
        // delete_node(bp);
        delete_node(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    else if (!prev_alloc && next_alloc)
    {  // Case 3
        // delete_node(bp);
        delete_node(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else if (!prev_alloc && !next_alloc)
    {  // Case 4
        // delete_node(bp);
        delete_node(PREV_BLKP(bp));
        delete_node(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    // add_free(bp);
    insert_node(bp, size);
    // last_bp = bp;
    return bp;
}

/*
 * mm_realloc - Reallocate a block in place, extending the heap if necessary.
 *              The new block is padded with a buffer to guarantee that the
 *              next reallocation can be done without extending the heap,
 *              assuming that the block is expanded by a constant number of bytes
 *              per reallocation.
 *
 *              If the buffer is not large enough for the next reallocation, 
 *              mark the next block with the reallocation tag. Free blocks
 *              marked with this tag cannot be used for allocation or
 *              coalescing. The tag is cleared when the marked block is
 *              consumed by reallocation, when the heap is extended, or when
 *              the reallocated block is freed.
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *new_ptr = ptr;  // Pointer to be returned
    size_t new_size = size;  // Size of new block
    int remainder;  // Adequacy of block sizes
    int extendsize;  // Size of heap extension
    int block_buffer;  // Size of block buffer

    if (size == 0) {
        return NULL;
    }

    // Align block size
    if (new_size <= DSIZE) {
        new_size = 2 * DSIZE;
    } else {
        new_size = ALIGN(size + DSIZE);
    }

    // Add overhead requirments to block size
    new_size += REALLOC_BUFFER;

    // Calculate block buffer
    block_buffer = GET_SIZE(HDRP(ptr)) - new_size;

    // Alocate more space if overhead falls below the minimum
    if (block_buffer < 0) {
        // Check if next block is a free block or the epilogue block
        if (!GET_ALLOC(HDRP(NEXT_BLKP(ptr))) || !GET_SIZE(HDRP(NEXT_BLKP(ptr)))) {
            remainder = GET_SIZE(HDRP(ptr)) + GET_SIZE(HDRP(NEXT_BLKP(ptr))) - new_size;
            if (remainder < 0) {
                extendsize = MAX(-remainder, CHUNKSIZE);
                if (extend_heap(extendsize) == NULL)
                    return NULL;
                remainder += extendsize;
            }
            delete_node(NEXT_BLKP(ptr));

            // Do not split block
            PUT_NOTAG(HDRP(ptr), PACK(new_size + remainder, 1));
            PUT_NOTAG(FTRP(ptr), PACK(new_size + remainder, 1));
        } else {
            new_ptr = mm_malloc(new_size - DSIZE);
            memcpy(new_ptr, ptr, MIN(size, new_size));
            mm_free(ptr);
        }
        block_buffer = GET_SIZE(HDRP(new_ptr)) - new_size;
    }

    // Tag the next block if block overhead drops below twice the overhead
    if (block_buffer < 2 * REALLOC_BUFFER)
        SET_RATAG(HDRP(NEXT_BLKP(new_ptr)));
    
    return new_ptr;
}

static void *place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    size_t remainder = csize - asize;

    delete_node(bp);

    if (remainder <= DSIZE * 2) {
        // Do not split block
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }

    else if (asize >= 100) {
        // Split block
        PUT(HDRP(bp), PACK(remainder, 0));
        PUT(FTRP(bp), PACK(remainder, 0));
        PUT_NOTAG(HDRP(NEXT_BLKP(bp)), PACK(asize, 1));
        PUT_NOTAG(FTRP(NEXT_BLKP(bp)), PACK(asize, 1));
        insert_node(bp, remainder);
        return NEXT_BLKP(bp);
    }

    else {
        // Split block
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        PUT_NOTAG(HDRP(NEXT_BLKP(bp)), PACK(remainder, 0));
        PUT_NOTAG(FTRP(NEXT_BLKP(bp)), PACK(remainder, 0));
        insert_node(NEXT_BLKP(bp), remainder);
    }
    return bp;
}

