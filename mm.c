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

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "team N and T",
    /* First member's full name */
    "Nicolaj Filrup Rasmussen",
    /* First member's email address */
    "nicr@itu.dk",
    /* Second member's full name (leave blank if none) */
    "Thai Wang",
    /* Second member's email address (leave blank if none) */
    "twan@itu.dk"
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

#define REGSIZE 8
#define BITMASK ~1

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

/* Basic constants and macros */
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
#define WSIZE   4       /* Word and header/footer size (bytes) */
#define DSIZE   8       /* Double word size (bytes) */
#define CHUNKSIZE (1<<2) /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocted bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)          (*(unsigned int *)(p))
#define PUT(p, val)     (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)     (GET(p) & ~0x7)
#define GET_ALLOC(p)    (GET(p) & 0x1)
#define GET_ALIGN(p)    (GET(p) & 0x7)

/* Given block ptr bp, compute address of its header and footer */
#define HEADER(bp)        ((char *)(bp) - WSIZE)
#define FOOTER(bp)        ((char *)(bp) + GET_SIZE(HEADER(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char * )(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Global variables */
// TODO: We may not need these
static char *heap_listp = 0;  /* Pointer to first block */
char *list_head = 0; //list of free blocks
char *epilogue_block = 0; /* Pointer to epilogue block */
int free_count = 0; //# of free blocks 

/* Prototypes for helper methods */
static void *extend_heap(size_t words);
static int mm_checker(void);
static int checkFreeInList(void);
static int checkOverlap(void);
static int checkCoalseceAndFree(void);
static int mm_valid_heap(void);

/* 
 * mm_init - initialize the malloc package.
 * Initializes with a global root header,
 * serving as the starting point for an explicit free list.
 * By storing it on the heap, we don't have to use a global variable
 */
int mm_init(void)
{
    // Get enough space to store the root header
    // The root header will contain a pointer to start the explicit free list
    // And a zero size, to be consistent in coalescing checks
    // Slightly wasteful in memory, but we avoid having to do any special checks in free
    // 8 is hardcoded because we assume 32-bit
    void *root = mem_sbrk(ALIGN(REGSIZE));
    // This will point to the next free block
    // And will be NULL if we don't have any
    root = NULL;

    return 0;
 /* Create the initial empty heap */
    // if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
    //     return -1;
    // PUT(heap_listp, 0);                             /* Alignmennt padding */
    // PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));    /* Prologue hader */
    // PUT(heap_listp + (2*WSIZE), PACK(DSIZE,1));     /* Prologue footer */
    // PUT(heap_listp + (3*WSIZE), PACK(0, 1));        /* Epilogue header */
    // heap_listp += (2*WSIZE);
    // list_head = 0 ; /* Initialize global list of free blocks */
    // free_count = 0; /* Initialize free blocks count */
    // /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    // if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
    //     return -1;
    // return 0;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an evenn number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HEADER(bp), PACK(size, 0));       /* Free block header */
    PUT(FOOTER(bp), PACK(size, 0));       /* Free block footer */
    PUT(HEADER(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}


/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{   
    // printf("===== Now mallocing =====\n");
    // printf("Malloc called with size %d\n", size);
    // The space required + two aligned sizes for header and footer
    size_t newsize = ALIGN(size);

    // Ensure that we have enough space to store the list pointers when freed
    if (newsize < 8)
        newsize = 8;

    size_t sizewheaders = newsize + 2 * SIZE_T_SIZE;

    // printf("New size without headers = %d\n", newsize);
    // printf("New size with headers = %d\n", sizewheaders);

    // Best fit allocation
    size_t best_diff = __INT_MAX__;
    void *best_ptr = NULL;

    // Check every free block
    void **current = mem_heap_lo();
    // Skip root
    current = *current;
    while (current != NULL)
    {
        // Get the size of the current free block
        size_t this_size = (*(size_t*)((char*)current - (SIZE_T_SIZE + 4))) & BITMASK;
        
        // If it is large enough check if it is better than current best fit
        if (newsize < this_size && (this_size - newsize) < best_diff)
        {
            best_diff = this_size - newsize;
            best_ptr = (void*)((char*)current - 4);
        }
        current = *current;
    }

    // If we found any suitable block, use it
    if (best_ptr != NULL)
    {
        if (best_diff > 32)
        {
            // If there is enough left over after this block to make another block perform a split

        }

        // Splice the list
        // For an explaination see mm_free
        void **prev_ptr = best_ptr;
        void **next_ptr = prev_ptr + 1;

        void **block1_prev = *prev_ptr;
        void **block1_next;
        if (block1_prev == mem_heap_lo())
            block1_next = block1_prev;
        else
            block1_next = block1_prev + 1;

        void **block2_next = *next_ptr;
        void **block2_prev = *next_ptr - 1;
        
        *block1_next = block2_next;
        if (*next_ptr != NULL)
            *block2_prev = block1_prev;

        size_t *header = (size_t*)((char*)best_ptr - SIZE_T_SIZE);
        *header = (*header & BITMASK);
        size_t *footer = (size_t*)((char*)header + *header + SIZE_T_SIZE);
        *footer = (*header & BITMASK);

        return best_ptr;
    }

    // Get the new memory
    void *p = mem_sbrk(sizewheaders);

    // Check if mm_sbrk is indicating failure
    if (p == (void *)-1)
	    return NULL;

    // Header
    *(size_t *)p = newsize;

    // Footer - The char* cast ensures we are incrementing in bytes
    size_t *f = (size_t*)((char*)p + newsize + SIZE_T_SIZE);
    *f = newsize;

    return (void *)((char *)p + SIZE_T_SIZE);
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{// Get header and footer
    size_t *header = (size_t*)((char*)ptr - SIZE_T_SIZE);
    size_t *footer = (size_t*)((char*)ptr + *header);

    if ((*header & 1) == 1)
        // This block is already free
        return;

    // Set free flag in header
    // We store this in the bottom bit of the size
    // We can do this because the aligment ensures it is always 0.
    *header = *header | 1;
    *footer = *footer | 1;

    // Coalesce
    // Let us check before the current block
    size_t *prev_foot = (size_t*)((char*)header - SIZE_T_SIZE); 
    if ((void*)prev_foot > mem_heap_lo() && (*prev_foot & 1) == 1)
    {
        // free bit is set, let's do coalescing
        // Calculate new size
        // It will be our size + previous size + size of one header and one footer
        // We also need to remember to filter the free bit out
        // After we are done we reset the free bit
        size_t new_size = ((*header & BITMASK) + (*prev_foot & BITMASK) + 2 * SIZE_T_SIZE) | 1;

        // We then need to set header to the other blocks header
        header = (size_t*)((char*)prev_foot - ((*prev_foot & BITMASK) + SIZE_T_SIZE));

        // We need to splice the free list for the block we just consumed
        // Pointer to previous's prev_ptr
        void **prev_ptr = (void*)((char*)header + SIZE_T_SIZE);
        // Pointer to nexts next_ptr
        void **next_ptr = prev_ptr + 1;

        // Find the block before this
        void **block1_prev = *prev_ptr;
        // If we are at the root node, there is no prev_ptr, account for this
        void **block1_next;
        if (block1_prev == mem_heap_lo())
            block1_next = block1_prev;
        else
            block1_next = block1_prev + 1;

        // The block after this
        // next_ptr can point to 0; Then these won't be valid adresses
        void **block2_next = *next_ptr;
        void **block2_prev = block2_next - 1;

        // Point block 1 to block 2
        *block1_next = block2_next;
        // Only point backwards if block2 is a real block
        if (*next_ptr != NULL)
            *block2_prev = block1_prev;

        // We then set header and footer to the new size
        // At this point the unused header and footer is still insize our new block.
        // But because malloc doesn't make promises about the state of the memory, this doesn't matter.
        *header = new_size;
        *footer = new_size;
    }

    // Now we check after the current block
    size_t *next_head = (size_t*)((char*)footer + SIZE_T_SIZE);
    
    // We have no global footer so we need to use a call to mem in order to check if we are oob.
    if ((void*)next_head < mem_heap_hi() && (*next_head & 1) == 1)
    {
        // Coalesce, same as before
        size_t new_size = ((*header & BITMASK) + (*next_head & BITMASK) + 2 * SIZE_T_SIZE) | 1;

        footer = (size_t*)((char*)next_head + (*next_head & BITMASK) - SIZE_T_SIZE);

        void **prev_ptr = (void*)((char*)next_head + SIZE_T_SIZE);
        // Pointer to nexts next_ptr
        void **next_ptr = prev_ptr + 1;

        void **block1_prev = *prev_ptr;
        void **block1_next;
        if (block1_prev == mem_heap_lo())
            block1_next = block1_prev;
        else
            block1_next = block1_prev + 1;

        void **block2_next = *next_ptr;
        void **block2_prev = *next_ptr - 1;

        *block1_next = block2_next;
        
        if (*next_ptr != NULL)
            *block2_prev = block1_prev;

        *header = new_size;
        *footer = new_size;
    }

    // Add ourselves to the top of the list
    // Get the spot for our ptrs
    void **prev_ptr = (void*)((char*)header + SIZE_T_SIZE);
    void **next_ptr = prev_ptr + 1;

    void **root = mem_heap_lo();

    *next_ptr = *root;
    *prev_ptr = root;
    *root = next_ptr;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

static int mm_checker(void)
{
    if (checkCoalseceAndFree() == 0){
        return 0;
    }
    if (checkFreeInList() == 0){
        return 0;
    }
    if (checkOverlap() == 0){
        return 0;
    }
    if (mm_valid_heap() == 0){
        return 0;
    }
    return 1;
}

static int mm_valid_heap(void){
    char *heap_check;
    for (heap_check = NEXT_BLKP(heap_listp); heap_check < epilogue_block; heap_check = NEXT_BLKP(heap_check)) {
        if((HEADER(heap_check) < HEADER(NEXT_BLKP(heap_listp))) || ((char *)GET(HEADER(heap_check)) > epilogue_block) ||  (GET_ALIGN(HEADER(heap_check)) != 0)) {
            printf("Error: current block points to an invalid heap address: %p\n", heap_check);
            return 0;
        }
    }
    return 1;
}

static int checkCoalseceAndFree(void){
    char*  current = list_head;
    int i;
    for (i = 0; i < free_count; i++){
        if (GET_ALLOC(HEADER(current)) || GET_ALLOC(FOOTER(current))) {     /* if either the header or the footer are marked allocated */
            return 0;
        }
        if (NEXT_BLKP(current) !=0 && !GET_ALLOC(HEADER(NEXT_BLKP(current)))) {     /* if either the header or the footer are marked allocated */
            return 0;   /* If it has a next and is free */
        }
        if (PREV_BLKP(current+SIZE_T_SIZE) !=0 && !GET_ALLOC(HEADER(PREV_BLKP(current)))) {     /* if either the header or the footer are marked allocated */
            return 0;   /* If it has a previous and is free */
        }
        current = (char*)GET(current+SIZE_T_SIZE);
    }
    return 1;
}

static int checkOverlap(void){
    return 1;
}

static int checkFreeInList(void){
    return 1;
}












