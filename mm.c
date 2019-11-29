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
#define BITMASK 65534

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))


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
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{   
    printf("===== Now mallocing =====\n");
    printf("Malloc called with size %d\n", size);
    // The space required + two aligned sizes for header and footer
    int newsize = ALIGN(size);
    int sizewheaders = newsize + 2 * SIZE_T_SIZE;

    printf("New size without headers = %d\n", newsize);
    printf("New size with headers = %d\n", sizewheaders);

    // Implement best-fit free checking here




    printf("Allocating new memory region\n");
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

    void *temp = p;

    printf("--- Header ---\nsize: %d\n--- Header ---\n", *(size_t*)temp);

    for (int i = 0; i < newsize; i++)
    {
      temp = (unsigned char*)p + SIZE_T_SIZE + i;
      printf("%d => %0d\n", i+1, *((unsigned char*)temp));
    }
    temp++;
    printf("--- Footer ---\nsize: %d\n--- Footer ---\n", *(size_t*)temp);

    return (void *)((char *)p + SIZE_T_SIZE);
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    // Get header and footer
    size_t *header = (size_t*)((char*)ptr - SIZE_T_SIZE);
    size_t *footer = (size_t*)((char*)ptr + *header);

    printf("===== Now freeing =====\n");
    printf("H: %d : F: %d\n", *header, *footer);

    // Set free flag in header
    // We store this in the bottom bit of the size
    // We can do this because the aligment ensures it is always 0.
    *header = *header | 1;
    *footer = *footer | 1;

    printf("H: %d : F: %d\n", *header, *footer);

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
        header = (size_t*)((char*)prev_foot - *prev_foot - SIZE_T_SIZE);

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

        footer = (size_t*)((char*)next_head + *next_head - SIZE_T_SIZE);

        *header = new_size;
        *footer = new_size;
    }

    // Set up the pointers in the old body to build the explicit free list

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














