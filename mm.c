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

#define REGSIZE 4
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
// static void *extend_heap(size_t words);
static int mm_checker(void);
static int checkFreeInList(void);
static int checkOverlap(void);
static int checkCoalseceAndFree(void);
static int mm_valid_heap(void);

static void* alloc_new_block(size_t newsize);
static void* look_for_free_block(size_t newsize);
static void* alloc_free_block(void *best_ptr, size_t newsize);
static void* split_free_block(size_t *header, size_t newsize);
static void splice_list(void **prev_ptr, void **next_ptr);
static size_t* coalesce(size_t *header, size_t *footer);
static void FL_push_front(size_t *header);

static void check_inv_list();
static void printfreelist()
{
    void **node = mem_heap_lo();
    int index = 0;
    printf("%p ", node);
    while (*node != NULL)
    {
        node = *node;
        printf(" => %p", node);
        index++;
        if (index > 32)
            break;
    }

    // backwards
    node = (void*)((char*)node - 4);
    printf(" == %p", node);
    index = 0;
    while ((void*)node > mem_heap_lo())
    {
        node = *node;
        printf(" => %p", node);
        index++;
        if (index > 32)
            break;
    }

    printf("\n");
    check_inv_list();
}

static void check_inv_list()
{
    void **node = mem_heap_lo();
    int index = 0;
    node = *node;
    if (node == NULL) return;
    while (*node != NULL)
    {
        void **next = *node;
        void **next_prev = (void*)((char*)next - 4);
        void **back_prev = *next_prev;
        void **back_again = (void*)((char*)back_prev + 4);

        if (node != back_again)
            printf("ERROR IN REV CHAIN %p => %p : %p => %p : %p\n", node, next_prev, next, back_prev, back_again);

        node = *node;
        index++;
        if (index > 1024)
            break;
    }
}


/* 
 * mm_init - initialize the malloc package.
 * Initializes with a global root header,
 * serving as the starting point for an explicit free list.
 * By storing it on the heap, we don't have to use a global variable
 */
int mm_init(void)
{
    printf("Init called\n");
    // Should be done for us, but let us do it anyway
    mem_reset_brk();
    
    // Get enough space to store the root header
    // The root header will contain a pointer to start the explicit free list
    void **root = mem_sbrk(ALIGN(REGSIZE));

    // This will point to the next free block
    // And will be NULL if we don't have any
    *root = NULL;
    
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{   
    printf("malloc called : %d\n", size);
    // The space required + two aligned sizes for header and footer
    size_t newsize = ALIGN(size);

    // Ensure that we have enough space to store the list pointers when freed
    if (newsize < 8)
        newsize = 8;


    // Check every free block
    void *best_ptr = look_for_free_block(newsize);

    // If we found any suitable block, use it
    if (best_ptr != NULL)
    {
        return alloc_free_block(best_ptr, newsize);
    }

    // Get new heap resources for allocation
    return alloc_new_block(newsize);
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    printf("Free called : %p\n", ptr);

    // Get header and footer
    size_t *header = (size_t*)((char*)ptr - SIZE_T_SIZE);
    size_t *footer = (size_t*)((char*)ptr + (*header & BITMASK));

    if ((*header & 1) == 1)
        // This block is already free
        // We can corrupt the heap if the user calls this incorrectly, so we just do nothing
        return;

    // Set free flag in header
    // We store this in the bottom bit of the size
    // We can do this because the aligment ensures it is always 0.
    *header = *header | 1;
    *footer = *footer | 1;

    // Coalesce
    header = coalesce(header, footer);

    // Add ourselves to the top of the list
    FL_push_front(header);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    printf("Realloc called\n");
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


/*
 * ========================================================
 *                  Static Helper functions
 * ========================================================
 */

static void* alloc_new_block(size_t newsize)
{
    // Get the size required to also fit headers    
    size_t sizewheaders = newsize + 2 * SIZE_T_SIZE;

    // Get the new memory from sbrk
    void *p = mem_sbrk(sizewheaders);

    printf("Allocating new memory : %d\n", mem_heapsize());

    // Check if mm_sbrk is indicating failure
    if (p == (void *)-1)
	    return NULL;

    // Set the header
    *(size_t *)p = newsize;

    // Find the footer location and set the footer as well
    size_t *footer = (size_t*)((char*)p + newsize + SIZE_T_SIZE);
    *footer = newsize;

    // printf("New %p : %p\n", (char*)p + SIZE_T_SIZE, mem_heap_hi());

    // Return a pointer to the new memory area
    return (void *)((char *)p + SIZE_T_SIZE);
}

static void* look_for_free_block(size_t newsize)
{
    // Initialize variables
    size_t best_diff = __INT_MAX__;
    void *best_ptr = NULL;
    int index = 0;

    // Find the root ptr
    void **current = mem_heap_lo();

    // Skip moce to first item in list
    current = *current;

    // Look through the list
    while (current != NULL)
    {
        // DEBUG Check
        if ((*(size_t*)((char*)current - (SIZE_T_SIZE + 4)) & 1) == 0)
            printf("Non free block in free list\n");

        // Get the size of the current free block
        size_t this_size = (*(size_t*)((char*)current - (SIZE_T_SIZE + 4))) & BITMASK;

        printf("Current -> %p : %d\n", current, this_size);
        // printf("checking %p => %p\n", current, *current);
        
        // If it is large enough check if it is better than current best fit
        if (newsize <= this_size && (this_size - newsize) < best_diff)
        {
            // If it is, then it is our new best fit
            best_diff = this_size - newsize;
            best_ptr = (void*)((char*)current - 4);
        }

        // If there is an exact match, no point continuing the loop
        if (best_diff == 0)
            break;

        // Move along the list
        current = *current;

        // Limit the time spend in this loop for very long lists
        // Sacrifice some fragmentation to get better speed
        // Was also helpful during debugging, as corruption would sometimes cause loops in the free list
        index++;
        if (index > 1024)
            break;
    }

    return best_ptr;
}

static void* split_free_block(size_t *header, size_t newsize)
{   
    // Get size of the block we are splitting off
    // ie. the size of the original block - the size of the block we are allocating - space for two new header at the border
    size_t size_new = *header - newsize - (2 * SIZE_T_SIZE);

    // printf("Splitting block of size %d into blocks of size %d and %d\n", *header, newsize, size_new);

    // Find location of new footer
    size_t *footer = (size_t*)((char*)header + newsize + SIZE_T_SIZE);

    // Set header and footer to new size
    *header = newsize;
    *footer = newsize;

    // Get new_header and new_footer of the new free block that we are splitting off
    size_t *new_header = (size_t*)((char*)footer + SIZE_T_SIZE);
    size_t *new_footer = (size_t*)((char*)new_header + size_new + SIZE_T_SIZE);

    // printf("%p = %d\n", (char*)new_header+SIZE_T_SIZE+4, *new_header & 1);

    // Set them to the new size and set their free bit
    *new_header = size_new | 1;
    *new_footer = size_new | 1;

    // Add the new split off block to beginning of free list
    // printf("Split block. New blocks at %p and %p\n", (char*)best_ptr+4, (char*)new_header+SIZE_T_SIZE+4);
    FL_push_front(new_header);

    printf("Splitting\n");

    // Return pointer to the allocated memory area
    return (void*)((char*)header + SIZE_T_SIZE);
}

static void* alloc_free_block(void *best_ptr, size_t newsize)
{
    // Get the free list pointers, so we can do splicing
    void **prev_ptr = best_ptr;
    void **next_ptr = prev_ptr + 1;

    // Remove this block from the free list
    splice_list(prev_ptr, next_ptr);
    
    // Find header location and unset the free bit
    size_t *header = (size_t*)((char*)best_ptr - SIZE_T_SIZE);
    *header = (*header & BITMASK);

    if ((*header - newsize) > 32)
    {
        // If there is enough left over after this block to make another block perform a split
        return split_free_block(header, newsize);
    }

    // If we aren't doing splittng just unset the free bit in the footer
    size_t *footer = (size_t*)((char*)header + *header + SIZE_T_SIZE);
    *footer = (*header & BITMASK);

    printf("Using whole free block\n");
    return best_ptr;
}

/*
 * Splices the list, so that the current block is removed from the free list
 */
static void splice_list(void **prev_ptr, void** next_ptr)
{   
    // Get the block before current in free list
    void **block1_prev = *prev_ptr;
    // If we are at the root node, there is no block1_prev, account for this
    void **block1_next;
    if (block1_prev == mem_heap_lo())
        block1_next = block1_prev;
    else
        block1_next = block1_prev + 1;

    // The block after this in free list
    // next_ptr can point to NULL if this is the last block in the list; Then these won't be valid adresses
    void **block2_next = *next_ptr;
    void **block2_prev = block2_next - 1;

    // Point block 1 to block 2
    *block1_next = block2_next;

    printf("Setting block1 %p => block2 %p\n", block1_next, block2_next);

    // Only point backwards if block2 is not pointing to NULL
    if (*next_ptr != NULL)
        *block2_prev = block1_prev;

    printf("Just spliced %p : ", next_ptr);
    printfreelist();
}

static size_t* coalesce(size_t *header, size_t *footer)
{
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
        printf("Coalesce behind %p => %d\n", header, new_size);

        // We need to splice the free list for the block we just consumed
        // Pointer to previous's prev_ptr
        void **prev_ptr = (void*)((char*)header + SIZE_T_SIZE);
        // Pointer to nexts next_ptr
        void **next_ptr = prev_ptr + 1;

        // Remove this block from the free list
        splice_list(prev_ptr, next_ptr);

        // We then set header and footer to the new size
        // At this point the unused header and footer is still insize our new block.
        // But because malloc doesn't make promises about the state of the memory, this doesn't matter.
        *header = new_size;
        *footer = new_size;
    }

    // Now we check after the current block
    size_t *next_head = (size_t*)((char*)footer + SIZE_T_SIZE);
    
    // printf("CAhaed candidate %p = %d | %p\n", next_head, *next_head, mem_heap_hi());

    // We have no global footer so we need to use a call to mem in order to check if we are oob.
    if ((void*)next_head < mem_heap_hi() && (*next_head & 1) == 1)
    {
        // Coalesce, same as before
        size_t new_size = ((*header & BITMASK) + (*next_head & BITMASK) + 2 * SIZE_T_SIZE) | 1;

        footer = (size_t*)((char*)next_head + (*next_head & BITMASK) - SIZE_T_SIZE);
        printf("Coalesce ahead %p => %d\n", next_head, new_size);

        void **prev_ptr = (void*)((char*)next_head + SIZE_T_SIZE);
        // Pointer to nexts next_ptr
        void **next_ptr = prev_ptr + 1;

        // Remove this block from the free list
        splice_list(prev_ptr, next_ptr);

        *header = new_size;
        *footer = new_size;
    }

    return header;
}

static void FL_push_front(size_t *header)
{
    // Get the spot for our ptrs
    void **prev_ptr = (void*)((char*)header + SIZE_T_SIZE);
    void **next_ptr = prev_ptr + 1;

    // Get the root pointer
    void **root = mem_heap_lo();

    // Add this block to beginning of list.
    // We point to the previous first block
    *next_ptr = *root;
    // printf("next @ %p = %p\n", next_ptr, *next_ptr);
    *prev_ptr = root;
    // printf("prev @ %p = %p\n", prev_ptr, *prev_ptr);
    *root = next_ptr;
    // printf("root @ %p = %p\n", root, *root);

    // The next blocs prev_ptr should point to us
    // Unless are the last block, and our next_ptr is NULL
    if (*next_ptr != NULL)
    {
        void **other_prev = (void*)((char*)*next_ptr - 4);
        *other_prev = prev_ptr;
    }

    printf("Just pushed %p : ", next_ptr);
    printfreelist();
}









static int mm_checker(void)
{
    printf("Checking!\n");
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












