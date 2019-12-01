/*
 * mm.c - Explicit free list malloc with best fit allocation
 * 
 * This implementation uses an explicit free list stored in pointers within the body of free blocks.
 * When allocating the free list is searched using best fit, limited by a maximum search depth of 1024.
 * 
 * This way of allocation leads to less fragmentation but takes longer.
 * This balances nicely with the explicit free list, which requires a larger minimum block size, but searches very fast,
 * especially in mostly full scenarios.
 * 
 * Coalesce and Split are written to housekeep the pointers in the free list.
 * The list is managed using Last In First Out or LIFO.
 * 
 * Studies suggests that this leads to slightly more fragmentation then address ordered, but is much
 * more trivial to implement.
 * 
 * The implementation used both headers and footers, consisting of a size_t size, with a free flag stored in the least significant bit.
 * This makes coalescing easy.
 * 
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

/* Size of a register (eip specifically), in this case 32-bit */
#define REGSIZE 4
/* A bitmask for filtering out the free bit (stored in the least significant bit) */
#define BITMASK ~1

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

/* Basic constants and macros */
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Prototypes for helper methods related to mm_check*/
static int mm_check(void);
static int checkFreeInList(void);
static int checkOverlap(void);
static int checkCoalseceAndFree(void);
static int mm_valid_heap(void);
static int check_inv_list(void);

/* Prototypes for helper methods related to core operations */
static void* alloc_new_block(size_t newsize);
static void* look_for_free_block(size_t newsize);
static void* alloc_free_block(void *best_ptr, size_t newsize);
static void* split_free_block(size_t *header, size_t newsize);
static void splice_list(void **prev_ptr, void **next_ptr);
static size_t* coalesce(size_t *header, size_t *footer);
static void FL_push_front(size_t *header);





/* 
 * mm_init - initialize the malloc package.
 * Initializes with a global root header,
 * serving as the starting point for an explicit free list.
 * By storing it on the heap, we don't have to use a global variable
 */
int mm_init(void)
{
    // printf("Init called\n");
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
 * mm_malloc - Allocates memory by attempting to find suitable free blocks and falling back to commisioning from sbrk.
 * 
 * (*) Attempts to find a free block using best fit.
 * 
 * (*) If a block is found it is split if required and a pointer is returned.
 * 
 * (*) If a suitable block is not found a block is requested from mem_sbrk.
 * 
 */
void *mm_malloc(size_t size)
{   
    // printf("malloc called : %d\n", size);
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
 * mm_free - Freeing a block sets the free bit in header and footer, attempts to coalesce and adds block to the free list.
 * 
 * (*) Set the free bit in the header and footer
 * 
 * (*) Checks if adjacent blocks are free, if so coalesces
 * 
 * (*) Adds to beginning of free list (as per LIFO standard)
 * 
 */
void mm_free(void *ptr)
{
    // printf("Free called : %p\n", ptr);

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
 * mm_realloc - Split into 4 distinct behaviours
 * 
 * (1) - As malloc
 *      If ptr is NULL, mm_realloc will simply call mm_malloc and pass the result along.
 *      Required operation is identical, so no point in reinventing the wheel
 * 
 * (2) - As free
 *      If size is 0, we call mm_free on ptr. Same rationale as (1).
 * 
 * (3) - Shrinking
 *      If the desired size is smaller than the current size, the block can be shrunk in place.
 *      If the difference is larger than 32 (larger enough for header, footer and prev, next ptrs) a free block will be split off.
 *      If not, we do nothing and simply return the ptr unchanged.
 * 
 * (4) - Reallocating
 *      We allocate a new block with mm_malloc and copy the content.
 *      The old block is then freed.
 *      An optimization here would be to do coalescing with sorrounding free blocks.
 *      Coalescing forwards would in this case save the memcpy. And it would lead to less fragmentation.
 *      THIS IS NOT CURRENTLY IMPLEMENTED!
 * 
 */
void *mm_realloc(void *ptr, size_t size)
{
    /*
     * -----------------------------------------------------------------------
     * | Behaviour 1 (As malloc): Check is ptr is NULL then just call malloc |
     * -----------------------------------------------------------------------
     */
    if (ptr == NULL)
        return mm_malloc(size);

    /*
     * ------------------------------------------------------------
     * | Behaviour 2 (As free): If size is 0, than just free ptr. |
     * ------------------------------------------------------------
     */

    if (size == 0)
    {
        mm_free(ptr);
        return NULL;
    }

    /*
     * ----------------------------------------------------------------------------------------------------
     * | Behaviour 3 (Shrinking): If the new size is smaller than shrink the block in place. Maybe split. |
     * ----------------------------------------------------------------------------------------------------
     */

    // Find the header of the current block
    size_t* header = (size_t*)((char*)ptr - SIZE_T_SIZE);

    // Get the current size of the block
    size_t current_size = *header;

    // If desired size is smaller than current size, shrink in place
    if (current_size > size)
    {
        // If size so much smaller that we can split a free block off, do this.
        if ((current_size - ALIGN(size)) > 32)
        {
            // Perform a split
            // split_free_block shrinks the block and gives us a ptr back we can return directly
            return split_free_block(header, ALIGN(size));
        }
        
        // If the reduction is too small to split off, we must simply live with the fragmentation and return the block unchanged.
        return ptr;
    }

    /*
     * --------------------------------------------------------------------------
     * | Behaviour 4 (Reallocation): Allocate a new block and move the content. |
     * --------------------------------------------------------------------------
     */
    
    // Get a new block of memory
    void* newptr = mm_malloc(size);

    // Guard against an error in malloc
    if (newptr == NULL)
        return NULL;

    // If we have come this far, the new block must be at least the current size, and so we can copy directly
    memcpy(newptr, ptr, current_size);

    // The old block can now be freed
    mm_free(ptr);

    // And the ptr to the new are is returned
    return newptr;
}


/*
 * ========================================================
 *                  Static Helper functions
 * ========================================================
 */

/*
 * alloc_new_block - Allocates a new block of size newsize, and sets the header and footer.
 */
static void* alloc_new_block(size_t newsize)
{
    // Get the size required to also fit headers    
    size_t sizewheaders = newsize + 2 * SIZE_T_SIZE;

    // Get the new memory from sbrk
    void *p = mem_sbrk(sizewheaders);

    // Check if mm_sbrk is indicating failure
    if (p == (void *)-1)
	    return NULL;

    // Set the header
    *(size_t *)p = newsize;

    // Find the footer location and set the footer as well
    size_t *footer = (size_t*)((char*)p + newsize + SIZE_T_SIZE);
    *footer = newsize;

    // Return a pointer to the new memory area
    return (void *)((char *)p + SIZE_T_SIZE);
}

/*
 * look_for_free_block - Searches the free list in search of a compatible block.
 * 
 * It will try to find the best matching block to the gicen newsize.
 * It has a maximum search depth of 1024 after which it will return a best guess.
 * If it finds no suitable block it return (void*)NULL.
 * 
 */
static void* look_for_free_block(size_t newsize)
{
    // Initialize variables
    size_t best_diff = __INT_MAX__;
    void *best_ptr = NULL;
    int index = 0;

    // Find the root ptr
    void **current = mem_heap_lo();

    // Skip once to first item in list
    current = *current;

    // Look through the list
    while (current != NULL)
    {
        // Get the size of the current free block
        size_t this_size = (*(size_t*)((char*)current - (SIZE_T_SIZE + 4))) & BITMASK;

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
        index++;
        if (index > 1024)
            break;
    }

    return best_ptr;
}

/*
 * split_free_block - Given a pointer to a header and a required size a split is performed to leave the rest of the block free.
 * 
 * This functions does not ensure that the free memory area is larger than the minimum requirement, so this needs to be checked elsewhere.
 * If the block passed is smaller than newsize, behaviour is undefined.
 * 
 * The function also does not remove the block from the free list, so this also has to be done outside if required.
 * It does however add the new free block to the free list.
 * 
 * It returns a void* to the new memory area, that can be returned directly to users.
 * 
 */
static void* split_free_block(size_t *header, size_t newsize)
{   
    // Get size of the block we are splitting off
    // ie. the size of the original block - the size of the block we are allocating - space for two new header at the border
    size_t size_new = *header - newsize - (2 * SIZE_T_SIZE);

    // Find location of new footer
    size_t *footer = (size_t*)((char*)header + newsize + SIZE_T_SIZE);

    // Set header and footer to new size
    *header = newsize;
    *footer = newsize;

    // Get new_header and new_footer of the new free block that we are splitting off
    size_t *new_header = (size_t*)((char*)footer + SIZE_T_SIZE);
    size_t *new_footer = (size_t*)((char*)new_header + size_new + SIZE_T_SIZE);

    // Set them to the new size and set their free bit
    *new_header = size_new | 1;
    *new_footer = size_new | 1;

    // Add the new split off block to beginning of free list
    FL_push_front(new_header);

    // Return pointer to the allocated memory area
    return (void*)((char*)header + SIZE_T_SIZE);
}

/*
 * alloc_free_block - Allocates a free block, and splits if required.
 * 
 * best_ptr passed to the function most be a valid pointer to a free block at leat newsize in length.
 * 
 * This function will:
 * 
 * (*) Remove the free block from the free list.
 * 
 * (*) Unset the free bit of the header and footer.
 * 
 * (*) Calculate whether a split will result in a valid free block and perform if possible.
 * 
 * (*) Return a valid malloc poiner to the new memory area.
 * 
 */
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

    // Check if there is enough excess to split a free block off
    if ((*header - newsize) > 32)
    {
        // If there is enough left over after this block to make another block perform a split
        return split_free_block(header, newsize);
    }

    // If we aren't doing splittng just unset the free bit in the footer
    size_t *footer = (size_t*)((char*)header + *header + SIZE_T_SIZE);
    *footer = (*header & BITMASK);

    // Return a pointer to the new allocated block
    return best_ptr;
}

/*
 * Splices the list, so that the current block is removed from the free list
 * 
 * prev_ptr and next_ptr are the free list pointers of the block getting spliced out.
 * 
 * By using these pointers the functions finds the block before and after in the list, and connect them directly.
 * Effectively removing the current block from the free list while keeping the list useable.
 * 
 * It also handles the special cases of the block being the first or last in the list.
 * 
 */
static void splice_list(void **prev_ptr, void** next_ptr)
{   
    // Get the block before current in free list
    void **block1_prev = *prev_ptr;

    // If this is the first block in the list our block_1 pointers will point to the root node.
    // This node only has a single pointer, so prev and next will point to the same address.
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
    // If we are the last block, block2_next will be NULL, and so block1 will then be the last block.
    *block1_next = block2_next;

    // If this is the last block, there is not prev pointer to point bacwards, so do nothing.
    if (*next_ptr != NULL)
        *block2_prev = block1_prev;
}

/*
 * coalesce - Performs coalescing backwards and forwards. Modyfies free list as required.
 * 
 * The header and footer passed as parameters are the header and footer of a newly free block.
 * Meaning a free block not yet in the free list.
 * 
 * If coalesce finds an adjacent free block it will splice this block from the free list and merge with the current block.
 * coalesce does not add the finished block to the free list when done.
 * 
 * It returns the new header location as a size_t*. It may or may not be modified from the one passed in.
 * 
 */
static size_t* coalesce(size_t *header, size_t *footer)
{
    // Find the previous footer
    size_t *prev_foot = (size_t*)((char*)header - SIZE_T_SIZE); 

    // Check that it is not the root and whether the free bit is set
    if ((void*)prev_foot > mem_heap_lo() && (*prev_foot & 1) == 1)
    {
        // free bit is set, so we merge
        
        // Calculate the size after merging, consuming the header and footer inside
        size_t new_size = ((*header & BITMASK) + (*prev_foot & BITMASK) + 2 * SIZE_T_SIZE) | 1;

        // We move our header pointer back to the header of the other block
        header = (size_t*)((char*)prev_foot - ((*prev_foot & BITMASK) + SIZE_T_SIZE));
        
        // We find the free list pointers of the consumed block
        void **prev_ptr = (void*)((char*)header + SIZE_T_SIZE);
        // Pointer to nexts next_ptr
        void **next_ptr = prev_ptr + 1;

        // And remove it from the free list
        splice_list(prev_ptr, next_ptr);

        // We then set header and footer to the new size
        *header = new_size;
        *footer = new_size;
    }

    // Now we check after the current block
    size_t *next_head = (size_t*)((char*)footer + SIZE_T_SIZE);

    // We check that the free bit is set, and that the adress is not outside the heap
    if ((void*)next_head < mem_heap_hi() && (*next_head & 1) == 1)
    {
        // Coalesce, same as above but moving the footer instead of the header
        size_t new_size = ((*header & BITMASK) + (*next_head & BITMASK) + 2 * SIZE_T_SIZE) | 1;

        footer = (size_t*)((char*)next_head + (*next_head & BITMASK) + SIZE_T_SIZE);
        
        void **prev_ptr = (void*)((char*)next_head + SIZE_T_SIZE);
        void **next_ptr = prev_ptr + 1;

        splice_list(prev_ptr, next_ptr);

        *header = new_size;
        *footer = new_size;
    }

    // Return the header to the coalesced block
    return header;
}

/*
 * FL_push_front - Pushed a block to the front of the free list.
 */
static void FL_push_front(size_t *header)
{
    // Find the location for the free list pointers
    void **prev_ptr = (void*)((char*)header + SIZE_T_SIZE);
    void **next_ptr = prev_ptr + 1;

    // Get the root pointer
    void **root = mem_heap_lo();

    // Add this block to beginning of list.
    // We point to the previous first block

    // Our next_ptr is set to whatever root pointed to before
    *next_ptr = *root;

    // Our previous pointer points back to root
    *prev_ptr = root;

    // Root points to us
    *root = next_ptr;

    // The next blocks prev_ptr should point to us
    // Unless we are the last block, and our next_ptr is NULL
    if (*next_ptr != NULL)
    {
        void **other_prev = (void*)((char*)*next_ptr - 4);
        *other_prev = prev_ptr;
    }
}


/*
 * ========================================================
 *              mm_check and related helpers
 * ========================================================
 */


static int mm_check(void)
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
    if (check_inv_list() == 0){
        return 0;
    }
    return 1;
}

static int mm_valid_heap(void){
    // char *heap_check;
    // for (heap_check = NEXT_BLKP(heap_listp); heap_check < epilogue_block; heap_check = NEXT_BLKP(heap_check)) {
    //     if((HEADER(heap_check) < HEADER(NEXT_BLKP(heap_listp))) || ((char *)GET(HEADER(heap_check)) > epilogue_block) ||  (GET_ALIGN(HEADER(heap_check)) != 0)) {
    //         printf("Error: current block points to an invalid heap address: %p\n", heap_check);
    //         return 0;
    //     }
    // }
    return 1;
}

static int checkCoalseceAndFree(void){
    // char*  current = list_head;
    // int i;
    // for (i = 0; i < free_count; i++){
    //     if (GET_ALLOC(HEADER(current)) || GET_ALLOC(FOOTER(current))) {     /* if either the header or the footer are marked allocated */
    //         return 0;
    //     }
    //     if (NEXT_BLKP(current) !=0 && !GET_ALLOC(HEADER(NEXT_BLKP(current)))) {     /* if either the header or the footer are marked allocated */
    //         return 0;   /* If it has a next and is free */
    //     }
    //     if (PREV_BLKP(current+SIZE_T_SIZE) !=0 && !GET_ALLOC(HEADER(PREV_BLKP(current)))) {     /* if either the header or the footer are marked allocated */
    //         return 0;   /* If it has a previous and is free */
    //     }
    //     current = (char*)GET(current+SIZE_T_SIZE);
    // }
    return 1;
}

static int checkOverlap(void){
    return 1;
}

static int checkFreeInList(void){
    return 1;
}

/*
 * check_inv_list - Checks whether forwards and reverse free lists are the same
 */
static int check_inv_list(void)
{
    void **node = mem_heap_lo();
    int index = 0;
    node = *node;
    if (node == NULL)
        return 1;
    while (*node != NULL)
    {
        void **next = *node;
        void **next_prev = (void*)((char*)next - 4);
        void **back_prev = *next_prev;
        void **back_again = (void*)((char*)back_prev + 4);

        if (node != back_again)
        {
            printf("ERROR IN REV CHAIN %p => (%p : %p) => (%p : %p)\n", node, next_prev, next, back_prev, back_again);
            return 0;
        }

        node = *node;
        index++;
        if (index > 1024)
            break;
    }
    return 1;
}










