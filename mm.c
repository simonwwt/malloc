/*
 * mm.c
 * Name: Weitao Wen
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stdbool.h>
#include <stdint.h>

#include "mm.h"
#include "memlib.h"

/*
 * If you want debugging output, uncomment the following.  Be sure not
 * to have debugging enabled in your final submission
 */
//#define DEBUG

#ifdef DEBUG
/* When debugging is enabled, the underlying functions get called */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#define dbg_requires(...) assert(__VA_ARGS__)
#define dbg_ensures(...) assert(__VA_ARGS__) 
#define dbg_checkheap(...) mm_checkheap(__VA_ARGS__)
#define dbg_printheap(...) print_heap(__VA_ARGS__)
#else
/* When debugging is disabled, no code gets generated */
#define dbg_printf(...)
#define dbg_assert(...)
#define dbg_requires(...)
#define dbg_ensures(...)
#define dbg_checkheap(...)
#define dbg_printheap(...)
#endif

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* def DRIVER */

/* What is the correct alignment? */
#define ALIGNMENT 16

/* rounds up to the nearest multiple of ALIGNMENT */
static size_t align(size_t x) {
    return ALIGNMENT * ((x+ALIGNMENT-1)/ALIGNMENT);
}


/* Basic constants */
typedef uint64_t word_t;
static const size_t wsize = sizeof(word_t);   // word and header size (bytes)
static const size_t dsize = 2*wsize;          // double word size (bytes)
static const size_t min_block_size = 2*dsize; // Minimum block size
static const size_t chunksize = (1 << 12);    // requires (chunksize % 16 == 0)
static const word_t prevaAlloc_mask = 0x2;
static const word_t alloc_mask = 0x1;
static const word_t size_mask = ~(word_t)0xF;

typedef struct block
{
    /* Header contains size + allocation flag */
    word_t header;
    /*
     * We don't know how big the payload will be.  Declaring it as an
     * array of size 0 allows computing its starting address using
     * pointer notation.
     */
    char payload[0];
    /*
     * We can't declare the footer as part of the struct, since its starting
     * position is unknown
     */
} block_t;


/* Global variables */
/* Pointer to first block */
static block_t *heap_listp = NULL;
/* Pointer to free block list */
static block_t *free_listp = NULL;
/* Pointer to the end of free block list */
static block_t *end_listp = NULL;

/* Function prototypes for internal helper routines */
static block_t *extend_heap(size_t size);
static void place(block_t *block, size_t asize);
static block_t *find_fit(size_t asize);
static block_t *coalesce(block_t *block);

static size_t max(size_t x, size_t y);
static size_t round_up(size_t size, size_t n);
static word_t pack(size_t size, bool prevAlloc, bool alloc);

static size_t extract_size(word_t header);
static size_t get_size(block_t *block);
static size_t get_payload_size(block_t *block);

static bool extract_alloc(word_t header);
static bool get_alloc(block_t *block);

static void write_header(block_t *block, size_t size, bool prev, bool alloc);
static void write_footer(block_t *block, size_t size, bool prev, bool alloc);

static block_t *payload_to_header(void *bp);
static void *header_to_payload(block_t *block);

static block_t *find_next(block_t *block);
static word_t *find_prev_footer(block_t *block);
static block_t *find_prev(block_t *block);

/* Function added by wwt */
inline static word_t *get_pred(block_t *freeBlock);
inline static word_t *get_succ(block_t *freeBlock);
inline static void write_pred(block_t *block, block_t *pred_block);
inline static void write_succ(block_t *block, block_t *succ_block);
inline static block_t *find_nextFree(block_t *block);
inline static block_t *find_prevFree(block_t *block);
static void setNewRoot(block_t *block);
static void setNewEnd(block_t *block);
static void deleteFreeBlock(block_t *block);
static bool extract_prevAlloc(word_t word);
static bool get_prevAlloc(block_t *block);
/*
 * Initialize: return false on error, true on success.
 */
bool mm_init(void) {
    heap_listp = NULL;
    free_listp = NULL;
    end_listp = NULL;
    // Create the initial empty heap 
    word_t *start = (word_t *)(mem_sbrk(2*wsize));

    if (start == (void *)-1) 
    {
        return false;
    }

    start[0] = pack(0, true, true); // Prologue footer
    start[1] = pack(0, true, true); // Epilogue header
    // Heap starts with first block header (epilogue)
    heap_listp = (block_t *) &(start[1]);
    // Free block list starts with first block headr plus wsize
    free_listp = (block_t *) &(start[1]);
    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL)
    {
        return false;
    }
    return true;
}

/*
 * malloc
 */
void *malloc (size_t size) {
    dbg_requires(mm_checkheap);
    
    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;

    if (heap_listp == NULL) // Initialize heap if it isn't initialized
    {
        mm_init();
    }

    if (size == 0) // Ignore spurious request
    {
        dbg_ensures(mm_checkheap);
        return bp;
    }

    // Adjust block size to include overhead and to meet alignment requirements
    asize = max(round_up(size + wsize, dsize), min_block_size);
    
    // Search the free list for a fit
    block = find_fit(asize);

    // If no fit is found, request more memory, and then and place the block
    if (block == NULL)
    {  
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);
        if (block == NULL) // extend_heap returns an error
        {
            return bp;
        }

    }

    place(block, asize);
    bp = header_to_payload(block);

    dbg_printf("Malloc size %zd on address %p.\n", size, bp);
    dbg_ensures(mm_checkheap);
    return bp;
}

/*
 * free
 */
void free (void *ptr) {
    if (ptr == NULL)
        return;

    block_t *block = payload_to_header(ptr);
    size_t size = get_size(block);
    bool prev_alloc = get_prevAlloc(block);
    write_header(block, size, prev_alloc, false);
    write_footer(block, size, prev_alloc, false);

    block_t *next_block = find_next(block);
    size_t next_size = get_size(next_block);
    bool next_alloc = get_alloc(next_block);
    write_header(next_block, next_size, false, next_alloc);
    if (!next_alloc)
        write_footer(next_block, next_size, false, next_alloc);
    coalesce(block);
}

/*
 * realloc
 */
void *realloc(void *oldptr, size_t size) {
    block_t *block = payload_to_header(oldptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0)
    {
        free(oldptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (oldptr == NULL)
    {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);
    // If malloc fails, the original block is left untouched
    if (!newptr)
    {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if(size < copysize)
    {
        copysize = size;
    }
    memcpy(newptr, oldptr, copysize);

    // Free the old block
    free(oldptr);

    return newptr;
}

/*
 * calloc
 * This function is not tested by mdriver
 */
void *calloc (size_t nmemb, size_t size) {
    void *bp;
    size_t asize = nmemb * size;

    if (asize/nmemb != size)
    // Multiplication overflowed
    return NULL;
    
    bp = malloc(asize);
    if (bp == NULL)
    {
        return NULL;
    }
    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}


/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static bool in_heap(const void *p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static bool aligned(const void *p) {
    size_t ip = (size_t) p;
    return align(ip) == ip;
}

/*
 * mm_checkheap
 */
bool mm_checkheap(int lineno) {
    //printf("Heap (%p):\n", heap_listp);

    //if ()
    return true;
}


/******** The remaining content below are helper and debug routines ********/

/*
 * extend_heap: Extends the heap with the requested number of bytes, and
 *              recreates epilogue header. Returns a pointer to the result of
 *              coalescing the newly-created block with previous free block, if
 *              applicable, or NULL in failure.
 */
static block_t *extend_heap(size_t size) 
{
    void *bp;

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1)
    {
        return NULL;
    }
    
    // Initialize free block header, pred, succ, footer 
    block_t *block = payload_to_header(bp);
    bool prevAlloc = get_prevAlloc(block);
    write_header(block, size, prevAlloc, false);
    write_pred(block, NULL);
    write_succ(block, NULL);
    write_footer(block, size, prevAlloc, false);
    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_header(block_next, 0, false, true);

    // Coalesce in case the previous block was free
    return coalesce(block);
}

/* Coalesce: 
 */
static block_t *coalesce(block_t *block) 
{
    block_t *block_next = find_next(block);
    //block_t *block_prev = find_prev(block);

    bool prev_alloc = get_prevAlloc(block);
    bool next_alloc = get_alloc(block_next);
    size_t size = get_size(block);

    if (prev_alloc && next_alloc)              // Case 1
    {
        //setNewRoot(block);
        setNewEnd(block);
        return block;
    }

    else if (prev_alloc && !next_alloc)        // Case 2
    {
        size += get_size(block_next);
        write_header(block, size, prev_alloc, false);
        write_footer(block, size, prev_alloc, false);

        deleteFreeBlock(block_next);
        //setNewRoot(block);
        setNewEnd(block);
    }

    else if (!prev_alloc && next_alloc)        // Case 3
    {
        block_t *block_prev = find_prev(block);
        bool prevprev_alloc = get_prevAlloc(block_prev);

        size += get_size(block_prev);
        write_header(block_prev, size, prevprev_alloc, false);
        write_footer(block_prev, size, prevprev_alloc, false);
        block = block_prev;

        deleteFreeBlock(block);
        //setNewRoot(block);
        setNewEnd(block);
    }

    else                                        // Case 4
    {
        block_t *block_prev = find_prev(block);
        bool prevprev_alloc = get_prevAlloc(block_prev);

        size += get_size(block_next) + get_size(block_prev);
        write_header(block_prev, size, prevprev_alloc, false);
        write_footer(block_prev, size, prevprev_alloc, false);
        block = block_prev;

        deleteFreeBlock(block);
        deleteFreeBlock(block_next);
        //setNewRoot(block);
        setNewEnd(block);
    }
    dbg_requires(get_alloc(find_next(block)) && get_alloc(find_next(block)));
    return block;
}

/*
 * place: Places block with size of asize at the start of bp. If the remaining
 *        size is at least the minimum block size, then split the block to the
 *        the allocated block and the remaining block as free, which is then
 *        inserted into the segregated list. Requires that the block is
 *        initially unallocated.
 */
static void place(block_t *block, size_t asize)
{
    size_t csize = get_size(block);
    block_t *block_next;
    bool prevAlloc = get_prevAlloc(block);

    deleteFreeBlock(block);
    if ((csize - asize) >= min_block_size)
    {
        write_header(block, asize, prevAlloc, true); 

        block_next = find_next(block);
        write_header(block_next, csize-asize, true, false);
        write_footer(block_next, csize-asize, true, false);
        coalesce(block_next);
    }
    else
    { 
        write_header(block, csize, prevAlloc, true);

        block_next = find_next(block);
        size_t next_size = get_size(block_next);
        bool next_alloc = get_alloc(block_next);
        write_header(block_next, next_size, true, next_alloc);
        if (!next_alloc)
            write_footer(block_next, next_size, true, next_alloc);
    }
}

/*
 * find_fit: Looks for a free block with at least asize bytes with
 *           first-fit policy. Returns NULL if none is found.
 */
static block_t *find_fit(size_t asize)
{
    block_t *block;

    for (block = free_listp; block != NULL;
                             block = find_nextFree(block))
    {
        if (asize <= get_size(block))
        {
            return block;
        }
    }
    return NULL; // no fit found
}

/*
 * max: returns x if x > y, and y otherwise.
 */
static size_t max(size_t x, size_t y)
{
    return (x > y) ? x : y;
}


/*
 * round_up: Rounds size up to next multiple of n
 */
static size_t round_up(size_t size, size_t n)
{
    return (n * ((size + (n-1)) / n));
}

/*
 * pack: returns a header reflecting a specified size and its alloc status.
 *       If the block is allocated, the lowest bit is set to 1, and 0 otherwise.
 */
static word_t pack(size_t size, bool prevAlloc, bool alloc)
{
    word_t temp = prevAlloc ? (size | 2) : size;
    return alloc ? (temp | 1) : temp;
}


/*
 * extract_size: returns the size of a given header value based on the header
 *               specification above.
 */
static size_t extract_size(word_t word)
{
    return (word & size_mask);
}

/*
 * get_size: returns the size of a given block by clearing the lowest 4 bits
 *           (as the heap is 16-byte aligned).
 */
static size_t get_size(block_t *block)
{
    return extract_size(block->header);
}

/*
 * get_payload_size: returns the payload size of a given block, equal to
 *                   the entire block size minus the header and footer sizes.
 */
static word_t get_payload_size(block_t *block)
{
    size_t asize = get_size(block);
    return asize - dsize;
}

/*
 * extract_alloc: returns the allocation status of a given header value based
 *                on the header specification above.
 */
static bool extract_alloc(word_t word)
{
    return (bool)(word & alloc_mask);
}

/*
 * get_alloc: returns true when the block is allocated based on the
 *            block header's lowest bit, and false otherwise.
 */
static bool get_alloc(block_t *block)
{
    return extract_alloc(block->header);
}

/*
 * write_header: given a block and its size and allocation status,
 *               writes an appropriate value to the block header.
 */
static void write_header(block_t *block, size_t size, bool prev, bool alloc)
{
    block->header = pack(size, prev, alloc);
}


/*
 * write_footer: given a block and its size and allocation status,
 *               writes an appropriate value to the block footer by first
 *               computing the position of the footer.
 */
static void write_footer(block_t *block, size_t size, bool prev, bool alloc)
{
    word_t *footerp = (word_t *)((block->payload) + get_size(block) - dsize);
    *footerp = pack(size, prev, alloc);
}


/*
 * find_next: returns the next consecutive block on the heap by adding the
 *            size of the block.
 */
static block_t *find_next(block_t *block)
{
    dbg_requires(block != NULL);
    block_t *block_next = (block_t *)(((char *)block) + get_size(block));

    dbg_ensures(block_next != NULL);
    return block_next;
}

/*
 * find_prev_footer: returns the footer of the previous block.
 */
static word_t *find_prev_footer(block_t *block)
{
    // Compute previous footer position as one word before the header
    return (&(block->header)) - 1;
}

/*
 * find_prev: returns the previous block position by checking the previous
 *            block's footer and calculating the start of the previous block
 *            based on its size.
 */
static block_t *find_prev(block_t *block)
{
    word_t *footerp = find_prev_footer(block);
    size_t size = extract_size(*footerp);
    return (block_t *)((char *)block - size);
}

/*
 * payload_to_header: given a payload pointer, returns a pointer to the
 *                    corresponding block.
 */
static block_t *payload_to_header(void *bp)
{
    return (block_t *)(((char *)bp) - offsetof(block_t, payload));
}

/*
 * header_to_payload: given a block pointer, returns a pointer to the
 *                    corresponding payload.
 */
static void *header_to_payload(block_t *block)
{
    return (void *)(block->payload);
}


/* Function added by wwt */
/*
 * get_pred:
 */
inline static word_t *get_pred(block_t *freeBlock)
{
    if (freeBlock == NULL)
        return NULL;
    word_t *pred_address = *(word_t **)(freeBlock->payload);
    return pred_address;
}

/*
 * get_succ:
 */
inline static word_t *get_succ(block_t *freeBlock)
{
    if (freeBlock == NULL)
        return NULL;
    word_t *succ_address = *(word_t **)((freeBlock->payload) + wsize);
    return succ_address;
}

/*
 * write_pred:
 */
inline static void write_pred(block_t *block, block_t *pred_block)
{
    if (block == NULL)
        return ;
    word_t *predPtr = (word_t *) block->payload;
    *predPtr = (word_t) pred_block;
}

/*
 * write_succ:
 */
inline static void write_succ(block_t *block, block_t *succ_block)
{
    if (block == NULL)
        return ;
    word_t *succPtr = (word_t *)((block->payload) + wsize);
    *succPtr = (word_t) succ_block;
}

/*
 * find_nextFree: 
 */
inline static block_t *find_nextFree(block_t *block)
{
    if (block == NULL)
        return NULL;
    dbg_requires(block != NULL);
    word_t *address = get_succ(block);
    block_t *block_next = (block_t *) address;

    return block_next;
}

/*
 * find_prevFree: 
 */
inline static block_t *find_prevFree(block_t *block)
{
    if (block == NULL)
        return NULL;
    word_t *address = get_pred(block);
    block_t *block_prev = (block_t *)address;

    return block_prev;
}

/*
 * setNewRoot: 
 */
static void setNewRoot(block_t *block)
{
    if (block == NULL)
        return ;
    write_pred(block, NULL);
    write_succ(block, free_listp);
    if (free_listp != NULL)
        write_pred(free_listp, block);
    free_listp = block;
}

 /*
 * setNewEnd: 
 */
static void setNewEnd(block_t *block)
{
    if (block == NULL)
        return ;
    write_pred(block, end_listp);
    write_succ(block, NULL);
    if (end_listp != NULL)
        write_succ(end_listp, block);
    end_listp = block;

    if (free_listp == NULL)
        free_listp = block;
}

/*
 * deleteFreeBlock: 
 */
static void deleteFreeBlock(block_t *block)
{
    if (block == NULL)
        return ;

    block_t *pred_block = find_prevFree(block);
    block_t *succ_block = find_nextFree(block);

    if (pred_block != NULL)        
        write_succ(pred_block, succ_block);
    else 
        free_listp = succ_block;
    if (succ_block != NULL)    
        write_pred(succ_block, pred_block);
    else
        end_listp = pred_block;
}

/*
 * extract_prevAlloc: returns the previous block allocation status 
 *                    of a given header value based on the header specification above.
 */
static bool extract_prevAlloc(word_t word)
{
    return (bool)(word & prevaAlloc_mask);
}


/*
 * get_prevAlloc: returns true when the preivous block is allocated based on the
 *            block header's second lowest bit, and false otherwise.
 */
static bool get_prevAlloc(block_t *block)
{
    return extract_prevAlloc(block->header);
}

