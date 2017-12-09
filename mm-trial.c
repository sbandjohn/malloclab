/* 
 * 林涛 1600012773
 * a simple dynamic memory allocator using segregated lists.
 *
 */
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "mm.h"
#include "memlib.h"

#define UL unsigned long

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/*
 * If NEXT_FIT defined use next fit search, else use first-fit search 
 */
#define NEXT_FITx

/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */ 
#define DSIZE       8       /* Double word size (bytes) */
//#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */  
#define CHUNKSIZE 512

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) 

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))            
#define PUT(p, val)  (*(unsigned int *)(p) = (val))    

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)                   
#define GET_ALLOC(p) (GET(p) & 0x1)                    
#define GET_PA(p)    (GET(p) & 0x2)

#define SET_PA(p, v)  (*(unsigned int*)(p) = (GET(p) ^ GET_PA(p)) | ((v) << 1))

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)                      
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) 

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) 
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) 

/* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */  
#ifdef NEXT_FIT
static char *rover;           /* Next fit rover */
#endif

#define LN 13

#define HPA     	((char*)heap_listp)
#define OFF(bp) 	((char *)bp - HPA)
#define ADD(off) 	(HPA + (off))
#define PTO(pp) 	(ADD(GET(pp)))
#define NXP(bp) 	((char *)bp + WSIZE)
#define NXO(bp) 	(GET(NXP(bp))) 
#define NXT(bp) 	(PTO(NXP(bp)))

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);

static void *get_list(size_t sz);
static void insert(void *pp, void *bp);
static void insert_to_list(void *lst, void *bp);
static void insert_node(void *bp);
static void *delete(void *pp);
static void *delete_from_list(void *lst, void *bp);
static void *delete_node(void *bp);
static void *find_node(size_t sz);
static void *find_in_list(void *lst, size_t sz);

inline int get_listID(size_t sz){
	int id;
	if (sz<=8) id = 0;
	else if (sz<=16) id = 1;
	else if (sz<=24) id = 2;
	else if (sz<=32) id = 3;
	else if (sz<=64) id = 4;
	else if (sz<=128) id = 5;
	else if (sz<=256) id = 6;
	else if (sz<=512) id = 7;
	else if (sz<=1024) id = 8;
	else if (sz<=2048) id = 9;
	else if (sz<=4096) id = 10;
	else if (sz<=8192) id = 11;
	else id = 12;
	return id;
}

static void *get_list_byID(int id){
	return ADD(id*WSIZE);
}

static void *get_list(size_t sz){
	if (sz <=8 ){
		fprintf(stderr, "get list: sz = %d <= 8\n", (int)sz);
		exit(0);
	}
	return get_list_byID(get_listID(sz));
}

void *find_node(size_t sz){
	int id = get_listID(sz);
	for (int i=id; i<LN; ++i){
		void *lst = get_list_byID(i);
		void *pp = find_in_list(lst, sz);
		if (pp != NULL) return pp;
	}
	return NULL;
}

void *find_in_list(void *lst, size_t sz){
	void *pp = lst;
	while (GET(pp)!=0){
		void *bp = PTO(pp);
		if (GET_SIZE(HDRP(bp)) >= sz)
			return pp;
		pp = NXP(bp);
	}
	return NULL;
}

void insert_node(void *bp){
	size_t sz = GET_SIZE(HDRP(bp));
	if (sz < 16){
		fprintf(stderr, "insert node: sz = %d <16\n", (int)sz);
		exit(0);
	}
	void *lst = get_list(sz);
	insert_to_list(lst, bp);
}

void insert_to_list(void *lst, void *bp){
	insert(lst, bp);
}

void insert(void *pp, void *bp){
	PUT(NXP(bp), GET(pp));
	PUT(pp, OFF(bp));
}

void *delete_node(void *bp){
	size_t sz = GET_SIZE(HDRP(bp));
	if (sz < 16){
		fprintf(stderr, "delete node: sz = %d < 16\n", (int)sz);
		exit(0);
	}
	void *lst = get_list(sz);
	return delete_from_list(lst, bp);
}

void *delete_from_list(void *lst, void *bp){
	void *pp = lst;
	while (GET(pp)!=0){
		if (PTO(pp) == bp)
			return delete(pp);
		pp = NXP(PTO(pp));
	}
	fprintf(stderr, "delete from list: not found %lx in list %lx\n", (UL)bp, (UL)lst);
	exit(0);
	return NULL;
}

void *delete(void *pp){
	void *bp = PTO(pp);
	PUT(pp, NXO(bp));
	return bp;
}

/* 
 * mm_init - Initialize the memory manager 
 */
int mm_init(void) 
{
	/* Create the initial empty heap */
	if ((heap_listp = mem_sbrk((LN+3)*WSIZE)) == (void *)-1) 
		return -1;

	for (int i=0; i<LN; ++i){
		PUT(ADD(i*WSIZE), 0);
	}
	void* pro = ADD((LN+1)*WSIZE);
	PUT(HDRP(pro), PACK(DSIZE, 1));
	PUT(FTRP(pro), PACK(DSIZE, 1));
	void* epiH = ADD((LN+2)*WSIZE);
	PUT(epiH, PACK(0, 1));

	return 0;
}

/* 
 * malloc - Allocate a block with at least size bytes of payload 
 */
void *mm_malloc(size_t size) 
{
	size_t asize;      /* Adjusted block size */
	size_t extendsize; /* Amount to extend heap if no fit */
	void *bp;      

	if (heap_listp == 0){
		mm_init();
	}
	/* Ignore spurious requests */
	if (size == 0)
		return NULL;

	/* Adjust block size to include overhead and alignment reqs. */
	if (size <= DSIZE)                                          
		asize = 2*DSIZE;                                        
	else
		asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE); 

	void *pp = find_node(asize);

	if (NULL != pp){
		bp = delete(pp);
		place(bp, asize);
	}else{
		extendsize = MAX(asize, CHUNKSIZE);
		if ((bp = extend_heap(extendsize/WSIZE)) == NULL){
			fprintf(stderr, "malloc: extend heap %d\n", (int)extendsize);
			return NULL;
		}
		place(bp, asize);
	}

	//mm_checkheap(__LINE__);

	return bp;
} 

/* 
 * free - Free a block 
 */
void mm_free(void *bp)
{
	if (bp == 0) 
		return;

	size_t size = GET_SIZE(HDRP(bp));
	
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	void *sucb = NEXT_BLKP(bp);
	SET_PA(HDRP(sucb), 0);
	bp = coalesce(bp);
	insert_node(bp);
}

/*
 * realloc - Naive implementation of realloc
 */
void *mm_realloc(void *ptr, size_t size)
{
	size_t oldsize;
	void *newptr;

	/* If size == 0 then this is just free, and we return NULL. */
	if(size == 0) {
		mm_free(ptr);
		return 0;
	}

	/* If oldptr is NULL, then this is just malloc. */
	if(ptr == NULL) {
		return mm_malloc(size);
	}

	newptr = mm_malloc(size);

	/* If realloc() fails the original block is left untouched  */
	if(!newptr) {
		return 0;
	}

	/* Copy the old data. */
	oldsize = GET_SIZE(HDRP(ptr));
	if(size < oldsize) oldsize = size;
	memcpy(newptr, ptr, oldsize);

	/* Free the old block. */
	mm_free(ptr);

	return newptr;
}

static void print_list(void *lst){
	printf("list: %lx %u\n", (UL)lst, (unsigned)OFF(lst));
	void *pp = lst;
	while (GET(pp)!=0){
		void *bp = PTO(pp);
		printf("   node: %lx %u  size:%u\n", (UL)bp, (unsigned)OFF(bp), (unsigned)GET_SIZE(HDRP(bp)));
		pp = NXP(bp);
	}
	printf("\n\n");
}

/* 
 * mm_checkheap - Check the heap for correctness. Helpful hint: You
 *                can call this function using mm_checkheap(__LINE__);
 *                to identify the line number of the call site.
 */
void mm_checkheap(int lineno)  
{ 
	lineno = lineno; /* keep gcc happy */
	printf("line:%d\n",lineno);
	for (int i=0; i<LN; ++i)
		print_list(get_list_byID(i));
}

/* 
 * The remaining routines are internal helper routines 
 */

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
static void *extend_heap(size_t words) 
{
	char *bp;
	size_t size;

	/* Allocate an even number of words to maintain alignment */
	size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; 
	if ((long)(bp = mem_sbrk(size)) == -1)  
		return NULL;                                        

	/* Initialize free block header/footer and the epilogue header */
	PUT(HDRP(bp), PACK(size, 0));         /* Free block header */   
	PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */   
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */ 

	/* Coalesce if the previous block was free */
	return coalesce(bp);
}

/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *bp) 
{
	size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));
	void *nextb, *prevb;

	if (prev_alloc && next_alloc) {            /* Case 1 */
		return bp;
	}

	else if (prev_alloc && !next_alloc) {      /* Case 2 */
		nextb = NEXT_BLKP(bp);
		delete_node(nextb);
		size += GET_SIZE(HDRP(nextb));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
	}

	else if (!prev_alloc && next_alloc) {      /* Case 3 */
		prevb = PREV_BLKP(bp);
		delete_node(prevb);
		size += GET_SIZE(HDRP(prevb));
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	}

	else {                                     /* Case 4 */
		prevb = PREV_BLKP(bp);
		nextb = NEXT_BLKP(bp);
		delete_node(prevb);
		delete_node(nextb);
		size += GET_SIZE(HDRP(prevb)) + GET_SIZE(FTRP(nextb));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	}
	return bp;
}

/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
static void place(void *bp, size_t asize)
{
	size_t csize = GET_SIZE(HDRP(bp));   

	if ((csize - asize) >= (2*DSIZE)) { 
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(csize-asize, 0));
		PUT(FTRP(bp), PACK(csize-asize, 0));
		insert_node(bp);
		SET_PA(HDRP(bp), 1);
	}
	else { 
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
		bp = NEXT_BLKP(bp);
		SET_PA(HDRP(bp), 1);
	}
}

