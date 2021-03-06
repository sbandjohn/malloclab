/* 
 * 林涛 1600012773
 * a simple dynamic memory allocator using segregated lists.
 *
 */
//#define DEBUG

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdlib.h>
#include <time.h>

#include "mm.h"
#include "memlib.h"

#define UL unsigned long

#define LEFT 1
#define RIGHT 0
#define MIDDLE 2
#define THRESHOLD 10000000 

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
#define CHUNKSIZE  512  /* Extend heap by this amount (bytes) */  

#define LISTSZ		DSIZE

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) 

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))            
#define PUT(p, val)  (*(unsigned int *)(p) = (val))    

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)                   
#define GET_ALLOC(p) (GET(p) & 0x1)                  
#define GET_A(p)  GET_ALLOC(p)
#define GET_PA(p)    ((GET(p) & 0x2) != 0)

#define SET_SIZE(p, v)  (*(unsigned int*)(p) = (GET(p) & 0x7) | (v))
#define SET_A(p, v)   (*(unsigned int*)(p) = (GET(p) & ~0x1) | (v))
#define SET_PA(p, v)  (*(unsigned int*)(p) = (GET(p) & ~0x2) | ((v) << 1))

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)                      
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) 

/* Given block ptr bp, compute address of next and previous blocks */
#define PREV_FTRP(bp)  ((char *)(bp) - DSIZE)
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) 
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(PREV_FTRP(bp)))

/* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */  

static int cntL=0, cntR=0, cntM=0;
static int max_choice = 0;
#define LN 15

#define HPA     	((char*)heap_listp)
#define OFF(bp) 	((char *)bp - HPA)
#define ADD(off) 	(HPA + (off))
#define PTO(pp) 	(ADD(GET_SIZE(pp)))
#define NXP(bp) 	((char *)bp + WSIZE)
#define NXO(bp) 	(GET_SIZE(NXP(bp))) 
#define NXT(bp) 	(PTO(NXP(bp)))
#define NNP(bp) 	((char *)bp + DSIZE)
#define NNO(bp) 	(GET_SIZE(NNP(bp)))

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void *place(void *bp, size_t asize, int mode);
static void *coalesce(void *bp);

static void *get_list(size_t sz);

static void insert_to_list(void *lst, void *bp);
static void insert_node(void *bp);

static void *locate_in_list(void *lst, void *bp);

static void *delete_from_list(void *lst, void *bp);
static void *delete_node(void *bp);
static void *find_node(size_t sz, int mode);
static void *find_in_list(void *lst, size_t sz, int mode);

static void insert_to_l0(void *bp);
static void *delete_from_l0(void *pp);
static void *find_in_l0();
static void *locate_in_l0(void *bp);

static void *place_l0(void *bp);

static void *new_unit(void *nb, unsigned pa);
static void *new_node(void *nb, size_t sz, unsigned pa);
static void *new_allocate(void *nb, size_t sz, unsigned pa);


inline int power2(size_t sz){
	int id;
	if (sz<=8) id = 0;
	else if (sz<=16) id = 1;
	else if (sz<=32) id = 2;
	else if (sz<=64) id = 3;
	else if (sz<=128) id = 4;
	else if (sz<=256) id = 5;
	else if (sz<=512) id = 6;
	else if (sz<=1024) id = 7;
	else if (sz<=2048) id = 8;
	else if (sz<=4096) id = 9;
	else if (sz<=8192) id = 10;
	else if (sz<=16384) id = 11;
	else if (sz<=32768) id = 12;
	else if (sz<=65536) id = 13;
	else id = 14;
	return id;
}


inline int fibonacci(size_t sz){
	if (sz<=8) return 0;
	if (sz<=16) return 1;
	if (sz<=32) return 2;
	if (sz<=48) return 3;
	if (sz<=80) return 4;
	if (sz<=128) return 5;
	if (sz<=208) return 6;
	if (sz<=336) return 7;
	if (sz<=544) return 8;
	if (sz<=880) return 9;
	if (sz<=1424) return 10;
	if (sz<=2304) return 11;
	if (sz<=3728) return 12;
	if (sz<=6032) return 13;
	return 14;
}

inline int get_listID(size_t sz){
	if (sz<=8) return 0;
	return power2(sz);
}

static int get_ID(void *lst){
	return OFF(lst) / LISTSZ;
}

static int get_order(void *lst){
	return get_ID(lst) <= 4;
}

static void *get_list_byID(int id){
	return ADD(id*LISTSZ);
}

static void *get_list(size_t sz){
	return get_list_byID(get_listID(sz));
}

void *find_node(size_t sz, int mode){
	if (sz <= DSIZE) sz = 2*DSIZE;
	int id = get_listID(sz);
	for (int i=id; i<LN; ++i){
		void *lst = get_list_byID(i);
		void *pp = find_in_list(lst, sz, mode);
		if (pp != NULL) return pp;
	}
	return NULL;
}

void *find_in_list(void *lst, size_t sz, int mode){
	void *pp = lst;
	/*size_t minsz = 0;
	void *best = NULL;
	int cnt = 0;*/
	if (mode == LEFT){
		while (GET_SIZE(pp)!=0){
			void *bp = PTO(pp);
			size_t cursz = GET_SIZE(HDRP(bp));
			if (cursz >= sz){
		/*		if (cursz > minsz){
					minsz = cursz;
					cnt = 1;
					best = pp;
				}else if (cursz == minsz){
					++cnt;
					if (GET_SIZE(pp) > GET_SIZE(best)) best = pp;
				}*/
				return pp;
			}
			pp = NXP(bp);
		}
		/*if (cnt > max_choice) max_choice = cnt;
		return best; */
		return NULL;
	}else if (mode == RIGHT){
		void *pre = NULL;
		while (GET_SIZE(pp)!=0){
			void *bp = PTO(pp);
			if (GET_SIZE(HDRP(bp)) >= sz){
				pre = pp;
			}
			pp = NXP(pp);
		}
		return pre;
	}

	return NULL;
}

void *find_in_l0(){
	void *pp = get_list_byID(0);
	if (GET_SIZE(pp) != 0) return pp;
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

static int cmp_size(void *a, void *b){
	return GET_SIZE(a) < GET_SIZE(b);
}

void insert_to_list(void *lst, void *bp){
	size_t tailOff = NXO(lst);
	size_t curOff = OFF(bp);
	SET_SIZE(bp, tailOff);
	SET_SIZE(NXP(bp), 0);
	SET_SIZE(NXP(lst), curOff);
	if (tailOff)
		SET_SIZE(NXP(ADD(tailOff)), curOff); 
	else
		SET_SIZE(lst, curOff);
}

void insert_to_l0(void *bp){
	void *pp = get_list_byID(0);
	while (GET_SIZE(pp) != 0){
		pp = PTO(pp);
	}
	SET_SIZE(bp, GET_SIZE(pp));
	SET_SIZE(pp, OFF(bp));
}

void *locate_in_list(void *lst, void *bp){
	void *pp = lst;
	while (GET_SIZE(pp)!=0){
		if (PTO(pp) == bp)
			return pp;
		pp = NXP(PTO(pp));
	}
	return NULL;
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
	size_t preOff = GET_SIZE(bp);
	size_t nexOff = NXO(bp);
	if (preOff){
		SET_SIZE(NXP(ADD(preOff)), nexOff);
	}else{
		SET_SIZE(lst, nexOff);
	}
	if (nexOff){
		SET_SIZE(ADD(nexOff), preOff);
	}else{
		SET_SIZE(NXP(lst), preOff);
	}
	return bp;
}

void *delete_l0(void *pp){
	void *bp = PTO(pp);
	SET_SIZE(pp, GET_SIZE(bp));
	return bp;
}

void *locate_in_l0(void *bp){
	void *pp = get_list_byID(0);
	while (GET_SIZE(pp) != 0){
		if (PTO(pp) == bp) return pp;
		pp = PTO(pp);
	}
	return NULL;
}

void *delete_from_l0(void *bp){
	void *pp = locate_in_l0(bp);
	if (NULL == pp){
		fprintf(stderr, "delete from l0: no %lx in it\n", (UL)bp);
		exit(0);
	}
	return delete_l0(pp);
}

void *new_unit(void *nb, unsigned pa){
	SET_SIZE(HDRP(nb), DSIZE);
	SET_A(HDRP(nb), 0);
	SET_PA(HDRP(nb), pa);
	SET_A(nb, 1);           /* to tell the next block this is a unit */
	return nb;
}

void *new_node(void *nb, size_t sz, unsigned pa){
	SET_SIZE(HDRP(nb), sz);
	SET_A(HDRP(nb), 0);
	SET_PA(HDRP(nb), pa);
	PUT(FTRP(nb), PACK(sz, 0));
	return nb;
}

void *new_allocate(void *nb, size_t sz, unsigned pa){
	SET_SIZE(HDRP(nb), sz);
	SET_A(HDRP(nb), 1);
	SET_PA(HDRP(nb), pa);
	return nb;
}

/* 
 * mm_init - Initialize the memory manager 
 */
int mm_init(void) 
{
	/* Create the initial empty heap */
	srand(time(NULL));
	size_t sz = LN*LISTSZ + 2*DSIZE;
	if ((heap_listp = mem_sbrk((sz))) == (void *)-1) 
		return -1;

	for (int i=0; i<LN; ++i){
		PUT(ADD(i*LISTSZ), 0);
		PUT(ADD(i*LISTSZ+WSIZE), 0);
	}
	void* pro = ADD(sz - DSIZE);
	new_allocate(pro, DSIZE, 0);
	void* epi = ADD(sz);
	new_allocate(epi, 0, 1);

	cntL = 0; cntR = 0; cntM = 0;
	max_choice = 0;
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

#ifdef DEBUG
	mm_checkheap(__LINE__);
#endif

	if (heap_listp == 0){
		mm_init();
	}
	/* Ignore spurious requests */
	if (size == 0)
		return NULL;

	/* Adjust block size to include overhead and alignment reqs. */
	asize = DSIZE * ((size + (WSIZE) + (DSIZE-1)) / (DSIZE)); 

	//asize = MAX(asize, 2*DSIZE);
	//printf("malloc %d\n", (int)asize);

	void *pp;

	if (asize == DSIZE){
		pp = find_in_l0();
		if (NULL != pp){
			bp = delete_l0(pp);
			return place_l0(bp);
		}
	}

	//int mode = asize <= THRESHOLD ? LEFT : RIGHT;
	int mode = LEFT;

	pp = find_node(MAX(2*DSIZE, asize), mode);

	if (NULL != pp){
		bp = delete_node(PTO(pp));
	}else{
		extendsize = MAX(asize, CHUNKSIZE);
		if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
			return NULL;
	}

	return place(bp, asize, mode);
} 

/* 
 * free - Free a block 
 */
void mm_free(void *bp)
{
	if (bp == 0) 
		return;

	size_t size = GET_SIZE(HDRP(bp));

	//printf("free %d\n", (int)size);
	
	if (size == DSIZE)
		new_unit(bp, GET_PA(HDRP(bp)));
	else
		new_node(bp, size, GET_PA(HDRP(bp)));

	void *sucb = NEXT_BLKP(bp);
	SET_PA(HDRP(sucb), 0);

	bp = coalesce(bp);
	if (GET_SIZE(HDRP(bp)) == DSIZE)
		insert_to_l0(bp);
	else
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
	void *pp = lst;
	int cnt = 0;
	while (GET_SIZE(pp)!=0){
		void *bp = PTO(pp);
		pp = NXP(bp);
		++cnt;	
	}
	printf("list: %d size: %d\n", get_ID(lst), cnt);
}

/* 
 * mm_checkheap - Check the heap for correctness. Helpful hint: You
 *                can call this function using mm_checkheap(__LINE__);
 *                to identify the line number of the call site.
 */
void mm_checkheap(int lineno)  
{ 
	static int cnt = 0;
	lineno = lineno; /* keep gcc happy */
	++cnt;
	if (cnt % 10000 != 0) return ;
	for (int i=1; i<LN; ++i){
	//	print_list(get_list_byID(i));
	}
	printf("\n%d %d %d   max_choice:%d\n", cntL, cntR, cntM, max_choice);
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

	/* bp is a node and it's pa doesn't change */
	new_node(bp, size, GET_PA(HDRP(bp)));

	void *nepi = NEXT_BLKP(bp);
	new_allocate(nepi, 0, 0);

	/* Coalesce if the previous block was free */
	return coalesce(bp);
}

/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *bp) 
{
	size_t prev_alloc = GET_PA(HDRP(bp));
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));
	void *nextb, *prevb;

	if (prev_alloc && next_alloc) {            /* Case 1 */
		return bp;
	}

	else if (prev_alloc && !next_alloc) {      /* Case 2 */
		nextb = NEXT_BLKP(bp);
		int nxt_sz = GET_SIZE(HDRP(nextb));
		if (nxt_sz == DSIZE)
			delete_from_l0(nextb);
		else
			delete_node(nextb);
		size += nxt_sz;
		new_node(bp, size, GET_PA(HDRP(bp)));
	}

	else if (!prev_alloc && next_alloc) {      /* Case 3 */
		/* prevb is unit when prevb's A is 1 */
		unsigned a = GET_A(PREV_FTRP(bp));
		if (a){
			prevb = PREV_FTRP(bp);
			delete_from_l0(prevb);
		}else{
			prevb = PREV_BLKP(bp);
			delete_node(prevb);
		}
		size += GET_SIZE(HDRP(prevb));
		
		bp = prevb;
		new_node(bp, size, GET_PA(HDRP(bp)));
	}

	else {                                     /* Case 4 */
		nextb = NEXT_BLKP(bp);
		int nxt_sz = GET_SIZE(HDRP(nextb));
		if (nxt_sz == DSIZE)                   /* whether next block is unit */
			delete_from_l0(nextb);
		else
			delete_node(nextb);
		size += nxt_sz;

		int a = GET_A(PREV_FTRP(bp));
		if (a){                             /* whether previous block is unit */
			prevb = PREV_FTRP(bp);
			delete_from_l0(prevb);
		}else{
			prevb = PREV_BLKP(bp);
			delete_node(prevb);
		}
		size += GET_SIZE(HDRP(prevb));

		bp = prevb;
		new_node(bp, size, GET_PA(HDRP(bp)));
	}
	
	return bp;
}

/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
static void *place(void *bp, size_t asize, int mode)
{
	size_t csize = GET_SIZE(HDRP(bp));   
	size_t dsize = csize - asize;

	if (dsize == 0){
		new_allocate(bp, asize, GET_PA(HDRP(bp)));
		void *nb = NEXT_BLKP(bp);
		SET_PA(HDRP(nb), 1);
		return bp;
	}

	size_t prev_a = GET_PA(HDRP(bp));
	size_t next_a = GET_A(NEXT_BLKP(bp));

	//printf("dsize %d\n", dsize);
	if (prev_a && !next_a){
		++cntL;
	}
	if (!prev_a && next_a){
		++cntR;
	}
	if (!prev_a && !next_a){
		++cntM;
	}

	if (prev_a) mode = LEFT;
	else{
		if (next_a) mode = RIGHT;
		else
			mode = rand()%2 ? LEFT : RIGHT;
	}

	mode = LEFT;

	if (mode == LEFT){
		new_allocate(bp, asize, GET_PA(HDRP(bp)));
		void *nb = NEXT_BLKP(bp);
		if (dsize == DSIZE){
			new_unit(nb, 1);
			insert_to_l0(nb);
		}
		else if (dsize >= 2*DSIZE){
			new_node(nb, dsize, 1);
			insert_node(nb);
		}else{
			fprintf(stderr, "place error: dsize = %d\n", (int)dsize);
			exit(0);
		}
		return bp;
	}
	else if (mode == RIGHT){
		if (dsize == DSIZE){
			new_unit(bp, GET_PA(HDRP(bp)));
			insert_to_l0(bp);
		}else if (dsize >= 2*DSIZE){
			new_node(bp, dsize, GET_PA(HDRP(bp)));
			insert_node(bp);
		}else{
			fprintf(stderr,"place error: dsize = %d\n", (int)dsize);
			exit(0);
		}
		void *nb = NEXT_BLKP(bp);
		new_allocate(nb, asize, 0);
		SET_PA(HDRP(NEXT_BLKP(nb)), 1);
		return nb;
	}

	return NULL;
}

static void *place_l0(void *bp){
	return place(bp, DSIZE, LEFT);
}

