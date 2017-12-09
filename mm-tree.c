/* 
 * 林涛 1600012773
 * a simple dynamic memory allocator using segregated lists.
 *
 */
#define DEBUG

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdlib.h>
#include <time.h>
#include <assert.h>


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

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)                      

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)                   
#define GET_A(p)  	(GET(p) & 0x1)
#define GET_PA(p) 	((GET(p) & 0x2) != 0)
#define GET_U(p)    (GET(p) & 0x1)

#define SET_SIZE(p, v)  (*(unsigned int*)(p) = (GET(p) & 0x7) | (v))
#define SET_A(p, v)   (*(unsigned int*)(p) = (GET(p) & ~0x1) | (v))
#define SET_PA(p,v)   (*(unsigned int*)(p) = (GET(p) & ~0x2) | ((v)<<1))
#define SET_U(p, v)  (*(unsigned int*)(p) = (GET(p) & ~0x1) | ((v)))

/* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */  

static int cntL=0, cntR=0, cntM=0;
static int max_choice = 0;
static int height = 0, maxheight = 0;

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

inline size_t get_size(void *bp);
inline void *next_bp(void *bp);
inline void *prev_bp(void *bp);

static void *extend_heap(size_t words);
static void *place(void *bp, size_t asize, int mode);
static void *coalesce(void *bp);

static void *get_list(size_t sz);

static void insert_to_list(void *lst, void *bp, size_t sz);
static void insert_node(void *bp);

static void *locate_in_list(void *lst, void *bp, size_t sz);

static void *delete_from_list(void *lst, void *bp);
static void *delete_node(void *bp);

static void *find_node(size_t sz, int mode);
static void *find_in_list(void *lst, size_t sz, int mode);

inline void *new_node(void *nb, size_t sz, size_t pa);
inline void *new_allocate(void *nb, size_t sz, size_t pa);

static void rotate_left(void *p);
static void rotate_right(void *p);
static void locate_and_splay(void *t, void *x, size_t sz);
static void find_and_splay(void *t, size_t sz);

inline size_t get_size(void *bp){
	size_t a = GET_A(HDRP(bp));
	size_t u = GET_U(bp);
	if (a == 0 && u == 0) return GET_SIZE(NXP(bp));
	if (a == 0 && u == 1) return DSIZE;
	return GET_SIZE(HDRP(bp));
}

inline void *next_bp(void *bp){
	return (void*)((char *)bp + get_size(bp));
}

inline void *prev_bp(void *bp){
	size_t pa = GET_PA(HDRP(bp));
	if (pa){
		fprintf(stderr, "prev block is allocated\n");
		exit(1);
	}
	size_t u = GET_U(HDRP(HDRP(bp)));
	size_t sz = 0;
	if (u == 0) sz = GET_SIZE(HDRP(HDRP(bp)));
	if (u == 1) sz = DSIZE;
	return (void *)((char *)bp - sz);
}

inline void * new_node(void *bp, size_t sz, size_t pa){
	void *ftrp = (char *)bp - DSIZE + sz;
	size_t u = (sz == DSIZE);
	SET_A(HDRP(bp), 0);
	SET_PA(HDRP(bp), pa);
	SET_U(bp, u);
	SET_U(ftrp, u);
	if (u == 0){
		SET_SIZE(NXP(bp), sz);
		SET_SIZE(ftrp, sz);
	}
	return bp;
}

inline void *new_allocate(void *nb, size_t sz, size_t pa){
	SET_SIZE(HDRP(nb), sz);
	SET_A(HDRP(nb), 1);
	SET_PA(HDRP(nb), pa);
	return nb;
}


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

inline size_t in_left(void *cur, void *bp, size_t sz){
	size_t cursz = get_size(cur);
	if (sz < cursz) return 1;
	if (sz > cursz) return 0;
	return bp < cur;
}

void rotate_left(void *p){
	void *x = PTO(p);
	void *y = PTO(x);
	SET_SIZE(x, GET_SIZE(HDRP(y)));
	SET_SIZE(HDRP(y), OFF(x));
	SET_SIZE(p, OFF(y));
}
void rotate_right(void *p){
	void *x = PTO(p);
	void *y = PTO(HDRP(x));
	SET_SIZE(HDRP(x), GET_SIZE(y));
	SET_SIZE(y, OFF(x));
	SET_SIZE(p, OFF(y));
}

void locate_and_splay(void *t, void *x, size_t sz){
	size_t off = GET_SIZE(t);
	if (off == NULL){
		fprintf(stderr, "locate not found\n");
		exit(1);
	}

	void *p = PTO(t);
	if (p == x) return x;
	int left1 = in_left(p, x, sz);
	void *ch1 = left1 ? HDRP(p) : p;
	
	assert(GET_SIZE(ch1) != 0);

	void *q = PTO(ch1);
	if (q != x){
		int left2 = in_left(q, x, sz);
		void ch2 = left2 ? HDRP(q) : q;
		locate_and_splay(ch2, x, sz);
		if (left2) rotate_right(ch1);
		else rotate_left(ch1);
	}
	if (left1) rotate_right(t);
	else rotate_left(t);
}

void find_and_splay(void *t, size_t sz){
	size_t off = GET_SIZE(t);
	if (off == 0) return NULL;

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
	size_t off = GET_SIZE(lst);
	if (off == 0) return NULL;
	void *bp = ADD(off);
	size_t cursz = get_size(bp);
	if (cursz < sz) return find_in_list(bp, sz, mode);
	void *tmp = find_in_list(HDRP(bp), sz, mode);
	if (tmp != NULL) return tmp;
	return lst;
}

void insert_node(void *bp){
	assert(GET_A(HDRP(bp)) == 0);
	size_t sz = get_size(bp);
	void *lst = get_list(sz);
	height = 0;
	insert_to_list(lst, bp, sz);
}

void insert_to_list(void *lst, void *bp, size_t sz){
	height ++;
	if (height > maxheight){
		maxheight = height;
		printf("%d\n",maxheight);
	}

	size_t off = GET_SIZE(lst);
	if (off == 0){
		SET_SIZE(bp, 0);
		SET_SIZE(HDRP(bp), 0);
		SET_SIZE(lst, OFF(bp));
		height--;
		return ;
	}
	void *cur = ADD(off);
	int d = in_left(cur, bp, sz);
	if (d) insert_to_list(HDRP(cur), bp, sz);
	else insert_to_list(cur, bp, sz);
	height--;
}

void *locate_in_list(void *lst, void *bp, size_t sz){
	size_t off = GET_SIZE(lst);
	if (off == 0) return NULL;
	void *cur = ADD(off);
	if (bp == cur) return lst;
	if (in_left(cur, bp, sz)) return locate_in_list(HDRP(cur), bp, sz);
	return locate_in_list(cur, bp, sz);
}

void *delete_node(void *bp){
	assert(GET_A(HDRP(bp)) == 0);
	size_t sz = get_size(bp);
	void *lst = get_list(sz);
	void *pp = locate_in_list(lst, bp, sz);
	if (pp == NULL){
		fprintf(stderr, "delete: node not foun\n");
		exit(1);
	}
	return delete_from_list(pp, bp);
}

void *delete_from_list(void *p, void *x){
	size_t l_off = GET_SIZE(HDRP(x));
	size_t r_off = GET_SIZE(x);
	if (l_off == 0 && r_off == 0){
		SET_SIZE(p, 0);
		return x;
	}
	if (l_off == 0){
		SET_SIZE(p, r_off);
		return x;
	}
	if (r_off == 0){
		SET_SIZE(p, l_off);
		return x;
	}
	void *y = ADD(r_off);
	size_t tmp = GET_SIZE(HDRP(y));
	if (tmp == 0){
		SET_SIZE(HDRP(y), l_off);
		SET_SIZE(p, OFF(y));
		return x;
	}
	void *q = y;
	y = ADD(tmp);
	while ((tmp = GET_SIZE(HDRP(y))) != 0){
		q = y;
		y = ADD(tmp);
	}
	SET_SIZE(HDRP(y), l_off);
	SET_SIZE(x, GET_SIZE(y));
	SET_SIZE(y, r_off);
	SET_SIZE(HDRP(x), 0);
	SET_SIZE(p, OFF(y));
	SET_SIZE(HDRP(q), OFF(x));
	return delete_from_list(HDRP(q), x);
}

/* 
 * mm_init - Initialize the memory manager 
 */
int mm_init(void) 
{
	/* Create the initial empty heap */
	maxheight = 0;
	srand(time(NULL));
	size_t sz = LN*LISTSZ + 2*DSIZE;
	if ((heap_listp = mem_sbrk((sz))) == (void *)-1) 
		return -1;

	for (int i=0; i<LN; ++i){
		PUT(ADD(i*LISTSZ), 0);
		PUT(ADD(i*LISTSZ+WSIZE), 0);
	}
	void* pro = ADD(sz - DSIZE);
	new_allocate(pro, DSIZE, 1);
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

	void *pp;

	int mode = LEFT;

	pp = find_node(asize, mode);

	if (NULL != pp){
		bp = delete_from_list(pp, PTO(pp));
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

	assert(GET_A(HDRP(bp)) == 1);
	size_t size = get_size(bp);

	//printf("free %d\n", (int)size);
	
	new_node(bp, size, GET_PA(HDRP(bp)));

	void *sucb = next_bp(bp);
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

static void print_tree(void *lst){
	size_t off = GET_SIZE(lst);
	if (off == 0) return ;
	void *p = ADD(off);
	print_tree(HDRP(p));
	printf("  %d %d %lx off: %d  size: %d  ", 
			(int)GET_SIZE(HDRP(p)), (int)GET_SIZE(p),
			(long)p, (int)off, (int)get_size(p));
	print_tree(p);
}

static void print_list(void *lst){
	printf("list: %d\n", get_ID(lst));
	print_tree(lst);
	printf("\n");
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
		print_list(get_list_byID(i));
	}
	//printf("\n%d %d %d   max_choice:%d\n", cntL, cntR, cntM, max_choice);
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

	void *nepi = next_bp(bp);
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
	size_t next_alloc = GET_A(HDRP(next_bp(bp)));
	size_t size = get_size(bp);
	void *nextb, *prevb;

	if (prev_alloc && next_alloc) {            /* Case 1 */
		return bp;
	}

	else if (prev_alloc && !next_alloc) {      /* Case 2 */
		nextb = next_bp(bp);
		size += get_size(nextb);
		delete_node(nextb);
		new_node(bp, size, GET_PA(HDRP(bp)));
	}

	else if (!prev_alloc && next_alloc) {      /* Case 3 */
		/* prevb is unit when prevb's A is 1 */
		prevb = prev_bp(bp);
		size += get_size(prevb);
		delete_node(prevb);
		bp = prevb;
		new_node(bp, size, GET_PA(HDRP(bp)));
	}

	else {                                     /* Case 4 */
		nextb = next_bp(bp);
		delete_node(nextb);
		size += get_size(nextb);
		prevb = prev_bp(bp);
		delete_node(prevb);
		size += get_size(prevb);
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
	size_t csize = get_size(bp);   
	size_t dsize = csize - asize;

	if (dsize == 0){
		new_allocate(bp, asize, GET_PA(HDRP(bp)));
		void *nb = next_bp(bp);
		SET_PA(HDRP(nb), 1);
		return bp;
	}

	/*
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
	*/

	mode = LEFT;

	if (mode == LEFT){
		new_allocate(bp, asize, GET_PA(HDRP(bp)));
		void *nb = next_bp(bp);
		new_node(nb, dsize, 1);
		insert_node(nb);
		return bp;
	}
	else if (mode == RIGHT){
		new_node(bp, dsize, GET_PA(HDRP(bp)));
		insert_node(bp);
		void *nb = next_bp(bp);
		new_allocate(nb, asize, 0);
		SET_PA(HDRP(next_bp(nb)), 1);
		return nb;
	}

	return NULL;
}

