/* 
   林涛 1600012773
   使用分离双向链表，插入新空闲快时放到链表尾部,
   分配块时从头开始找到第一个适配的空闲块，
   找不到则扩充堆的大小
   块的大小按照2的幂分类
   放置块时放在低地址端
   采用立即合并

   已分配、空闲块的最小大小都是8字节，格式如下：
  
           header      | bp         | NXP        |    偶数个字        | footer
           29位      a |          u |                                            u 
   已分配：
           size * pa 1 | ********** | *******(这一段可以没有) ********|
   
   至少16个字节的空闲块：
           prev * pa 0 | next * * 0 | size * * * | ********* ******** | size * * 0 
   
   8个字节的空闲块：
           prev * pa 0 | next * * 1 |
   
   pa 表示前一块是否为已分配块, u表示这个空闲块是否是8字节的

   一个链表需要用两个字记录头和尾，一共有15个链表，这些信息顺序储存在堆的最前面
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
#define GET_SIZE(p)  (GET(p) & ~0x7)       // 取高29位             
#define GET_A(p)  	(GET(p) & 0x1)
#define GET_PA(p) 	((GET(p) & 0x2) != 0)
#define GET_U(p)    (GET(p) & 0x1)

#define SET_SIZE(p, v)  (*(unsigned int*)(p) = (GET(p) & 0x7) | (v))
#define SET_A(p, v)   (*(unsigned int*)(p) = (GET(p) & ~0x1) | (v))
#define SET_PA(p,v)   (*(unsigned int*)(p) = (GET(p) & ~0x2) | ((v)<<1))
#define SET_U(p, v)  (*(unsigned int*)(p) = (GET(p) & ~0x1) | ((v)))

/* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */  

#define LN 15   /* 链表的个数 */

#define HPA     	((char*)heap_listp)
#define OFF(bp) 	((char *)bp - HPA)           // 相对堆基址的偏移
#define ADD(off) 	(HPA + (off))                // 真实地址
#define PTO(pp) 	(ADD(GET_SIZE(pp)))          // 真实地址pp指向的真实地址
#define NXP(bp) 	((char *)bp + WSIZE)         // 真实地址pp的下一个字的地址
#define NXO(bp) 	(GET_SIZE(NXP(bp)))          // pp的下一个字的值的高29位
#define NXT(bp) 	(PTO(NXP(bp)))

/* Function prototypes for internal helper routines */

inline size_t get_size(void *bp);
inline void *next_bp(void *bp);
inline void *prev_bp(void *bp);

static void *extend_heap(size_t words);
static void *place(void *bp, size_t asize);
static void *coalesce(void *bp);

static void *get_list(size_t sz);

static void insert_to_list(void *lst, void *bp);
static void insert_node(void *bp);

static void *locate_in_list(void *lst, void *bp);

static void *delete_from_list(void *lst, void *bp);
static void *delete_node(void *bp);

static void *find_node(size_t sz);
static void *find_in_list(void *lst, size_t sz);

inline void *new_node(void *nb, size_t sz, size_t pa);
inline void *new_allocate(void *nb, size_t sz, size_t pa);

// 求块bp的大小，分已分配、非8位的、8位的讨论
inline size_t get_size(void *bp){
	size_t a = GET_A(HDRP(bp));
	size_t u = GET_U(bp);
	if (a == 0 && u == 0) return GET_SIZE(NXP(bp));
	if (a == 0 && u == 1) return DSIZE;
	return GET_SIZE(HDRP(bp));
}

// 求下一块的地址
inline void *next_bp(void *bp){
	return (void*)((char *)bp + get_size(bp));
}

// 求前一块的地址, 只有前一块是空闲块时才有意义
inline void *prev_bp(void *bp){
	size_t u = GET_U(HDRP(HDRP(bp)));
	size_t sz = 0;
	if (u == 0) sz = GET_SIZE(HDRP(HDRP(bp)));
	if (u == 1) sz = DSIZE;
	return (void *)((char *)bp - sz);
}

// 在bp位置新建一个空闲块
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

// 在bp位置新建一个已分配块
inline void *new_allocate(void *nb, size_t sz, size_t pa){
	SET_SIZE(HDRP(nb), sz);
	SET_A(HDRP(nb), 1);
	SET_PA(HDRP(nb), pa);
	return nb;
}

// 分组策略
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

// 将大小sz映射到链表的ID
inline int get_listID(size_t sz){
	return power2(sz);
}

// 通过链表的位置计算链表的ID，
static int get_ID(void *lst){
	return OFF(lst) / LISTSZ;
}

static void *get_list_byID(int id){
	return ADD(id*LISTSZ);
}

// 通过大小sz确定链表，链表用保存头部信息的字的地址表示
static void *get_list(size_t sz){
	return get_list_byID(get_listID(sz));
}

// 寻找大小为少为sz的空闲块 
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
	while (GET_SIZE(pp) != 0){
		void *bp = PTO(pp);
		if (get_size(bp) >= sz) return pp;
		pp = bp;
	}
	return NULL;
}

// 将空闲块bp根据他的大小插入到合适的链表中
void insert_node(void *bp){
	size_t sz = get_size(bp);
	void *lst = get_list(sz);
	insert_to_list(lst, bp);
}

void insert_to_list(void *lst, void *bp){
	size_t tail_off = NXO(lst);           // 原来的尾
	size_t cur_off = OFF(bp);
	SET_SIZE(HDRP(bp), tail_off);         // bp的prev指向原来的尾
	SET_SIZE(bp, 0);                      // bp的next为0
	SET_SIZE(NXP(lst), cur_off);          // 更新链表的尾
	if (tail_off)                 // 原来的链表非空，更新原来的尾的后继
		SET_SIZE(ADD(tail_off), cur_off);
	else                          // 原来的链表为空，更新头
		SET_SIZE(lst, cur_off);
}

// 在链表lst中确定块bp的位置
void *locate_in_list(void *lst, void *bp){
	void *pp = lst;
	while (GET_SIZE(pp) != 0){
		if (PTO(pp) == bp)
			return pp;
		pp = PTO(pp);
	}
}

// 从合适的链表中删掉块bp, 并返回bp自己
void *delete_node(void *bp){
	size_t sz = get_size(bp);
	void *lst = get_list(sz);
	return delete_from_list(lst, bp);
}

void *delete_from_list(void *lst, void *bp){
	size_t pre_off = GET_SIZE(HDRP(bp));
	size_t nex_off = GET_SIZE(bp);
	if (pre_off)
		SET_SIZE(ADD(pre_off), nex_off);
	else
		SET_SIZE(lst, nex_off);
	if (nex_off)
		SET_SIZE(HDRP(ADD(nex_off)), pre_off);
	else
		SET_SIZE(NXP(lst), pre_off);
	return bp;
}

/* 
 * mm_init - Initialize the memory manager 
 * 初始的结构是：
 * | L0 | L1 | L2 | ... ... | L14 |  pro|pro epi|
 */
int mm_init(void) 
{
	/* Create the initial empty heap */
	size_t sz = LN*LISTSZ + 2*DSIZE;
	if ((heap_listp = mem_sbrk((sz))) == (void *)-1) 
		return -1;

	// 初始化链表
	for (int i=0; i<LN; ++i){
		PUT(ADD(i*LISTSZ), 0);
		PUT(ADD(i*LISTSZ+WSIZE), 0);
	}
	// 序言块和结语块
	void* pro = ADD(sz - DSIZE);
	new_allocate(pro, DSIZE, 1);
	void* epi = ADD(sz);
	new_allocate(epi, 0, 1);

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

	void *pp = find_node(asize);

	if (NULL != pp){
		bp = delete_node(PTO(pp));
	}else{
		extendsize = MAX(asize, CHUNKSIZE);
		if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
			return NULL;
	}

	return place(bp, asize);
} 

/* 
 * free - Free a block 
 */
void mm_free(void *bp)
{
	if (bp == 0) 
		return;

	size_t size = get_size(bp);

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

static void print_list(void *lst){
	printf("list: %d\n", get_ID(lst));
	printf("\n");
}

static int check_list(int id){
	void *lst = get_list_byID(id);
	void *pp = lst;
	size_t pre_off = 0;
	int cnt = 0;
	while (GET_SIZE(pp)){
		++cnt;
		void *bp = PTO(pp);

		//check pointers and head
		assert(GET_SIZE(HDRP(bp)) == pre_off);

		//check tail
		if (GET_SIZE(bp) == 0)
			assert(NXO(lst) == OFF(bp));

		//check size range
		size_t sz = get_size(bp);
		assert(get_listID(sz) == id);

		pre_off = OFF(bp);
		pp = bp;
	}

	return cnt;
}

/* 
 * mm_checkheap - Check the heap for correctness. Helpful hint: You
 *                can call this function using mm_checkheap(__LINE__);
 *                to identify the line number of the call site.
 */
void mm_checkheap(int lineno)  
{ 
	lineno = lineno; // keep gcc happy
	/*static int cnt = 0;
	++cnt;
	if (cnt % 100 != 0) return ;
*/
	// check prologue
	void *pro = ADD(LN*LISTSZ + DSIZE);
	assert(get_size(pro) == DSIZE);
	assert(GET_A(HDRP(pro)) == 1);
	size_t pa = 1;
	int cnt_free = 0;
	int cnt_a = 0;

	// check each block
	void *bp = next_bp(pro);
	size_t sz;
	while ( (sz = get_size(bp)) != 0){
		assert(pa == GET_PA(HDRP(bp)));
		pa = GET_A(HDRP(bp));
		if (pa){
			++cnt_a;
		}else{
			++cnt_free;
			size_t u = GET_U(bp);
			if (u == 1){
				assert(sz == DSIZE);
			}else{
				void *ftrp = bp + sz - DSIZE;
				assert(GET_SIZE(ftrp) == sz);
				assert(GET_U(ftrp) == 0);
			}
		}
		bp = next_bp(bp);
	}

	//check epilogue
	assert(pa == GET_PA(HDRP(bp)));
	assert(GET_A(HDRP(bp)) == 1);

	//check the consistency between lists and blocks
	int cnt_list = 0;
	for (int id=0; id<LN; ++id){
		cnt_list += check_list(id);
	}
	assert(cnt_list == cnt_free);
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
static void *place(void *bp, size_t asize)
{
	size_t csize = get_size(bp);   
	size_t dsize = csize - asize;

	void *nb;

	if (dsize == 0){
		new_allocate(bp, asize, GET_PA(HDRP(bp)));
		nb = next_bp(bp);
		SET_PA(HDRP(nb), 1);
		return bp;
	}
	
	new_allocate(bp, asize, GET_PA(HDRP(bp)));
	nb = next_bp(bp);
	new_node(nb, dsize, 1);
	insert_node(nb);
	return bp;
}

