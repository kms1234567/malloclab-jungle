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
    "jungle",
    /* First member's full name */
    "kms",
    /* First member's email address */
    "asd",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* basic constants and macros (기본 상수 및 매크로)*/
#define WSIZE 4					/* 워드크기 (header/footer size) (bytes) */
#define DSIZE 8					/* 더블 워드 크기 (bytes) */
#define CHUNKSIZE (1<<12)		/* 초기 가용 블록과 힙 확장을 위한 기본크기 (2**12) */
#define LISTLIMIT 20            /* list의 limit 값을 설정해준다. */

#define MAX(x,y) ((x) > (y) ? (x): (y))

/* 해당 size(전체크기(헤더풋터포함))와 할당비트를 통합해서 header와 footer에 저장할 수 있는 값을 리턴한다 */
#define PACK(size, alloc) ((size) | (alloc))

/*	GET매크로는 인자 p가 참조하는 워드를 읽어서 리턴한다. 인자 p는 대개 (void*) 포인터이기 때문에 직접적으로 역참조할 수 없어서 캐스팅한다. 
	PUT매크로는 인자 p가 가리키는 워드에 val을 저장한다. */
#define GET(p)			(*(unsigned int *)(p))
#define PUT(p, val)		(*(unsigned int *)(p) = (val))

// GET_SIZE와 GET_ALLOC 매크로는 각각 주소 p에 있는 header/footer의 size와 할당 비트를 리턴한다.
#define GET_SIZE(p)		(GET(p) & ~0x7)		// 0x7 은 이진수로 111 이기 때문에 ~ 연산(000)을 통해 하위 3비트(header/footer의 할당 비트)를 0처리한 것을 볼 수 있다.
#define GET_ALLOC(p)	(GET(p) & 0x1)

/* 블록 포인터 bp(payload 시작점)가 주어질 때, 각각 매크로는 header 또는 footer를 가리키는 포인터를 리턴한다. */
#define HDRP(bp) ((char*)(bp) - WSIZE)
#define FTRP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* 다음과 이전 블록의 블록 포인터를 각각 리턴한다. */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char*)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char*)(bp) - DSIZE)))

/* 가용 블록의 주소값(포인터의 주소값)을 저장하므로 이중포인터로 읽어들인 다음 가리키는 값을 리턴한다. */
#define PRED_P(bp)  (*(char **)(bp))
#define SUCC_P(bp)  (*(char **)((bp)+WSIZE))

/* 추가 선언 */
static void* heap_listp;
static void* segregation_list[LISTLIMIT]; // 각 사이즈 크기의 첫 번째 가용 블록포인터를 저장함.

static void* extend_heap(size_t words);
static void* coalesce(void* bp);
static void* find_fit(size_t asize);
static void place(void* bp, size_t asize);
static void remove_block(void *bp);
static void insert_block(void* bp, size_t size);

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
// 해당 숫자를 최적의 8의 배수로 만듦
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* 
 * find_fit - bp는 앞 가용리스트로 계속 옮겨간다. 해당 가용리스트의 size가 asize로 충분히 들어간다면, bp를 반환한다.
 */
static void* find_fit(size_t asize)
{
    void* bp;
    
    int list = 0;
    size_t search_size= asize;

    while (list < LISTLIMIT){
        if((list == LISTLIMIT-1) || (search_size<=1)&&(segregation_list[list] != NULL)){
            bp = segregation_list[list];       

            while((bp != NULL) && (asize > GET_SIZE(HDRP(bp)))){
                bp = SUCC_P(bp);
            }
            if (bp != NULL){
                return bp;
            }
        }
        search_size >>= 1;
        list ++;
    }
    return NULL;
}

/*
 * insert_block - 현재 블록의 사이즈를 찾은 후, 해당 사이즈리스트에서 어디에 위치해야하는지 탐색 후, 연결한다. (오름차순)
 * 1. (앞:!=NULL, 뒤:!=NULL, 중간) 2. (앞!=NULL, 뒤==NULL, 처음) 3. (앞==NULL, 뒤!=NULL, 마지막) 4. (앞==NULL, 뒤==NULL, 완전처음)
 */
static void insert_block(void* bp, size_t size){
    size_t asize = size;
    int list = 0;
    void* search_ptr;
    void* insert_ptr = NULL;

    while((list < LISTLIMIT-1) && (asize > 1)){
        asize >>= 1;
        list++;
    }

    search_ptr = segregation_list[list];
    while((search_ptr != NULL) && (size>(GET_SIZE(HDRP(search_ptr))))){
        insert_ptr = search_ptr;
        search_ptr = SUCC_P(search_ptr);
    }

    if (search_ptr != NULL){
        if(insert_ptr != NULL){
            PRED_P(bp) = insert_ptr;
            SUCC_P(bp) = search_ptr;
            SUCC_P(insert_ptr) = bp;
            PRED_P(search_ptr) = bp; 
        }
        else{
            PRED_P(bp) = NULL;
            SUCC_P(bp) = search_ptr;
            PRED_P(search_ptr) = bp;
            segregation_list[list] = bp;
        }
    }else{
        if(insert_ptr != NULL){
            SUCC_P(bp) = NULL;
            PRED_P(bp) = insert_ptr;
            SUCC_P(insert_ptr) = bp;
        }
        else{
            PRED_P(bp) = NULL;
            SUCC_P(bp) = NULL;
            segregation_list[list] = bp;
        }
    }
    return; 
}

/*
 * remove_block - 해당 bp가 어느 사이즈 리스트에 있는지 검색 후, 해당 블록의 연결을 끊은 후, 갱신한다.
 * (case) 1. 현재 블록이 중간일 때 2. 현재 블록이 처음일 때 3. 현재 블록이 마지막일 때 4. 애초에 나 하나만 있었을 때
 */
static void remove_block(void *bp)
{
    int list = 0;
    size_t size = GET_SIZE(HDRP(bp));

    while((list < LISTLIMIT-1) && (size > 1)){
        size >>= 1;
        list++;
    }

    if (SUCC_P(bp) != NULL){
        if (PRED_P(bp) != NULL){
            SUCC_P(PRED_P(bp)) = SUCC_P(bp);
            PRED_P(SUCC_P(bp)) = PRED_P(bp);
        }
        else{
            PRED_P(SUCC_P(bp)) = NULL;
            segregation_list[list] = SUCC_P(bp);
        }
    }
    else{
        if(PRED_P(bp) != NULL){
            SUCC_P(PRED_P(bp)) = NULL;
        }
        else{
            segregation_list[list] = NULL;
        }
    }
    return;
}

/*
 * place - 해당 bp에 asize를 넣고, 헤더와 풋터를 갱신한다. 또한, 남은 블록이 최소블록(16)과 같거나 큰 경우에는 분할한다.
 * 최소블록이 16인 이유는 헤더+풋터 = 8byte이므로, 데이터가 1byte만 들어와도 패딩과 함께 16byte가 되어야 한다.
 */
static void place(void* bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    remove_block(bp);
    if ((csize - asize) >= 2*(DSIZE)){
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
        coalesce(bp);
    }
    else{
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
    
}

/*
 * coalesce - 해당 블록포인터가 가리키는 블록을 기준으로 가용공간을 연결하는 함수
 */
static void* coalesce(void* bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));     // 이전 블록이 할당(1)되어 있는지
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));     // 다음 블록이 할당(1)되어 있는지
    size_t size = GET_SIZE(HDRP(bp));                       // 현재 블록의 size(크기)

    /* case 1 : 이전 블록과 다음 블록 모두 할당되어있을 경우 */
    if (prev_alloc && next_alloc){
        insert_block(bp, size);
        return bp;
    }

    /* case 2 : 이전 블록이 할당, 다음 블록이 가용상태일 떄 */
    if (prev_alloc && !next_alloc){
        remove_block(NEXT_BLKP(bp));

        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    /* case 3 : 이전 블록이 가용, 다음 블록이 할당상태일 때 */
    else if (!prev_alloc && next_alloc){
        remove_block(PREV_BLKP(bp));
        size += GET_SIZE(FTRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    /* case 4 : 이전 블록, 다음 블록 모두 가용상태일 때 */
    else if (!prev_alloc && !next_alloc){
        remove_block(PREV_BLKP(bp));
        remove_block(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    insert_block(bp, size);
    return bp;
}

/* 
 * extend_heap - 받은 크기를 정렬 size로 바꾼 후, 추가적인 힙 공간을 요청하는 함수 
 */
static void* extend_heap(size_t words)
{
    char* bp;
    size_t size;            

    size = (words % 2) ? (words + 1)*WSIZE : words*WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1) 
        return NULL;
    
    PUT(HDRP(bp), PACK(size, 0));        
    PUT(FTRP(bp), PACK(size, 0));            
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));   
    return coalesce(bp);
}

/* 
 * mm_init         - initialize the malloc package.
 * segregated list - 정해진 사이즈로 (여기서는 끝 사이즈가 모두 2의 지수승을 나타낸다.) 가용 리스트를 연결한다. 
 */
int mm_init(void)
{
    for(int list=0; list<LISTLIMIT; list++){
        segregation_list[list] = NULL;      
    }

    if((heap_listp = mem_sbrk(4*WSIZE)) == (void*)-1){
        return -1;
    }
    PUT(heap_listp, 0);                             
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));  
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));       
    PUT(heap_listp + (3*WSIZE), PACK(0,1));             
    
    heap_listp += 2 * WSIZE;                               

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL){
        return -1;
    }

    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 * Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char* bp;

    if (size == 0){
        return NULL;
    }

    if(size <= DSIZE){
        asize = 2*DSIZE;
    }
    else{
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE); 
    }

    if((bp = find_fit(asize)) != NULL){
        place(bp, asize);
        return bp;
    }

    extendsize =MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL){
        return NULL;
    }
    place(bp, asize);
    return bp;
}   

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));    
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);                 
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
    copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize); 
    mm_free(oldptr);
    return newptr;
}