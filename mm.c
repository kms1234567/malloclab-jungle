/*d
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
    "jungle-Aclass-second",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* basic constants and macros (기본 상수 및 매크로)*/
#define WSIZE 4					/* 워드크기 (header/footer size) (bytes) */
#define DSIZE 8					/* 더블 워드 크기 (bytes) */
#define CHUNKSIZE (1<<12)		/* 초기 가용 블록과 힙 확장을 위한 기본크기 (2**12) */

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

/* 추가 선언 */
static void* heap_listp;
// static void* last_bp;

static void* extend_heap(size_t words);
static void* coalesce(void* bp);
static void* find_fit(size_t asize);
static void place(void* bp, size_t asize);

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
// 해당 숫자를 최적의 8의 배수로 만듦
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* 
 * find_fit(first_fit) - 힙을 처음부터 검색하면서 해당 size가 들어갈 수 있는 공간을 찾으면 바로 할당함
 * 
 */
static void* find_fit(size_t asize)
{
    void* bp;
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
            return bp;
        }
    }
    return NULL;
}

/*
 * place - 해당 bp에 asize를 넣고, 헤더와 풋터를 갱신한다. 또한, 남은 블록이 최소블록(16)과 같거나 큰 경우에는 분할한다.
 * 최소블록이 16인 이유는 헤더+풋터 = 8byte이므로, 데이터가 1byte만 들어와도 패딩과 함께 16byte가 되어야 한다.
 * 만약 남은 블록이 최소크기보다 작다면, 분할할 이유가 없으므로 해당 전체블록을 할당한다.
 */
static void place(void* bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= 2*(DSIZE)){
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
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
    size_t size = GET_SIZE(HDRP(bp));                             // 현재 블록의 size(크기)

    /* case 1 : 이전 블록과 다음 블록 모두 할당되어있을 경우 */
    if (prev_alloc && next_alloc){
        return bp;
    }

    /* case 2 : 이전 블록이 할당, 다음 블록이 가용상태일 떄 */
    else if (prev_alloc && !next_alloc){
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        // PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); 왜 이게 아닐까;;
    }

    /* case 3 : 이전 블록이 가용, 다음 블록이 할당상태일 때 */
    else if (!prev_alloc && next_alloc){
        size += GET_SIZE(FTRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    /* case 4 : 이전 블록, 다음 블록 모두 가용상태일 때 */
    else{
        size += GET_SIZE(FTRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

/* 
 * extend_heap - 받은 크기를 정렬 size로 바꾼 후, 추가적인 힙 공간을 요청하는 함수 
 */
static void* extend_heap(size_t words)
{
    char* bp;
    size_t size;            // 실제로 넣을 size

    /* 정렬을 위해 홀수는 짝수로 만든 후, (요청할 때 size를 WSIZE 크기만큼 나눠서 주었기 때문에) WSIZE를 곱해준다. */
    size = (words % 2) ? (words + 1)*WSIZE : words*WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)   // mem_sbrk(size)로 해당 size만큼 힙크기를 늘려달라고 요청한다.
        return NULL;
    
    PUT(HDRP(bp), PACK(size, 0));            // 해당 사이즈만큼 가용블록의 헤더와 풋터를 갱신한다.
    PUT(FTRP(bp), PACK(size, 0));            
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));    // 에필로그 블록을 끝쪽으로 갱신한다.

    // 가용공간들을 연결한다. (coalesce)
    return coalesce(bp);
}

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if((heap_listp = mem_sbrk(4*WSIZE)) == (void*)-1){
        return -1;
    }
    PUT(heap_listp, 0);                             // 미사용 패딩 워드
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));    // 프롤로그 블록 헤더
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));    // 프롤로그 블록 풋터
    PUT(heap_listp + (3*WSIZE), PACK(0,1));         // 에필로그 블록
    heap_listp += (2*WSIZE);                        // heap_listp는 프롤로그 헤더와 풋터 사이를 가리킨다.

    // 비어있는 힙을 특정 크기로 가용공간을 확장시킨다. (extend_heap)
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL){
        return -1;
    }

    return 0;
}


/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    // int newsize = ALIGN(size + SIZE_T_SIZE);
    // void *p = mem_sbrk(newsize);        
    // if (p == (void *)-1)
	// return NULL;
    // else {
    //     *(size_t *)p = size;
    //     return (void *)((char *)p + SIZE_T_SIZE);
    // }
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
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE); // 딱 맞는 (8의배수) size가 왔을 때를 대비해서 DSIZE-1을 더함.
    }

    /* 해당 size에 맞는 빈 가용블록을 찾는다. */
    if((bp = find_fit(asize)) != NULL){
        place(bp, asize);
        return bp;
    }

    /* 해당 size에 맞는 가용블록이 없으므로, 메모리를 더 가져와 추가된 힙에 block을 위치시킨다. */
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
    size_t size = GET_SIZE(HDRP(ptr));        // 현재 블록의 size를 받고, 헤더와 풋터를 가용상태로 갱신한다.
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);                      // 이전 블록 혹은, 다음 블록을 확인해 가용상태라면 연결한다.
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
    // copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}