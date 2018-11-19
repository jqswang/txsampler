#ifndef _SHADOWMEMORY_H
#define _SHADOWMEMORY_H

#include <sys/mman.h>
/* infrastructure for shadow memory */
/* MACROs */
// 64KB shadow pages
#define PAGE_OFFSET_BITS (16LL)
#define PAGE_OFFSET(addr) ( addr & 0xFFFF)
#define PAGE_OFFSET_MASK ( 0xFFFF)

#define PAGE_SIZE (1 << PAGE_OFFSET_BITS)

// 2 level page table
#define PTR_SIZE (sizeof(void *))
#define LEVEL_1_PAGE_TABLE_BITS  (20)
#define LEVEL_1_PAGE_TABLE_ENTRIES  (1 << LEVEL_1_PAGE_TABLE_BITS )
#define LEVEL_1_PAGE_TABLE_SIZE  (LEVEL_1_PAGE_TABLE_ENTRIES * PTR_SIZE )

#define LEVEL_2_PAGE_TABLE_BITS  (12)
#define LEVEL_2_PAGE_TABLE_ENTRIES  (1 << LEVEL_2_PAGE_TABLE_BITS )
#define LEVEL_2_PAGE_TABLE_SIZE  (LEVEL_2_PAGE_TABLE_ENTRIES * PTR_SIZE )

#define LEVEL_1_PAGE_TABLE_SLOT(addr) (((addr) >> (LEVEL_2_PAGE_TABLE_BITS + PAGE_OFFSET_BITS)) & 0xfffff)
#define LEVEL_2_PAGE_TABLE_SLOT(addr) (((addr) >> (PAGE_OFFSET_BITS)) & 0xFFF)

#define SHADOWDATATYPE_BYTE unsigned long
#define SHADOWDATATYPE_CACHELINE uint64_t

#define CACHELINE(addr) (addr >> 6) //64 bytes per cache line

#define GET_WRITE_BIT(shadow_data) (shadow_data >> 63) //the most significant bit is the write bit
#define GET_TID(shadow_data) (shadow_data & ((1UL << 63) - 1))

#define COMPOSE_SHADOW_DATA(tid, isWrite) ( tid | ((uint64_t)isWrite << 63))

// All globals
//#define MAX_FILE_PATH   (200)
//#define MAX_DEAD_CONTEXTS_TO_LOG (4000)
//#define MAX_LOG_NUM (110)
//#define SAMPLE_PERIOD (1000000)
//#define STOP_PERIOD (1000000000)
//#define VALUE_N (10)


uint8_t ** gL1PageTable[LEVEL_1_PAGE_TABLE_SIZE];
uint8_t ** gL1CachePageTable[LEVEL_1_PAGE_TABLE_SIZE];


/* helper functions for shadow memory */
inline uint8_t* GetShadowBaseAddress_TableByte(uint64_t address) {
    uint8_t *shadowPage;
    uint8_t ***l1Ptr = &gL1PageTable[LEVEL_1_PAGE_TABLE_SLOT(address)];
    if(*l1Ptr == 0) {
        //*l1Ptr = (uint8_t **) calloc(1, LEVEL_2_PAGE_TABLE_SIZE);
        *l1Ptr = (uint8_t **) hpcrun_malloc(LEVEL_2_PAGE_TABLE_SIZE);
        memset(*l1Ptr, 0, LEVEL_2_PAGE_TABLE_SIZE);
        shadowPage = (*l1Ptr)[LEVEL_2_PAGE_TABLE_SLOT(address)] =  (uint8_t *) mmap(0, PAGE_SIZE * sizeof(SHADOWDATATYPE_BYTE), PROT_WRITE | PROT_READ, MAP_NORESERVE | MAP_PRIVATE | MAP_ANONYMOUS, 0, 0);
    	//memset(shadowPage, 0, PAGE_SIZE * sizeof(SHADOWDATATYPE_BYTE));
    }
    else if((shadowPage = (*l1Ptr)[LEVEL_2_PAGE_TABLE_SLOT(address)]) == 0 ){
        shadowPage = (*l1Ptr)[LEVEL_2_PAGE_TABLE_SLOT(address)] =  (uint8_t *) mmap(0, PAGE_SIZE * sizeof(SHADOWDATATYPE_BYTE), PROT_WRITE | PROT_READ, MAP_NORESERVE | MAP_PRIVATE | MAP_ANONYMOUS, 0, 0);
    	//memset(shadowPage, 0, PAGE_SIZE * sizeof(SHADOWDATATYPE_BYTE));
    }
    return shadowPage;
}
inline uint8_t* GetShadowBaseAddress_TableCacheLine(uint64_t address) {
    uint8_t *shadowPage;
    uint8_t ***l1Ptr = &gL1CachePageTable[LEVEL_1_PAGE_TABLE_SLOT(address)];
    if(*l1Ptr == 0) {
        //*l1Ptr = (uint8_t **) calloc(1, LEVEL_2_PAGE_TABLE_SIZE);
        *l1Ptr = (uint8_t **) hpcrun_malloc(LEVEL_2_PAGE_TABLE_SIZE);
        memset(*l1Ptr, 0, LEVEL_2_PAGE_TABLE_SIZE);
        shadowPage = (*l1Ptr)[LEVEL_2_PAGE_TABLE_SLOT(address)] =  (uint8_t *) mmap(0, PAGE_SIZE * sizeof(SHADOWDATATYPE_CACHELINE), PROT_WRITE | PROT_READ, MAP_NORESERVE | MAP_PRIVATE | MAP_ANONYMOUS, 0, 0);
    	//memset(shadowPage, 0, PAGE_SIZE * sizeof(SHADOWDATATYPE_CACHELINE));
    }
    else if((shadowPage = (*l1Ptr)[LEVEL_2_PAGE_TABLE_SLOT(address)]) == 0 ){
        shadowPage = (*l1Ptr)[LEVEL_2_PAGE_TABLE_SLOT(address)] =  (uint8_t *) mmap(0, PAGE_SIZE * sizeof(SHADOWDATATYPE_CACHELINE), PROT_WRITE | PROT_READ, MAP_NORESERVE | MAP_PRIVATE | MAP_ANONYMOUS, 0, 0);
    	//memset(shadowPage, 0, PAGE_SIZE * sizeof(SHADOWDATATYPE_CACHELINE));
    }
    return shadowPage;
}


/* get the stored data from the shadow memory and store the new  */
inline SHADOWDATATYPE_BYTE getValueAndStore_byte(uint64_t addr, unsigned long tid, unsigned short store_flag){
    uint8_t* status =GetShadowBaseAddress_TableByte(addr);
    SHADOWDATATYPE_BYTE *prevAddr = (SHADOWDATATYPE_BYTE *)(status + PAGE_OFFSET(addr) * sizeof(SHADOWDATATYPE_BYTE));
    SHADOWDATATYPE_BYTE ret_value = *prevAddr;
    if (store_flag != 0){
      *prevAddr = (SHADOWDATATYPE_BYTE) tid;
    }
    return ret_value;
}

inline SHADOWDATATYPE_CACHELINE getValueAndStore_cacheline(uint64_t addr, unsigned long tid, unsigned short store_flag){
    uint8_t* status = GetShadowBaseAddress_TableCacheLine(CACHELINE(addr));
    SHADOWDATATYPE_CACHELINE *prevAddr = (SHADOWDATATYPE_CACHELINE *)(status + PAGE_OFFSET(CACHELINE(addr)) * sizeof(SHADOWDATATYPE_CACHELINE));
    SHADOWDATATYPE_CACHELINE ret_value = *prevAddr;
    if (store_flag != 0){
      *prevAddr = (SHADOWDATATYPE_CACHELINE) tid;
    }
    return ret_value;
}

int incrementShadowMetric(uint64_t addr, unsigned long tid, unsigned short isWrite){
	//add into cache line map

  unsigned long cacheline_ret = getValueAndStore_cacheline(addr, COMPOSE_SHADOW_DATA(tid, isWrite), 1);

	//add into byte map
	unsigned long byte_ret = getValueAndStore_byte(addr, COMPOSE_SHADOW_DATA(tid, isWrite), 1);

	//False sharing: 1. another thread has touched the cache line; 2. the touched byte is NOT accessed by another thread

  if (cacheline_ret == 0) { //the cache line first-time touched
    return 0;
  }

  if (GET_WRITE_BIT(cacheline_ret) == 0 && isWrite == 0){ //both READ, no false sharing
    return 0;
  }
  if ( (GET_TID(cacheline_ret) != tid) && ( byte_ret == 0 || GET_TID(byte_ret) == tid) ) {
		return 1;
	}
	return 0;
}


#endif
