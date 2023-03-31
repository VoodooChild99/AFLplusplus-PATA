#ifndef __AFL_LLVM_PATA_H__
#define __AFL_LLVM_PATA_H__

#ifdef __cplusplus
extern "C" {
#endif

#define PATA_KIND_CMP     0
#define PATA_KIND_SWITCH  1
#define PATA_KIND_CALL    2

#define PATA_CALL_MEMCMP    0
#define PATA_CALL_STRCMP    1
#define PATA_CALL_STRNCMP   2
#define PATA_CALL_STRSTR    3 
#define PATA_CALL_MEMMEM    4

#define PATA_OP_INC     0
#define PATA_OP_DEC     1
#define PATA_OP_KEEP    2

#define PATA_MAP_HEADER   (3 * sizeof(uint32_t))
#define PATA_FILTER_ALL   (0xFFFFFFFF)
#define PATA_FILTER_NONE  (0xFFFFFFFE)


#include <stdint.h>

typedef struct ConstraintVariable {
  // case values for SWITCH
  void *opaque;
  /* block features */
  uint32_t *bf;
  uint32_t num_bf;
  /* pattern feature and operand feature */
  // CMP, SWITCH or CALL
  uint8_t kind;
  // CMP:    predicate
  // CALL:   function name
  // SWITCH: lsb of number of cases for SWITCH
  uint8_t operation;
  // size of the operands
  uint8_t size;
  // CMP:    if rhs or lhs is a constant
  // CALL:   reserved
  // SWITCH: msb of number of cases for SWITCH
  uint8_t misc;
}__attribute__((packed)) ConstraintVariable;

struct afl_forkserver;
void patalog_exec_child(struct afl_forkserver *fsrv, char **argv);

#ifdef __cplusplus
}
#endif

#endif