#include <stdio.h>
#include <stdlib.h>
#include "util.h"
#include "gc.h"

extern int our_code_starts_here(int* HEAP) asm("our_code_starts_here");
extern void error() asm("error");
extern int print(int val) asm("print");
extern int* try_gc(int* stack_top, int* first_frame, int* alloc_ptr, int bytes_needed) asm("try_gc");
extern int* HEAP_END asm("HEAP_END");
extern int* STACK_BOTTOM asm("STACK_BOTTOM");

const int ERR_COMP_NOT_NUM   = 1;
const int ERR_ARITH_NOT_NUM  = 2;
const int ERR_LOGIC_NOT_BOOL = 3;
const int ERR_IF_NOT_BOOL    = 4;
const int ERR_OVERFLOW       = 5;
const int ERR_GET_NOT_TUPLE  = 6;
const int ERR_GET_LOW_INDEX  = 7;
const int ERR_GET_HIGH_INDEX = 8;
const int ERR_INDEX_NOT_NUM  = 9;
const int ERR_CALL_NOT_FUNC  = 10;
const int ERR_CALL_BAD_ARITY = 11;
const int ERR_SET_NOT_TUPLE  = 12;
const int ERR_OUT_OF_MEMORY  = 13;

size_t HEAP_SIZE;
int* STACK_BOTTOM;
int* HEAP;
int *ALIGNED_HEAP;
int* HEAP_END;

int print(int val) {
  printHelp(stdout, val, 0);
  printf("\n");
  return val;
}

void error(int i) {
  switch (i) {
  case ERR_COMP_NOT_NUM:
    fprintf(stderr, "Error: comparison expected a number\n");
    break;
  case ERR_ARITH_NOT_NUM:
    fprintf(stderr, "Error: arithmetic expected a number\n");
    break;
  case ERR_LOGIC_NOT_BOOL:
    fprintf(stderr, "Error logic expected a boolean\n");
    break;
  case ERR_IF_NOT_BOOL:
    fprintf(stderr, "Error: if expected a boolean\n");
    break;
  case ERR_OVERFLOW:
    fprintf(stderr, "Error: Integer overflow\n");
    break;
  case ERR_GET_NOT_TUPLE:
    fprintf(stderr, "Error: get expected tuple\n");
    break;
  case ERR_SET_NOT_TUPLE:
    fprintf(stderr, "Error: set expected tuple\n");
    break;
  case ERR_GET_LOW_INDEX:
    fprintf(stderr, "Error: index too small\n");
    break;
  case ERR_GET_HIGH_INDEX:
    fprintf(stderr, "Error: index too large\n");
    break;
  case ERR_INDEX_NOT_NUM:
    fprintf(stderr, "Error: expected number for index\n");
    break;
  case ERR_CALL_NOT_FUNC:
    fprintf(stderr, "Error: tried to call a non-function\n");
    break;
  case ERR_CALL_BAD_ARITY:
    fprintf(stderr, "Error: arity mismatch in function call\n");
    break;
  default:
    fprintf(stderr, "Error: Unknown error code: %d\n", i);
  }
  exit(i);
}

/*
  Try to reserve the desired number of bytes of memory, and free garbage if
  needed.  Fail (and exit the program) if there is insufficient memory.  Does
  not actually allocate the desired number of bytes of memory; the caller
  will do that.

  Arguments:

    int* cur_stack_top - the stack pointer of the topmost stack frame of our
                         code (i.e., ESP)
    int* cur_frame - the base pointer of the topmost stack frame of our code
                     (i.e., EBP)
    int* alloc_ptr - the current top of the heap (which we store in ESI), where
                     the next allocation should occur, if possible
    int bytes_needed - the number of bytes of memory we want to allocate
                       (including padding)

  Returns:
    The new top of the heap (i.e. the new value of ESI) after garbage collection.
    Does not actually allocate bytes_needed space.

  Side effect:
    Also updates HEAP_END to point to the new end of the heap, if it's changed
*/
int* try_gc(int* cur_stack_top, int* cur_frame, int* alloc_ptr, int bytes_needed) {
  int* new_heap = (int*)calloc(HEAP_SIZE, sizeof(int));
  int* new_heap_end = new_heap + HEAP_SIZE;
  int* old_heap = HEAP;
  int* old_heap_end = HEAP_END;

  int* new_esi = NULL;

  // Abort early, if we can't allocate a new to-space
  if (new_heap == NULL) {
    fprintf(stderr, "Out of memory: could not allocate a new semispace for garbage collection");
    exit(ERR_OUT_OF_MEMORY);
  }

  new_esi = gc(STACK_BOTTOM, cur_frame, cur_stack_top, ALIGNED_HEAP, HEAP_END, new_heap);
  HEAP = new_heap;
  ALIGNED_HEAP = (int *)((unsigned int)((void *)new_heap + 7) & 0xFFFFFFF8);
  HEAP_END = new_heap_end;
  free(old_heap);

  // Note: strict greater-than is correct here: if new_esi + (bytes_needed / 4) == HEAP_END,
  // that does not mean we're *using* the byte at HEAP_END, but rather that it would be the
  // next free byte, which is still ok and not a heap-overflow.
  if (bytes_needed / 4 > HEAP_SIZE) {
    fprintf(stderr, "Allocation error: needed %d words, but the heap is only %lu words",
            bytes_needed / 4, HEAP_SIZE);
    exit(ERR_OUT_OF_MEMORY);
  } else if((new_esi + (bytes_needed / 4)) > HEAP_END) {
    fprintf(stderr, "Out of memory: needed %d words, but only %d remain after collection",
            bytes_needed / 4, (HEAP_END - new_esi));
    if (new_heap != NULL) free(new_heap);
    exit(ERR_OUT_OF_MEMORY);
  }
  else {
    return new_esi;
  }
}

int main(int argc, char** argv) {
  if(argc > 1) {
    HEAP_SIZE = atoi(argv[1]);
  }
  else {
    HEAP_SIZE = 100000;
  }
  HEAP = (int*)calloc(HEAP_SIZE, sizeof (int));
  ALIGNED_HEAP = (int *)((unsigned int)((void*)HEAP + 7) & 0xFFFFFF8);
  HEAP_END = HEAP + HEAP_SIZE;

  int result = our_code_starts_here(ALIGNED_HEAP);

  print(result);
  return 0;
}
