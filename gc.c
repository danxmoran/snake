#include <stdio.h>
#include <stddef.h>
#include "util.h"
#include "gc.h"

/*
  Copies a Snake value from the given address to the new heap,
  but only if the value is heap-allocated and needs copying.

  Arguments:
    snake_val_addr: the *address* of some Snake value, which contains a Snake value,
                    i.e. a tagged word.
                    It may or may not be a pointer to a heap-allocated value...
    heap_top: the location at which to begin copying, if any copying is needed

  Return value:
    The new top of the heap, at which to continue allocations

  Side effects:
    If the data needed to be copied, then this replaces the value at its old location
    with a forwarding pointer to its new location
 */
int* copy_if_needed(int* snake_val_addr, int* heap_top) {
  int snake_val = *snake_val_addr;
  if (!is_num(snake_val) && !is_bool(snake_val)) {
    int *heap_thing = (int *)without_tag(snake_val);
    int thing_tag = get_tag(snake_val);

    if (*heap_thing < 0) {
      // The only time the size headword will be negative is if the object
      // originally starting at that location has been copied, in which case
      // the new address will have been placed in the next word.
      *snake_val_addr = *(heap_thing + 1);
    } else {
      // If the size headword is positive, the thing hasn't been copied yet.
      int thing_size = *heap_thing + 1;
      // Store a tagged pointer to the size word at the spot in the to-space
      // where the size would be expected.
      // This is used so we can detect the original type for the allocation
      // in the to-space, since we can't rely on tagged values from the stack.
      *heap_top = (int)heap_thing + thing_tag;
      // Copy the rest of the allocation to the to-space.
      for (int i = 1; i < thing_size; i++) {
        *(heap_top + i) = *(heap_thing + i);
      }
      int new_addr = (int)heap_top + thing_tag;
      // Update the Snake value to point at the copy.
      *snake_val_addr = new_addr;
      // Store the new address in the second word of the copied allocation,
      // and multiply the size word by -1 to mark it as a forwarder.
      *(heap_thing + 1) = new_addr;
      *heap_thing = -thing_size;
      heap_top += thing_size;
      // Make sure the heap stays 8-byte aligned.
      if ((int)heap_top % 8 != 0) {
        heap_top++;
      }
    }
  }
  return heap_top;
}

/*
  Implements Cheney's garbage collection algorithm.

  Arguments:
    bottom_frame: the base pointer of our_code_starts_here, i.e. the bottommost Snake frame
    top_frame: the base pointer of the topmost Snake stack frame
    top_stack: the current stack pointer of the topmost Snake stack frame
    from_start and from_end: bookend the from-space of memory that is being compacted
    to_start: the beginning of the to-space of memory

  Returns:
    The new location within to_start at which to allocate new data
 */
int* gc(int* bottom_frame,
        int* top_frame,
        int* top_stack,
        int* from_start,
        int* from_end,
        int* to_start) {

  int *to_end = to_start;
  int *cur_word = top_stack;
  int *next_ebp = top_frame;

  while (cur_word < bottom_frame) {
    if (cur_word == next_ebp) {
      // Skip over stored EBPs and return addresses.
      cur_word += 2;
      next_ebp = (int *)(*next_ebp);
    } else {
      to_end = copy_if_needed(cur_word, to_end);
      cur_word++;
    }
  }

  cur_word = to_start;
  while (cur_word < to_end) {
    // Invariant: cur_word will only ever land at the beginning of an allocation.
    int scan_offset;
    if (is_tuple(*cur_word)) {
      scan_offset = 1; // Skip size word.
    } else {
      scan_offset = 3; // Skip size word, arity, and text pointer.
    }
    int *prev_allocation = (int *)without_tag(*cur_word);
    int allocation_size = *prev_allocation * -1;
    for (int i = scan_offset; i < allocation_size; i++) {
      to_end = copy_if_needed(cur_word + i, to_end);
    }
    *cur_word = allocation_size - 1;
    cur_word += allocation_size;
    if ((int)cur_word % 8 != 0) {
      cur_word++;
    }
  }

  return to_end;
}
