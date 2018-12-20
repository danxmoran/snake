#ifndef GC_H
#define GC_H

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
int* copy_if_needed(int* snake_val_addr, int* heap_top);

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
int* gc(int* bottom_frame, int* top_frame, int* top_stack, int* from_start, int* from_end, int* to_start);

#endif
