#include <stdio.h>
#include "util.h"

const int TAG_MASK   = 0x00000007;
const int NUM_MASK   = 0x00000001;
const int BOOL_TRUE  = 0xFFFFFFFF;
const int BOOL_FALSE = 0x7FFFFFFF;

int is_num(int val) {
  return (val & NUM_MASK) == 0;
}
int is_bool(int val) {
  return (val == BOOL_TRUE) || (val == BOOL_FALSE);
}
int is_tuple(int val) {
  return (val & TAG_MASK) == 1;
}
int is_closure(int val) {
  return (val & TAG_MASK) == 5;
}
int get_tag(int val) {
  return val & TAG_MASK;
}
int without_tag(int val) {
  return val & (0xFFFFFFFF ^ TAG_MASK);
}

void printHelp(FILE *out, int val, int tupleCounter) {
  if (is_num(val)) {
    fprintf(out, "%d", val >> 1);
  }
  else if (val == BOOL_TRUE) {
    fprintf(out, "true");
  }
  else if (val == BOOL_FALSE) {
    fprintf(out, "false");
  }
  else if (is_closure(val)) {
    fprintf(out, "<function>");
  }
  else if (is_tuple(val)) {
    int* addr = (int*)(val - 1);
    // Check whether we've visited this tuple already
    if ((*addr & 0x80000000) != 0) {
      fprintf(out, "<cyclic tuple %d>", (int)(*addr & 0x7FFFFFFF));
      return;
    }
    // Mark this tuple: save its length locally, then mark it
    int len = addr[0];
    *(addr) = 0x80000000 | (++tupleCounter);
    fprintf(out, "(");
    for (int i = 1; i <= len; i++) {
      if (i > 1) fprintf(out, ", ");
      printHelp(out, addr[i], tupleCounter);
    }
    fprintf(out, ")");
    // Unmark this tuple: restore its length
    *(addr) = len;
  }
  else {
    fprintf(out, "Unknown value: %#010x", val);
  }
}
