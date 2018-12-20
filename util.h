#include <stdio.h>

#ifndef UTIL_H
#define UTIL_H

int is_num(int val);
int is_bool(int val);
int is_tuple(int val);
int is_closure(int val);
int is_forwarder(int val);

int get_tag(int val);
int without_tag(int val);
int make_forwarder(int val);

void printHelp(FILE *out, int val, int tupleCounter);

#endif
