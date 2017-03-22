#include <stdio.h>

int global;
static int static_global;
const char* file = __FILE__;

void init() {
  global = 0;
  static_global = 0;
}

void iterate() {
  global++;
  static_global++;
}

int show() {
  return global*10 + static_global;
}
