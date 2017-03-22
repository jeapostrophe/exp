#include <stdio.h>
#include <dlfcn.h>

typedef void (*vfun)();
typedef int (*ifun)();

int main ( int argc, char **argv ) {
  int r = 0;
  if ( argc != 3 ) { r = 1; goto end; }

  void *lib1 = dlopen(argv[1], RTLD_NOW|RTLD_LOCAL);
  if (!lib1) { r = 2; goto end; }
  void *lib2 = dlopen(argv[2], RTLD_NOW|RTLD_LOCAL);
  if (!lib2) { r = 3; goto free1; }

  vfun init1 = dlsym(lib1, "init");
  vfun init2 = dlsym(lib2, "init");
  vfun iterate1 = dlsym(lib1, "iterate");
  vfun iterate2 = dlsym(lib2, "iterate");
  ifun show1 = dlsym(lib1, "show");
  ifun show2 = dlsym(lib2, "show");

  init1(); init2();
  if ( show1() != 00 ) { r = 4; goto free2; }
  if ( show2() != 00 ) { r = 5; goto free2; }
  iterate1();
  if ( show1() != 11 ) { r = 6; goto free2; }
  if ( show2() != 00 ) { r = 7; goto free2; }
  iterate2();
  if ( show1() != 11 ) { r = 8; goto free2; }
  if ( show2() != 11 ) { r = 9; goto free2; }

 free2:
  dlclose(lib2);
 free1:
  dlclose(lib1);
 end:
  return r;
}
