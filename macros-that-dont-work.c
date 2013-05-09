#include <stdio.h>

// only call discriminant with effect-free expressions
#define discriminant(a, b, c) (((b)*(b)) - (4*(a)*(c)))

int discriminantf( int a, int b, int c ) {
  return (b*b) - (4*a*c);
}

#define test(a,b,c) printf("%d should be %d\n", discriminant(a, b, c), discriminantf(a, b, c))
#define test2(a,b,c) printf("%d should be %d\n", 2*discriminant(a, b, c), 2*discriminantf(a, b, c))

#define discriminant_set(a, b, c, out) int bv = b; int out = (((bv)*(bv)) - (4*(a)*(c)));

int main () {
  // Easy
  test(1,2,3);
  // Hard
  test(1+1,2+2,3+3);
  // Harder
  test2(1+1,2+2,3+3);

  // Hardest
  int x0 = 3;
  int x1 = 3;

  printf("%d should be %d\n", discriminant(1, x0--, 2), discriminantf(1, x1--, 2));

  // Hack
  int y0 = 3;
  int y1 = 3;

  discriminant_set(1, y0--, 2, d0);
  
  printf("%d should be %d\n", d0, discriminantf(1, y1--, 2));

  return 0;
}
