#include <stdio.h>

typedef trie;

typedef struct {
  int count;
  trie *next[256];
} trie;

void uniq ( char *f ) {
  FILE *IN = fopen(f, "r");
  if ( ! IN ) {
    return; 
  }

  trie *top = trie_allocate();
  int c;
  trie *cur = top;
  while ((c = fgetc(IN)) != EOF) {
    if ( c == ' ' ) {
      cur = top;
    } else {
      cur = trie_lookup(c);
      trie_increment(cur);
    }
  }
  
  fclose(IN);
}

int main (int argc, char **argv) {
  if ( argc == 1 ) {
    uniq("/home/jay/Dev/scm/github.jeapostrophe/exp/uniq.c");
  } else {
    for ( int i = 1 ; i < argc ; i++ ) {
      uniq(argv[i]);
    }
  }
  return 0;
}
