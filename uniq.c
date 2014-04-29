#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

typedef struct trie {
  struct trie *next[256];
  int count;
} trie;

trie* trie_allocate () {
  // Use calloc because it 0s memory
  return calloc(sizeof(trie), 1); }

trie* trie_lookup( trie* cur, int c ) {
  trie* next = cur->next[c];
  if ( next == NULL ) {
    next = trie_allocate();
    cur->next[c] = next; }
  return next; }

typedef struct marks {
  struct marks* prev;
  char c;
} marks;

void display_marks ( marks *ms ) {
  if ( ms ) {
    display_marks( ms->prev );
    printf("%c", ms->c); } }

void trie_display( trie* cur, marks *prev_ms ) {
  struct marks my_ms;
  my_ms.prev = prev_ms;
  if ( cur->count ) {
    printf("%3d ", cur->count );
    display_marks(prev_ms);
    printf("\n"); }
  for ( int i = 0; i < 256; i++ ) {
    trie* next = cur->next[i];
    if ( next ) {
      my_ms.c = i;
      trie_display(next, &my_ms); } } }

void uniq ( char *f ) {
  FILE *IN = fopen(f, "r");
  if ( ! IN ) { return; }

  trie *top = trie_allocate();
  int c;
  bool seen = false;
  trie *cur = top;
  while ((c = fgetc(IN)) != EOF) {
    if ( c == ' ' || c == '\n' || c == '\t' ) {
      if ( seen ) { cur->count++; }
      seen = false;
      cur = top; }
    else {
      seen = true;
      cur = trie_lookup(cur, c); } }
  fclose(IN);

  trie_display(top, NULL); }

int main (int argc, char **argv) {
  if ( argc == 1 ) {
    uniq("/home/jay/.emacs.el"); }
  else {
    for ( int i = 1 ; i < argc ; i++ ) {
      uniq(argv[i]); } } }
