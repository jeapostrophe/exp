#include <iostream>
#include <list>

using namespace std;

class List {
public:
  virtual bool is_empty() = 0;
  virtual bool is_one( char a, List *l ) = 0;
  virtual bool same_as( List *l ) = 0;
  virtual List *reverse( List *l ) = 0;
};

class LMt : public List {
public:
  LMt() {};
  List *reverse( List *r ) { return r; }
  bool is_empty() { return true; }
  bool is_one( char a, List *l ) { return false; }
  bool same_as( List *l ) { return l->is_empty(); } };

class LOne : public List {
  char a; List *d;
public:
  LOne( char a, List *d ): a(a), d(d) {};
  bool is_empty() {
    return false; }
  bool is_one( char a, List *l ) {
    return (this->a == a) && this->d->same_as( l ); }
  bool same_as( List *l ) {
    return l->is_one( a, d ); }
  List *reverse( List *r ) {
    return this->d->reverse( new LOne( this->a, r ) ); } };

/*
  palindrome : list<char> -> boolean
  True if the list is the same front to back
*/
bool palindrome( List *l ) {
  return l->same_as(l->reverse( new LMt() )); }

bool palindrome_array( char a[], size_t alen ) {
  for ( size_t i = 0; i <= alen; i++ ) {
    if ( a[i] != a[alen - i] ) {
      return false; } }
  return true; }

bool palindrome_dll( list<char> *l ) {
  auto f = l->begin();
  auto r = l->rbegin();
  for ( ; f != l->end() && r != l->rend(); f++, r++ ) {
    if ( *f != *r ) {
      return false; } }
  return true; } 

int main() {
  { char example[] = "racecar";
    cout << palindrome_array( example, 6 ) <<
      " should be " << true << endl ; }

  { char example[] = "ricecar";
    cout << palindrome_array( example, 6 ) <<
      " should be " << false << endl ; }

  { auto example = new LOne( 'r', new LOne( 'a', new LOne( 'c', new LOne( 'e', new LOne( 'c', new LOne( 'a', new LOne( 'r', new LMt() ) ) ) ) ) ) );
    cout << palindrome( example ) <<
      " should be " << true << endl ; }

  { auto example = new LOne( 'r', new LOne( 'i', new LOne( 'c', new LOne( 'e', new LOne( 'c', new LOne( 'a', new LOne( 'r', new LMt() ) ) ) ) ) ) );
    cout << palindrome( example ) <<
      " should be " << false << endl ; }

  { auto example = new list<char>();
    example->push_back('r');
    example->push_back('a');
    example->push_back('c');
    example->push_back('e');
    example->push_back('c');
    example->push_back('a');
    example->push_back('r');
    cout << palindrome_dll( example ) <<
      " should be " << true << endl ; }

  { auto example = new list<char>();
    example->push_back('r');
    example->push_back('i');
    example->push_back('c');
    example->push_back('e');
    example->push_back('c');
    example->push_back('a');
    example->push_back('r');
    cout << palindrome_dll( example ) <<
      " should be " << false << endl ; }}
