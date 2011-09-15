#include <iostream>
#include <iomanip>
#include <math.h>
#include <string>
using namespace std;

// smallestDivisorNoFor: natural natural -> natural
// returns the smallest divisor of n between num and n
int smallestDivisorNoFor ( int n, int num ) {
  if ( num < n ) {
    if (n % num == 0) {
      return num;
    } else {
      return smallestDivisorNoFor(n, num + 1);
    }
  } else {
    return n;
  }
}

// smallestDivisor : natural -> natural
// returns the smallest divisor of n
int smallestDivisor ( int n ) {
  for (int num = 2; num < n; num++) {
    int mod = n % num; // Gets the remainder
    if (mod == 0) {
      return num;
    }
  }
  return n;
}

// validInputHuh : natural -> boolean
// determines if the number is a valid input to this program
bool validInputHuh ( int n ) {
  return (n > 0) && (n < 100000);
}

/* This program determines if a number is prime

Input: The number to check for primality

Output: Print if it is prime or not

Logic: Finds the smallest divisor of the number, if it is the given
number, then it must be prime

Manual test cases:

1. We cannot automatically test when the user types in a non-number,
so you should manually ensure that entering a string like "aa" results
in a request for another number
*/
int main() {    
    cout << "Automated tests" << endl;

    cout << "validInputHuh(" << -1 << ") = " << validInputHuh(-1) << ", but should equal " << false << endl; 
    cout << "validInputHuh(" << 12 << ") = " << validInputHuh(12) << ", but should equal " << true << endl;
    /* Substitution:
       validInputHuh(12)
       = (n > 0) && (n < 100000) [where n = 12]
       = (12 > 0) && (12 < 100000)
       = true && (12 < 100000)
       = (12 < 100000)
       = true
    */
    cout << "validInputHuh(" << 10000000 << ") = " << validInputHuh(10000000) << ", but should equal " << false << endl; 


    cout << "smallestDivisor(" << 12 << ") = " << smallestDivisor(12) << ", but should equal " << 2 << endl;
    cout << "smallestDivisor(" << 13 << ") = " << smallestDivisor(13) << ", but should equal " << 13 << endl; 
    /* Store tracking: */
    // smallestDivisor(13);
    // // =
    // // [Store: n = 13 ]
    // for (int num = 2; num < n; num++) {
    //   int mod = n % num; // Gets the remainder
    //   if (mod == 0) {
    //     return num;
    //   }
    // }
    // return n;
    // // = 
    // // [Store: n = 13, num = 2 ]
    // for (; num < n; num++) {
    //   int mod = n % num; // Gets the remainder
    //   if (mod == 0) {
    //     return num;
    //   }
    // }
    // return n;
    // // =
    // // [Store: n = 13, num = 2 ]
    // if ( num < n ) {
    //   int mod = n % num; // Gets the remainder
    //   if (mod == 0) {
    //     return num;
    //   }
    //   num ++;
    //   for (; num < n; num++) {
    //     int mod = n % num; // Gets the remainder
    //     if (mod == 0) {
    //       return num;
    //     }
    //   }
    //   return n;
    // } else {
    //   return n;
    // }
    // // =
    // // [Store: n = 13, num = 2 ]
    // if ( 2 < 13 ) {
    //   int mod = n % num; // Gets the remainder
    //   if (mod == 0) {
    //     return num;
    //   }    
    //   num ++;
    //   for (; num < n; num++) {
    //     int mod = n % num; // Gets the remainder
    //     if (mod == 0) {
    //       return num;
    //     }
    //   }
    //   return n;
    // } else {
    //   return n;
    // }
    // // =
    // // [Store: n = 13, num = 2 ]
    // if ( true ) {
    //   int mod = n % num; // Gets the remainder
    //   if (mod == 0) {
    //     return num;
    //   }
    //   num ++;
    //   for (; num < n; num++) {
    //     int mod = n % num; // Gets the remainder
    //     if (mod == 0) {
    //       return num;
    //     }
    //   }
    //   return n;
    // } else {
    //   return n;
    // }
    // // =
    // // [Store: n = 13, num = 2 ]
    // int mod = n % num; // Gets the remainder
    // if (mod == 0) {
    //   return num;
    // }
    // num ++;
    // for (; num < n; num++) {
    //   int mod = n % num; // Gets the remainder
    //   if (mod == 0) {
    //     return num;
    //   }
    // }
    // return n;
    // // =
    // // [Store: n = 13, num = 2 ]
    // int mod = 13 % 2; // Gets the remainder
    // if (mod == 0) {
    //   return num;
    // }
    // num ++;
    // for (; num < n; num++) {
    //   int mod = n % num; // Gets the remainder
    //   if (mod == 0) {
    //     return num;
    //   }
    // }
    // return n;
    // // =
    // // [Store: n = 13, num = 2 ]
    // if (1 == 0) {
    //   return num;
    // }
    // num ++;
    // for (; num < n; num++) {
    //   int mod = n % num; // Gets the remainder
    //   if (mod == 0) {
    //     return num;
    //   }
    // }
    // return n;
    // // =
    // // [Store: n = 13, num = 2 ]
    // if (false) {
    //   return num;
    // }
    // num ++;
    // for (; num < n; num++) {
    //   int mod = n % num; // Gets the remainder
    //   if (mod == 0) {
    //     return num;
    //   }
    // }
    // return n;
    // // =
    // // [Store: n = 13, num = 2 ]
    // num ++;
    // for (; num < n; num++) {
    //   int mod = n % num; // Gets the remainder
    //   if (mod == 0) {
    //     return num;
    //   }
    // }
    // return n;
    // // =
    // // [Store: n = 13, num = 2 ]
    // num = num + 1;
    // for (; num < n; num++) {
    //   int mod = n % num; // Gets the remainder
    //   if (mod == 0) {
    //     return num;
    //   }
    // }
    // return n;
    // // =
    // // [Store: n = 13, num = 2 ]
    // num = 2 + 1;
    // for (; num < n; num++) {
    //   int mod = n % num; // Gets the remainder
    //   if (mod == 0) {
    //     return num;
    //   }
    // }
    // return n;
    // // =
    // // [Store: n = 13, num = 2 ]
    // num = 3;
    // for (; num < n; num++) {
    //   int mod = n % num; // Gets the remainder
    //   if (mod == 0) {
    //     return num;
    //   }
    // }
    // return n;
    // // =
    // // [Store: n = 13, num = 3 ]
    // for (; num < n; num++) {
    //   int mod = n % num; // Gets the remainder
    //   if (mod == 0) {
    //     return num;
    //   }
    // }
    // return n;
    // // and so on...

    cout << "smallestDivisorNoFor(" << 12 << ", " <<  2 << ") = " << smallestDivisorNoFor(12,2) << ", but should equal " << 2 << endl;
    cout << "smallestDivisorNoFor(" << 13 << ", " << 2 << ") = " << smallestDivisorNoFor(13, 2) << ", but should equal " << 13 << endl; 
    /* Substitution
       smallestDivisorNoFor(13, 2)
       = [where n = 13, num = 13]
       >> if: num < n
       >> if: 2 < 13
       >> if: true
       >> choose true side
       >> if: n % num == 0
       >> if: 13 % 2 == 0
       >> if: 1 == 0
       >> if: false
       >> choose false side
       = smallestDivisorNoFor(n, num + 1)
       = smallestDivisorNoFor(13, 2 + 1)
       = smallestDivisorNoFor(13, 3)
       = and so on...
    */

	while (true) {
      int isprime = 0;
      cout << "Enter the number for primality check" << endl;
      cin >> isprime; // Input the number
      if ( cin.fail() || ! validInputHuh( isprime ) ) {
        cout << "Please enter a number between 0 and 100000" << endl;
        cin.clear();
        cin.sync();
      } else {
        cout << "Number for primality checking is " << isprime << endl;

        int num = smallestDivisor(isprime) ;
        if ( num == isprime ) {
          cout << isprime << " is prime" << endl;
        } else {
          cout << isprime << " is not prime, it is divisible by " << num << endl;
        }

        return 0;
      }
	}
}
