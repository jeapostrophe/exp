typedef struct { double x; double y; } thestruct;
double get_x ( thestruct *u ) { return u->x; }
double get_y ( thestruct *u ) { return u->y; }
double go () {
 thestruct it = { .x = 1.0, .y = 2.0 };
 double sum = 0.0;
 for ( int i = 0; i < 18000000; i++ ) {
   sum = sum + get_x(&it) + get_y(&it);
 }
 return sum;
}