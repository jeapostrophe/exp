all: attack

attack: lib.so
	@echo Running without compiled version
	rm -fr compiled
	racket -t phase0.rkt --
	@echo Running with compiled version
	raco make phase0.rkt
	racket -t phase0.rkt --

lib.so: lib.o
	gcc -shared -o $@ $^

lib.o: lib.c
	gcc -fPIC -c $^ -o $@

