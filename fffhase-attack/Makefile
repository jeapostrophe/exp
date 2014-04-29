all: attack

attack: lib.so
	rm -fr compiled
	@echo Running without compiled version
	racket -t phase0.rkt --
	raco make phase0.rkt
	@echo Running with compiled version
	racket -t phase0.rkt --

lib.so: lib.o
	gcc -shared -o $@ $^

lib.o: lib.c
	gcc -fPIC -c $^ -o $@

