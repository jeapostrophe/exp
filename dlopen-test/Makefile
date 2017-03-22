all: test

lib%o.c: lib.c
	cp $^ $@

lib%c.so: lib%o.so
	cp $^ $@

lib%.so: lib%.c
	gcc -shared $^ -o $@

main: main.c
	gcc $^ -o $@

test: main lib1o.so lib2o.so lib1c.so
	md5 $^
	./main lib1o.so lib2o.so
	./main lib1o.so lib1c.so
	./main lib1o.so lib1o.so
