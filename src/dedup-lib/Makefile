CFLAGS=-Wall -fPIC
LDFLAGS=-L.
LIBS=-lssl -lcrypto 
OBJECTS=rabinpoly.o msb.o

ifdef DEBUG
	CFLAGS+=-g
endif

all: rabin-example

rabin-example : rabin-example.o libdedup.a
	gcc $(LDFLAGS) -o $@ $^ $(LIBS)

libdedup.a : $(OBJECTS)
	ar -rcs $@ $?

%.o : %.c 
	gcc $(CFLAGS) -c -o $@ $<

%.c : %.h

.PHONY: clean

clean : 
	rm -f *.o libdedup.a rabin-example
