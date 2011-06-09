FUN_SRCS = mss1.c
LIB_SRCS = max.c
MAIN_SRCS = main.c
SRCS = $(MAIN_SRCS) $(FUN_SRCS) $(LIB_SRCS)
LIBS = $(LIB_SRCS:%.c=%.o)
OBJS = $(SRCS:%.c=%.o)
EXES = $(FUN_SRCS:%.c=test_%)

CC = gcc
CFLAGS = -std=c99 -pedantic -Wall -Werror
CPPFLAGS =
OPTFLAGS =
DBGFLAGS =
LDFLAGS =
RM = rm -rf

FRAMA_C = frama-c
FRAMAC_FLAGS = -cpp-extra-args="-DJESSIE_PRAGMAS"
JESSIE = $(FRAMA_C) $(FRAMAC_FLAGS) -jessie
JESSIE_ERGO = $(JESSIE) -jessie-atp=ergo
JESSIE_SIMPLIFY = $(JESSIE) -jessie-atp=simplify

%.o: %.c
	$(CC) $(CFLAGS) $(CPPFLAGS) $(OPTFLAGS) $(DBGFLAGS) -c $<

test_%: main.o %.o $(LIBS)
	$(CC) $(CFLAGS) $(OPTFLAGS) $(DBGFLAGS) $(LDFLAGS) -o $@ $^

ergo_%: %.c
	$(JESSIE_ERGO) $^

simplify_%: %.c
	$(JESSIE_SIMPLIFY) $^

jessie_%: %.c
	$(JESSIE) $^

.PHONY: all clean allclean jessieclean

all: $(EXES)

mss1.o: mss.h max.h

max.o: max.h

main.o: mss.h max.h

clean:
	$(RM) $(EXES)
	$(RM) $(OBJS)

allclean: clean
	$(RM) *~
	$(RM) a.out *.o

distclean: allclean
	$(RM) *.jessie

