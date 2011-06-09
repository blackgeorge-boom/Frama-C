FUN_SRCS = mss1.c mss2.c mss3.c
LIB_SRCS = max.c
MAIN_SRCS = main.c
SRCS = $(MAIN_SRCS) $(FUN_SRCS) $(LIB_SRCS)
LIBS = $(LIB_SRCS:%.c=%.o)
OBJS = $(SRCS:%.c=%.o)
EXES = $(FUN_SRCS:%.c=test_%)

CC = gcc
CFLAGS = -std=c99 -pedantic -Wall -Werror
CPPFLAGS = -DNO_JESSIE_PRAGMAS
OPTFLAGS =
DBGFLAGS =
LDFLAGS =
RM = rm -rf

FRAMA_C = frama-c
FRAMAC_FLAGS = #-cpp-extra-args="-DJESSIE_PRAGMAS"
JESSIE = $(FRAMA_C) $(FRAMAC_FLAGS) -jessie
JESSIE_ERGO = $(JESSIE) -jessie-atp=ergo
JESSIE_SIMPLIFY = $(JESSIE) -jessie-atp=simplify
JESSIE_CVC3 = $(JESSIE) -jessie-atp=cvc3

%.o: %.c
	$(CC) $(CFLAGS) $(CPPFLAGS) $(OPTFLAGS) $(DBGFLAGS) -c $<

test_%: main.o %.o $(LIBS)
	$(CC) $(CFLAGS) $(OPTFLAGS) $(DBGFLAGS) $(LDFLAGS) -o $@ $^

jessie_%: %.c
	$(JESSIE) $^

ergo_%: %.c
	$(JESSIE_ERGO) $^

simplify_%: %.c
	$(JESSIE_SIMPLIFY) $^

cvc3_%: %.c
	$(JESSIE_CVC3) $^

.PHONY: all clean allclean jessieclean

all: $(EXES)

main.o: mss.h max.h

max.o: max.h

mss1.o: mss.h max.h

mss3.o: mss.h max.h


clean:
	$(RM) $(EXES)
	$(RM) $(OBJS)

allclean: clean
	$(RM) *~
	$(RM) a.out *.o

distclean: allclean
	$(RM) *.jessie

