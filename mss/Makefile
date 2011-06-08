FUN_SRCS = mss1.c
MAIN_SRCS = main.c
SRCS = $(FUN_SRCS) $(MAIN_SRCS)
OBJS = $(SRCS:%.c=%.o)
EXES = $(FUN_SRCS:%.c=test_%)

CC = gcc
CFLAGS = -std=c99 -pedantic -Wall
CPPFLAGS =
OPTFLAGS =
DBGFLAGS =
LDFLAGS =
RM = rm -rf

FRAMA_C = frama-c
JESSIE = $(FRAMA_C) -jessie
JESSIE_ERGO = $(JESSIE) -jessie-atp=ergo
JESSIE_SIMPLIFY = $(JESSIE) -jessie-atp=simplify

JESSIE_DIRS = $(FUN_SRCS:%.c=%.jessie)

%.o: %.c
	$(CC) $(CFLAGS) $(CPPFLAGS) $(OPTFLAGS) $(DBGFLAGS) -c $<

test_%: main.o %.o
	$(CC) $(CFLAGS) $(OPTFLAGS) $(DBGFLAGS) $(LDFLAGS) -o $@ $^

ergo_%: %.c
	$(JESSIE_ERGO) $^

simplify_%: %.c
	$(JESSIE_SIMPLIFY) $^

jessie_%: %.c
	$(JESSIE) $^

.PHONY: all clean allclean jessieclean

all: $(EXES)

clean:
	$(RM) $(EXES)
	$(RM) $(OBJS)

allclean: clean
	$(RM) *~
	$(RM) a.out

jessieclean:
	$(RM) $(JESSIE_DIRS)

