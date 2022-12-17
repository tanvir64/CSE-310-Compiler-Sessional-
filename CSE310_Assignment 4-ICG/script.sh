#!/bin/bash
yacc -y -d -v 1705064.y
g++ -w -c -o y.o y.tab.c
flex 1705064.l
g++ -w -c -o l.o lex.yy.c
g++ -o a.out y.o l.o -lfl 
./a.out $1
