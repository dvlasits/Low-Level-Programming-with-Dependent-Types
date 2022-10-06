#include <stdio.h>
#include <stdlib.h>

typedef struct {
    int x;
} number;

number* getPointer(void) {
    number* pt = malloc(sizeof(number));
    pt->x = 10;
    return pt;
}

int readNumber(number* num) {
    return num->x;
}

int freePointer(number* pt){
    free(pt);
    return 0;
}

