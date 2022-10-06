#include <stdio.h>
#include <stdlib.h>

typedef struct {
    int* ptr;
    int num;
} pointnum;

int* getPointer(void) {
    return malloc(sizeof(int));
}

int readNumber(int* ptr) {
    //pointnum p1;
    //p1->ptr = ptr;
    //p1->num = *ptr;
    //return p1;
    return *ptr;

}

int testFunc(int (*ptr)(int)){
    return ptr(5);
}

readPrime 

void freePointer(int* pt){
    free(pt);
}

int* writePointer(int* pt, int num){
    *pt = num;
    return pt;
}