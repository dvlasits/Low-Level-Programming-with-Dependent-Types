#include <stdio.h>
#include <stdlib.h>

typedef struct
{
    int *ptr;
    int num;
} pointnum;

int *getPointer(void)
{
    return malloc(sizeof(int));
}

int *getArray(int size)
{
    return malloc(sizeof(int) * size);
}

int readPointerOffset(int offset, int *arr)
{
    return arr[offset];
}

void writeOffset(int offset, int *arr, int val)
{
    arr[offset] = val;
}

int readNumber(int *ptr)
{
    return *ptr;
}

int testFunc(int (*ptr)(int))
{
    return ptr(5);
}

void freePointer(int *pt)
{
    free(pt);
}

int *writePointer(int *pt, int num)
{
    *pt = num;
    return pt;
}

void smartRead(void (*func)(int *, int), int *ptr)
{
    func(ptr, *ptr);
}

int basicRead(int *ptr)
{
    return *ptr;
}

int *g = NULL;

int *savePtr(int *ptr)
{
    g = ptr;
    return ptr;
}

int readGlobal(void)
{
    return *g;
}

int *readPointer(void)
{
    return g;
}
