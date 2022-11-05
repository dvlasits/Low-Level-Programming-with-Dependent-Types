#include <stdio.h>
#include <stdlib.h>

typedef struct
{
    int *ptr;
    int num;
} pointnum;

int *getPointer(void)
{
    int *a = malloc(sizeof(int));
    fprintf(stderr, "Getting a new pointer %d\n", a);
    return a;
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
    fprintf(stderr, "Freeing pointer %d\n", pt);
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
