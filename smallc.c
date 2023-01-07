#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// Creating Array

int *getArray(int size)
{
    return malloc(sizeof(int) * size);
}

int *getArrayChar(int size)
{
    fprintf(stderr, "Run create arr %s \n", "size");
    fprintf(stderr, "Run create arr %d \n", size);
    return malloc(sizeof(char) * size);
}

// Reading Array

int readPointerOffset(int offset, int *arr)
{
    return arr[offset];
}

char readPointerOffsetChar(int offset, char *arr)
{
    return arr[offset];
}

// Writing Array

void writeOffset(int offset, int *arr, int val)
{
    arr[offset] = val;
}

void writeOffsetChar(int offset, char *arr, char val)
{
    arr[offset] = val;
}

// Freeing Array
void freePointer(void *pt)
{
    free(pt);
}

void freePointerChar(char *pt)
{
    free(pt);
}

// Creating Any Pointers
void *createStruct(int size)
{
    // fprintf(stderr, "%s", "Run create Struct\n", 30);
    return malloc(size);
}

// Getting Data from Structs

int getIntStruct(unsigned char *ptr, int offset)
{
    unsigned char *ptr2 = ptr + offset;
    int *ptr3 = (int *)ptr2;
    return (*ptr3);
}

char getCharStruct(unsigned char *ptr, int offset)
{
    return (ptr[offset]);
}

void *getStructStruct(unsigned char *ptr, int offset)
{
    return (void *)(ptr + offset);
}

// Writing to Structs
void writeIntStruct(unsigned char *ptr, int offset, int num)
{
    // fprintf(stderr, "Writing %d to offset %d", num, offset, 30);
    unsigned char *a = ptr + offset;
    a[3] = (num >> 24) & 0xFF;
    a[2] = (num >> 16) & 0xFF;
    a[1] = (num >> 8) & 0xFF;
    a[0] = num & 0xFF;
}

void writeCharStruct(unsigned char *ptr, int offset, char val)
{
    // fprintf(stderr, "%s", "string format", 30);

    ptr[offset] = val;
}

void writeStructStruct(unsigned char *ptr, int offset, unsigned char *ptr2, int size)
{

    memcpy(ptr + offset, ptr2, size);
}

int *getPointer(void)
{
    int *a = malloc(sizeof(int));
    return a;
}

int readNumber(int *ptr)
{
    return *ptr;
}

int testFunc(int (*ptr)(int))
{
    return ptr(5);
}

int *writePointer(int *pt, int num)
{
    *pt = num;
    return pt;
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
