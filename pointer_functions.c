#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// Basic Pointer Functions

void *alloc_pointer(void)
{
    int *a = malloc(sizeof(int));
    return a;
}

void write_int_pointer(int to_write, void *ptr)
{
    *(int *)ptr = to_write;
}

int read_int_pointer(void *ptr)
{
    return *(int *)ptr;
}

void free_pointer(void *pt)
{
    free(pt);
}
