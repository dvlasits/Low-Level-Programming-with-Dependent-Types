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

// Array int primitives

void *create_int_array(int size)
{
    return malloc(sizeof(int) * size);
}

void write_int_array(int loc, int item, void *ptr)
{
    ((int *)ptr)[loc] = item;
}

int read_int_array(int loc, void *ptr)
{
    return ((int *)ptr)[loc];
}

// Free remains the same

// Array Primitives for Char

void *create_char_array(int size)
{
    return malloc(sizeof(char) * size);
}

void write_char_array(int loc, char item, void *ptr)
{
    ((char *)ptr)[loc] = item;
}

char read_char_array(int loc, void *ptr)
{
    return ((char *)ptr)[loc];
}