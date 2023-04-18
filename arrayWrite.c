#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void writeNums(void *ptr, int size)
{

    int *ptr2 = (int *)ptr;
    for (int i = 0; i < (size - 1); i++)
    {
        ptr2[i] = i;
    }
}