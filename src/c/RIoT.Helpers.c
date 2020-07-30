#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include "RIoT_Helpers.h"

void write_out(const char* filename, uint8_t* content, uint32_t len){
    FILE *f = fopen(filename, "w");
    if (f == NULL) {
        printf("ERROR: Fail to open %s.\n", filename);
        exit(1);
    }

    for (uint32_t i = 0; i < len; i++) {
        fprintf(f, "%x", content[i]);
    }

    fclose(f);
}