#include "dir-24-8-basic.h"
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stddef.h>

void print_tbl_24_entry(struct tbl *tbl, size_t index)
{
    uint16_t tbl_24_entry = tbl->tbl_24[index];
    int flag = (tbl_24_entry & TBL_24_FLAG_MASK) >> 15;
    int prefixlen = (tbl_24_entry & TBL_24_PLEN_MASK) >> 8;
    int value = tbl_24_entry & TBL_24_VAL_MASK;

    printf("Printing tbl_24 entry at: %ld\n", index);
    printf("========== tbl_24 entry ==========\n");
    printf("flag: %d\n", flag);
    printf("prefix length: %d\n", prefixlen);
    printf("value: %d\n", value);
    printf("==================================\n");
}

void print_tbl_long_entry(struct tbl *tbl, size_t index){
    uint16_t tbl_long_entry = tbl->tbl_long[index];
    int prefixlen = (tbl_long_entry & TBL_LONG_PLEN_MASK) >> 8;
    int value = tbl_long_entry & TBL_LONG_VAL_MASK;

    printf("Printing tbl_long entry at: %ld\n", index);
    printf("========= tbl_long entry =========\n");
    printf("prefix length: %d\n", prefixlen);
    printf("value: %d\n", value);
    printf("==================================\n");
}

struct key *allocate_key(uint8_t *data, uint8_t prefixlen)
{
    struct key *key = (struct key *) malloc(sizeof(struct key));
    if(!key){
        return NULL;
    }

    memcpy(key->data, data, 4);
    key->prefixlen = prefixlen;

    return key;
}

int test_update_elem()
{
    int res;
    struct tbl *tbl = tbl_allocate(256);
    if(!tbl)
        return -1;
    uint16_t *tbl_24 = tbl->tbl_24;

    uint8_t data_1[4] = {10, 54, 0, 0};
    struct key *key_1 = allocate_key(data_1, 16);
    if(!key_1){
        tbl_free(tbl);
        return -1;
    }

    uint8_t data_2[4] = {10, 54, 34, 192};
    struct key *key_2 = allocate_key(data_2, 26);
    if(!key_2){
        free(key_1);
        tbl_free(tbl);
        return -1;
    }

    uint8_t data_3[4] = {10, 54, 34, 0};
    struct key *key_3 = allocate_key(data_3, 24);
    if(!key_3){
        free(key_1);
        free(key_2);
        tbl_free(tbl);
        return -1;
    }

    printf("##### Inserting first entry #####\n");
    res = tbl_update_elem(tbl, key_1, 10);
    if(res)
        goto out;
    printf("##### Inserted first entry #####\n");

    size_t index = extract_first_index(key_1->data);
    print_tbl_24_entry(tbl, index);

    index = extract_last_index(key_1->data);
    print_tbl_24_entry(tbl, index);

    printf("##### Inserting second entry #####\n");
    res = tbl_update_elem(tbl, key_2, 12);
    if(res)
        goto out;
    printf("##### Inserted second entry #####\n");

    index = extract_first_index(key_2->data);
    print_tbl_24_entry(tbl, index);
    index = 191;
    print_tbl_long_entry(tbl, index);
    index = 192;
    print_tbl_long_entry(tbl, index);
    index = 255;
    print_tbl_long_entry(tbl, index);

    printf("##### Inserting third entry #####\n");
    res = tbl_update_elem(tbl, key_3, 11);
    if(res)
        goto out;
    printf("##### Inserted third key #####\n");

    index = extract_first_index(key_3->data);
    print_tbl_24_entry(tbl, index);
    index = 0;
    print_tbl_long_entry(tbl, index);
    index = 191;
    print_tbl_long_entry(tbl, index);
    index = 192;
    print_tbl_long_entry(tbl, index);

out:
    tbl_free(tbl);
    free(key_3);
    free(key_2);
    free(key_1);
    return res;
}

int main()
{
    int res = test_update_elem();
    if(res){
        printf("Something went wrong: %d\n", res);
    } else {
        printf("End of test\n");
    }
}
