#include "dir-24-8-basic.h"
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stddef.h>

size_t extract_first_index(uint8_t *data)
{
    size_t index = data[0];
    index <<= 8;
    index |= data[1];
    index <<= 8;
    index |= data[2];

    return index;
}

size_t extract_last_index(uint8_t *data)
{
    size_t index = data[0];
    index <<= 8;
    index |= data[1];
    index <<= 8;
    index |= 0xFF;

    return index;
}

int entry_flag(uint16_t entry)
{
    return (entry & TBL_24_FLAG_MASK) >> 15;
}

int tbl_24_entry_plen(uint16_t entry)
{
    return (entry & TBL_24_PLEN_MASK) >> 8;
}

int entry_value(uint16_t entry)
{
    return entry & TBL_24_VAL_MASK;
}

uint16_t tbl_24_entry_put_plen(uint16_t entry, uint8_t prefixlen)
{
    return entry | ((prefixlen & (TBL_24_PLEN_MASK >> 8)) << 8);
}

uint16_t entry_set_flag(uint16_t entry)
{
    return entry | TBL_24_FLAG_MASK;
}

int tbl_long_entry_plen(uint16_t entry)
{
    return (entry & TBL_LONG_PLEN_MASK) >> 8;
}

uint8_t tbl_long_entry_val(uint16_t entry)
{
    return entry & TBL_LONG_VAL_MASK;
}

uint16_t tbl_long_entry_put_plen(uint16_t entry, uint8_t prefixlen)
{
    return entry | ((prefixlen & (TBL_LONG_PLEN_MASK >> 8)) << 8);
}

struct tbl *tbl_allocate(size_t max_entries)
{
    struct tbl *tbl = (struct tbl *) malloc(sizeof(struct tbl));
    if(!tbl)
        return NULL;

    uint16_t *tbl_24 = (uint16_t *) calloc(TBL_24_MAX_ENTRIES, sizeof(uint16_t));
    if(!tbl_24){
        free(tbl);
        return NULL;
    }

    uint16_t *tbl_long = (uint16_t *) calloc(TBL_LONG_MAX_ENTRIES, sizeof(uint16_t));
    if(!tbl_long){
        free(tbl_24);
        free(tbl);
        return NULL;
    }

    tbl->tbl_24 = tbl_24;
    tbl->tbl_long = tbl_long;
    tbl->tbl_long_index = 0;
    tbl->n_entries = 0;
    tbl->max_entries = max_entries;

    return tbl;
}

void tbl_free(struct tbl *tbl)
{
    free(tbl->tbl_24);
    free(tbl->tbl_long);
    free(tbl);
}

int tbl_update_elem(struct tbl *_tbl, struct key *_key, uint8_t value)
{
    uint8_t prefixlen = _key->prefixlen;
    uint8_t *data = _key->data;
    uint16_t *tbl_24 = _tbl->tbl_24;//Segfault
    uint16_t *tbl_long = _tbl->tbl_long;

    if(_tbl->n_entries >= _tbl->max_entries)
        return -1;

    _tbl->n_entries ++;

    //If prefixlen is smaller than 24, simply store the value in tbl_24, in
    //entries indexed from data[0...2] up to data[0].data[1].255
    if(prefixlen < 24){
        size_t first_index = extract_first_index(data);
        size_t last_index = extract_last_index(data);

        //fill all entries between first index and last index with value if
        //these entries don't have a longer prefix associated with them
        for(int i = first_index; i <= last_index; i++){
            if(!entry_flag(tbl_24[i]) && tbl_24_entry_plen(tbl_24[i]) <= prefixlen)
                tbl_24[i] = value;
                //record the length of the prefix associated with the entry
                tbl_24[i] = tbl_24_entry_put_plen(tbl_24[i], prefixlen);
        }
    } else {
        //If the prefixlen is not smaller than 24, we have to store the value
        //in tbl_long.

        //Check the tbl_24 entry corresponding to the key. If it already has a
        //flag set to 1, use the stored value as base index, otherwise get a new
        //index and store it in the tbl_24
        size_t base_index;
        size_t tbl_24_index = extract_first_index(data);
        if(entry_flag(tbl_24[tbl_24_index])){
            base_index = entry_value(tbl_24[tbl_24_index]);
        } else {
            //generate next index and store it in tbl_24
            base_index = _tbl->tbl_long_index;
            _tbl->tbl_long_index ++;
            tbl_24[tbl_24_index] = base_index;
            tbl_24[tbl_24_index] = entry_set_flag(tbl_24[tbl_24_index]);
            //record the prefix length associated with the entry
            tbl_24[tbl_24_index] = tbl_24_entry_put_plen(tbl_24[tbl_24_index], prefixlen);
        }

        //The last byte in data is used as the starting offset for tbl_long
        //indexes
        uint8_t offset = data[3];

        //Store value in tbl_long entries indexed from value*256+offset up to
        //value*256+255
        for(int i = offset; i < TBL_LONG_OFFSET_MAX; i++){
            int index = base_index * TBL_LONG_FACTOR + i;
            if(tbl_long_entry_plen(tbl_long[index]) <= prefixlen){
                tbl_long[index] = value;
                //record length of the prefix associated with the entry
                tbl_long[index] = tbl_long_entry_put_plen(tbl_long[index], prefixlen);
            }
        }
    }

    return 0;
}
