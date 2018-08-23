#include "dir-24-8-basic.h"
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stddef.h>

size_t tbl_24_extract_first_index(uint8_t *data)
{
    size_t index = data[0];
    index <<= 8;
    index |= data[1];
    index <<= 8;
    index |= data[2];

    return index;
}

size_t tbl_24_extract_last_index(struct key *key)
{
    uint8_t *data = key->data;
    size_t prefixlen = key->prefixlen;

    size_t index = tbl_24_extract_first_index(data);

    if(prefixlen < TBL_24_PLEN_MAX){
        size_t fill = 1;
        for(int i = 1; i < TBL_24_PLEN_MAX - prefixlen; i++){
            fill <<= 1;
            fill |= 1;
        }
        //printf("fill: %ld\n", fill);
        index |= fill;
    }

    return index;
}

uint8_t *tbl_24_make_data_from_index(size_t index)
{
    uint8_t data[4];

    data[0] = index >> 16;
    data[1] = (index << 8) >> 16;
    data[2] = (index << 16) >> 16;
    data[3] = 0;
}

int tbl_24_entry_plen(uint16_t entry)
{
    return (entry & TBL_24_PLEN_MASK) >> 8;
}

uint8_t *tbl_24_is_last_index(size_t index, struct tbl *tbl)
{
    uint16_t *tbl_24 = tbl->tbl_24;
    size_t prefixlen = tbl_24_entry_plen(tbl_24[index]);

    size_t mask = 1;
    for(int i = 1; i < TBL_24_PLEN_MAX - prefixlen; i++){
        mask <<= 1;
        mask |= 1;
    }

    size_t res = index & mask;//Has to be only ones
    if(res == (2 << (TBL_24_PLEN_MAX - prefixlen)) - 1){
        return tbl_24_make_data_from_index(index);
    } else {
        return NULL;
    }
}

int tbl_24_entry_flag(uint16_t entry)
{
    return (entry & TBL_24_FLAG_MASK) >> 15;
}

uint16_t tbl_24_find_replacement(struct key *key, struct tbl *tbl)
{
    if(key->prefixlen < 1)
        return 0;

    uint16_t *tbl_24 = tbl->tbl_24;
    uint8_t *data = key->data;

    size_t first = tbl_24_extract_first_index(data);
    size_t current = first - 1;
    uint8_t *current_data;

    while(current >= 0 &&
            ((current_data = tbl_24_is_last_index(current, tbl)) ||
                tbl_24_entry_flag(tbl_24[current]))){

        if(tbl_24_is_last_index(current, tbl)){
            current = tbl_24_extract_first_index(current_data) - 1;
        } else if(tbl_24_entry_flag(tbl_24[current])){
            current --;
        }
    }

    if(current < 0){
        return 0;
    }

    return tbl_24[current];
}

uint16_t tbl_24_entry_set_flag(uint16_t entry)
{
    return entry | TBL_24_FLAG_MASK;
}

uint16_t tbl_24_entry_put_plen(uint16_t entry, uint8_t prefixlen)
{
    return entry | ((prefixlen & (TBL_24_PLEN_MASK >> 8)) << 8);
}

int tbl_24_entry_val(uint16_t entry)
{
    return entry & TBL_24_VAL_MASK;
}

size_t tbl_long_extract_first_index(uint8_t *data, size_t base_index)
{
    return base_index * TBL_LONG_FACTOR + data[3];
}

size_t tbl_long_extract_last_index(struct key *key, size_t base_index)
{
    uint8_t offset = key->data[3];
    size_t prefixlen = key->prefixlen;

    size_t fill = 1;
    for(int i = 1; i < TBL_PLEN_MAX - prefixlen; i++){
        fill <<= 1;
        fill |= 1;
    }
    offset |= fill;

    return base_index * TBL_LONG_FACTOR + offset;
}

int tbl_long_entry_plen(uint16_t entry)
{
    return (entry & TBL_LONG_PLEN_MASK) >> 8;
}

uint8_t tbl_long_entry_val(uint16_t entry)
{
    return entry & TBL_LONG_VAL_MASK;
}

uint8_t *tbl_long_is_last_index(size_t index, struct tbl *tbl,
                                size_t base_index)
{
    uint16_t *tbl_long = tbl->tbl_long;
    size_t prefixlen = tbl_long_entry_plen(tbl_long[index]);

    size_t mask = 1;
    for(int i = 1; i < TBL_PLEN_MAX - prefixlen; i++){
        mask <<= 1;
        mask |= 1;
    }

    size_t res = index & mask;//Has to be only ones
    if(res == (2 << (TBL_PLEN_MAX - prefixlen)) - 1){
        return tbl_24_make_data_from_index(index);
    } else {
        return NULL;
    }
}

uint16_t tbl_long_find_replacement(struct key *key, struct tbl *tbl,
                                    size_t base_index)
{
    if(key->prefixlen < 25)
        return 0;

    uint16_t *tbl_long = tbl->tbl_long;
    uint8_t *data = key->data;

    uint8_t *current_data;
    size_t current = tbl_long_extract_first_index(data, base_index);
    while(current >= base_index * TBL_LONG_FACTOR &&
            (current_data = tbl_long_is_last_index(current, tbl, base_index))){
                current =
                    tbl_long_extract_first_index(current_data, base_index) - 1;
            }

    if(current < base_index * TBL_LONG_FACTOR){
        return 0;
    } else {
        return tbl_long[current];
    }
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

    uint16_t *tbl_24 = (uint16_t *) calloc(TBL_24_MAX_ENTRIES,
                                            sizeof(uint16_t));
    if(!tbl_24){
        free(tbl);
        return NULL;
    }

    uint16_t *tbl_long = (uint16_t *) calloc(TBL_LONG_MAX_ENTRIES,
                                                sizeof(uint16_t));
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
    if(!_tbl || !_key){
        //printf("Invalid table or key\n");
        return -1;
    }

    uint8_t prefixlen = _key->prefixlen;
    uint8_t *data = _key->data;
    uint16_t *tbl_24 = _tbl->tbl_24;
    uint16_t *tbl_long = _tbl->tbl_long;

    if(!tbl_24 || !tbl_long || !data || prefixlen > TBL_PLEN_MAX ||
        _tbl->n_entries >= _tbl->max_entries){
        //printf("Invalid secondary tables or prefixlen\n");
        return -1;
    }

    _tbl->n_entries ++;

    //If prefixlen is smaller than 24, simply store the value in tbl_24, in
    //entries indexed from data[0...2] up to data[0].data[1].255
    if(prefixlen < 24){
        size_t first_index = tbl_24_extract_first_index(data);
        size_t last_index = tbl_24_extract_last_index(_key);

        //fill all entries between first index and last index with value if
        //these entries don't have a longer prefix associated with them
        for(int i = first_index; i <= last_index; i++){
            if(!tbl_24_entry_flag(tbl_24[i]) &&
                tbl_24_entry_plen(tbl_24[i]) <= prefixlen)
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
        size_t tbl_24_index = tbl_24_extract_first_index(data);
        if(tbl_24_entry_flag(tbl_24[tbl_24_index])){
            base_index = tbl_24_entry_val(tbl_24[tbl_24_index]);
        } else {
            //generate next index and store it in tbl_24
            base_index = _tbl->tbl_long_index;
            _tbl->tbl_long_index ++;
            tbl_24[tbl_24_index] = base_index;
            tbl_24[tbl_24_index] = tbl_24_entry_set_flag(tbl_24[tbl_24_index]);
            //record the prefix length associated with the entry
            tbl_24[tbl_24_index] = tbl_24_entry_put_plen(tbl_24[tbl_24_index],
                                                            prefixlen);
        }

        //The last byte in data is used as the starting offset for tbl_long
        //indexes
        size_t first_index = tbl_long_extract_first_index(data, base_index);
        size_t last_index = tbl_long_extract_last_index(_key, base_index);

        //Store value in tbl_long entries indexed from value*256+offset up to
        //value*256+255
        for(int i = first_index; i <= last_index; i++){
            if(tbl_long_entry_plen(tbl_long[i]) <= prefixlen){
                tbl_long[i] = value;
                //record length of the prefix associated with the entry
                tbl_long[i] = tbl_long_entry_put_plen(tbl_long[i], prefixlen);
            }
        }
    }

    return 0;
}

int tbl_delete_elem(struct tbl *_tbl, struct key *_key)
{
    if(!_tbl || !_key){
        return -1;
    }

    uint8_t prefixlen = _key->prefixlen;
    uint8_t *data = _key->data;
    uint16_t *tbl_24 = _tbl->tbl_24;
    uint16_t *tbl_long = _tbl->tbl_long;

    if(!tbl_24 || !tbl_long || !data || prefixlen > TBL_PLEN_MAX){
        return -1;
    }

    size_t tbl_24_index = tbl_24_extract_first_index(data);

    if(tbl_24_entry_flag(tbl_24[tbl_24_index])) {
        //tbl_24 contains a base index for tbl_long
        size_t base_index = tbl_24[tbl_24_index];
        uint8_t offset = data[3];

        //remove all entries in tbl_long that match the key in argument and have
        //the same prefix length as the key in argument

        uint16_t replacement = tbl_long_find_replacement(_key, _tbl, base_index);

        for(int i = offset; i < TBL_LONG_OFFSET_MAX; i++){
            size_t index = base_index * TBL_LONG_FACTOR + i;
            if(tbl_long_entry_plen(tbl_long[index]) == prefixlen){
                tbl_long[index] = replacement;
            }
        }

        //then, remove the entry from tbl_24
        tbl_24[tbl_24_index] = 0;
    } else {
        //tbl_24 contains the next hop, just remove entries from the tbl_24 that
        //match the key given in argument and have the same prefix lentgh as the
        //key in argument

        uint16_t replacement = tbl_24_find_replacement(_key, _tbl);

        for(int i = tbl_24_extract_first_index(data);
            i <= tbl_24_extract_last_index(_key); i++){
            if(tbl_24_entry_plen(tbl_24[i]) == prefixlen){
                tbl_24[i] = replacement;
            }
        }
    }

    _tbl->n_entries --;
    return 0;
}

int tbl_lookup_elem(struct tbl *_tbl, struct key *_key)
{
    if(!_tbl || !_key){
        return -1;
    }

    uint8_t prefixlen = _key->prefixlen;
    uint8_t *data = _key->data;
    uint16_t *tbl_24 = _tbl->tbl_24;
    uint16_t *tbl_long = _tbl->tbl_long;

    if(!tbl_24 || !tbl_long || !data || prefixlen > TBL_PLEN_MAX){
        return -1;
    }

    size_t first_index = tbl_24_extract_first_index(data);

    if(prefixlen < TBL_24_PLEN_MAX){
        //the next hop is stored directly in tbl_24, just return the value in
        //the entry
        return tbl_24_entry_val(tbl_24[first_index]);
    } else {
        //the value stored in tbl_24 is a base index for tbl_long, go find the
        //next hop in tbl_long

        //get the right tbl_long index from the value in tbl_24 and the data in
        //the key argument
        size_t base_index = tbl_24[first_index];
        uint8_t offset = data[3];
        size_t index = base_index * TBL_LONG_FACTOR + offset;

        //return the value in the entry at the computed index
        return tbl_long_entry_val(tbl_long[index]);
    }
}
