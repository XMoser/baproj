#include "dir-24-8-basic.h"

int extract_last_index(uint32_t data)
{
    
}

uint8_t extract_last_byte(uint32_t data)
{
    return data & 0xff;
}

int tbl_update_elem(struct tbl *_tbl, struct key *_key, uint8_t value)
{
    size_t prefixlen = _key->prefixlen;
    uint32_t data = _key->data;

    //If prefixlen is smaller than 24, simply store the value in tbl_24, in
    //entries indexed from data up to
    if(prefixlen < 24)
        int first_index = data;
        int last_index = extract_last_index(data);
    else{
        //If the prefixlen is not smaller than 24, we have to store the value
        //in tbl_long.

        //Start by storing the value to be used to index tbl_long to tbl_24 and
        //set the first bit to 1 to indicate that this value is not a next hop
        tbl->tbl_24[data] = value | TBL_24_INDEX_MASK;
        //The last byte in data is used as the starting offset for tbl_long
        //indexes
        uint8_t offset = extract_last_byte(data);

        //Store value in tbl_long entries indexed from value*256+offset up to
        //value*256+255
        for(int i = offset; i < TBL_LONG_OFFSET_MAX; i++){
            tbl->tbl_long[last_byte * TBL_LONG_FACTOR + i] = value;
        }
    }

    return 0;
}
