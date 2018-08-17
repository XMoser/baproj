#include <stdint.h>

#define TBL_LONG_OFFSET_MAX 256
#define TBL_LONG_FACTOR 256
#define TBL_24_INDEX_MASK 1 << 16
#define TBL_24_PLEN_MASK 0x7C00

struct tbl{
    uint16_t *tbl_24;
    uint8_t *tbl_long;
}

struct key{
    uint32_t data;
    size_t prefixlen;
}

int tbl_update_elem(struct tbl *_tbl, struct key *_key, uint8_t value);

int tbl_delete_elem(struct tbl *_tbl, struct key *_key);

int tbl_lookup_elem(struct tbl *_tbl, struct key *_key);
