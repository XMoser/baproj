#include <stdint.h>
#include <stdlib.h>
#include <string.h>
//#include <errno.h>
#include <stddef.h>

#define LPM_TREE_NODE_FLAG_IM	1
#define LPM_DATA_SIZE_MAX	256
#define LPM_DATA_SIZE_MIN	1
#define LPM_VAL_SIZE_MAX	(SIZE_MAX - LPM_DATA_SIZE_MAX - \
				 				sizeof(struct lpm_trie_node))
#define LPM_VAL_SIZE_MIN	1
#define LPM_DATA_SIZE 		4
#define LPM_VALUE_SIZE		1
#define LPM_PLEN_MAX		32

#define min(a, b) ((a<b) ? (a) : (b))

struct lpm_trie_node;

struct lpm_trie_node {
	struct lpm_trie_node *child[2];
	uint32_t prefixlen;
	uint32_t flags;
	uint8_t data[LPM_DATA_SIZE];
	uint8_t value[LPM_VALUE_SIZE];
};

struct lpm_trie {
	struct lpm_trie_node *root;
	size_t n_entries;
    size_t max_entries;
	struct lpm_trie_node *node_mem_blocks;
	struct lpm_trie_node **node_ptr_stack;
	size_t next_ptr_index;
};

struct lpm_trie_key {
    uint32_t prefixlen;
    uint8_t data[LPM_DATA_SIZE];
};

struct lpm_trie_node *lpm_trie_node_alloc(struct lpm_trie *trie,
						 					const uint8_t *value);
/*@ requires true; @*/
/*@ ensures true; @*/

struct lpm_trie *lpm_trie_alloc(size_t max_entries);
/*@ requires true; @*/
/*@ ensures true; @*/

void trie_free(struct lpm_trie *trie);
/*@ requires true; @*/
/*@ ensures true; @*/

int extract_bit(const uint8_t *data, size_t index);
/*@ requires true; @*/
/*@ ensures true; @*/

size_t longest_prefix_match(const struct lpm_trie_node *node,
                   			const struct lpm_trie_key *key);
/*@ requires true; @*/
/*@ ensures true; @*/

uint8_t *trie_lookup_elem(struct lpm_trie *trie, void *_key);
/*@ requires true; @*/
/*@ ensures true; @*/

int trie_update_elem(struct lpm_trie *trie, void *_key, uint8_t *value,
					 uint64_t flags);
/*@ requires true; @*/
/*@ ensures true; @*/

int trie_delete_elem(struct lpm_trie *trie, void *_key);
/*@ requires true; @*/
/*@ ensures true; @*/

int trie_get_next_key(struct lpm_trie *trie, void *_key, void *_next_key);
/*@ requires true; @*/
/*@ ensures true; @*/

/**
 * fls - find last (most-significant) bit set
 * @x: the word to search
 *
 * This is defined the same way as ffs.
 * Note fls(0) = 0, fls(1) = 1, fls(0x80000000) = 32.
 */
static int fls(unsigned int x)
/*@ requires true; @*/
/*@ ensures true; @*/
{
	int r = 32;

	if (!x)
		return 0;
	if (!(x & 0xffff0000u)) {
		x <<= 16;
		r -= 16;
	}
	if (!(x & 0xff000000u)) {
		x <<= 8;
		r -= 8;
	}
	if (!(x & 0xf0000000u)) {
		x <<= 4;
		r -= 4;
	}
	if (!(x & 0xc0000000u)) {
		x <<= 2;
		r -= 2;
	}
	if (!(x & 0x80000000u)) {
		x <<= 1;
		r -= 1;
	}
	return r;
}
