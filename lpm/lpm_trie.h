#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <stddef.h>

#define LPM_TREE_NODE_FLAG_IM 1

#define min(a, b) ((a<b) ? (a) : (b))

struct lpm_trie_node;

struct lpm_trie_node {
	struct lpm_trie_node *child[2];
	uint32_t prefixlen;
	uint32_t flags;
	uint8_t data[0];
};

struct lpm_trie {
	struct lpm_trie_node *root;
	size_t n_entries;
    size_t max_entries;
	size_t max_prefixlen;
	size_t data_size;
    size_t value_size;
};

struct lpm_trie_key {
    uint32_t prefixlen;
    uint8_t data[0];
};

struct lpm_trie_node *lpm_trie_node_alloc(const struct lpm_trie *trie,
						 const void *value);

struct lpm_trie *lpm_trie_alloc(size_t max_entries, size_t max_prefixlen,
                                    size_t data_size, size_t value_size);

void trie_free(struct lpm_trie *trie);

int extract_bit(const uint8_t *data, size_t index);

size_t longest_prefix_match(const struct lpm_trie *trie,
				   const struct lpm_trie_node *node,
                   const struct lpm_trie_key *key);

void *trie_lookup_elem(struct lpm_trie *trie, void *_key);

int trie_update_elem(struct lpm_trie *trie, void *_key, void *value,
                            uint64_t flags);

int trie_delete_elem(struct lpm_trie *trie, void *_key);

int trie_get_next_key(struct lpm_trie *trie, void *_key, void *_next_key);

/**
 * fls - find last (most-significant) bit set
 * @x: the word to search
 *
 * This is defined the same way as ffs.
 * Note fls(0) = 0, fls(1) = 1, fls(0x80000000) = 32.
 */
static __always_inline int fls(int x)
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
