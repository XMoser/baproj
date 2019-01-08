#include "../lib/double-chain.h"
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stddef.h>
#include <stdbool.h>

//@ #include <list.gh>
//@ #include "../arith.gh"
//@ #include <nat.gh>
//@ #include <bitops.gh>

#define TRIE_SIZE_MAX 65535
#define MAX_NODE_SIZE 500
#define LPM_TREE_NODE_FLAG_IM	1
#define LPM_DATA_SIZE 		4
#define LPM_PLEN_MAX		32
#define INVALID_NODE_ID -1
#define INVALID_VAL -1

#define min(a, b) ((a<b) ? (a) : (b))

struct lpm_trie_node;

struct lpm_trie_node {
	int l_child;
	int r_child;
	int mem_index;
	int has_l_child;
	int has_r_child;
	uint32_t prefixlen;
	uint32_t flags;
	int value;
	uint8_t data[LPM_DATA_SIZE];
};

struct lpm_trie {
	int root;
	size_t n_entries;
	size_t max_entries;
	struct DoubleChain *dchain;
	struct lpm_trie_node *node_mem_blocks;
};

struct lpm_trie_key {
	uint32_t prefixlen;
	uint8_t data[LPM_DATA_SIZE];
};

/*@
	predicate trie_p(struct lpm_trie *trie, int n, int max) =
		malloc_block_lpm_trie(trie) &*&
		trie->root |-> ?r &*&
		trie->n_entries |-> n &*&
		n >= 0 &*&
		(n == 0 ? true : r >= 0 &*& r < max) &*&
		trie->max_entries |-> max &*&
		max > 0 &*&
		IRANG_LIMIT >= max &*&
		trie->dchain |-> ?dchain &*&
		double_chainp(?ch, dchain) &*&
		dchain_index_range_fp(ch) == max &*&
		dchain_high_fp(ch) <= 1 &*&
		trie->node_mem_blocks |-> ?mem_blocks &*&
		(void*)0 < ((void*)(mem_blocks)) &*&
		(void*)(mem_blocks + max) <= (char*)UINTPTR_MAX &*&
		malloc_block_chars((void*)mem_blocks,
		                   (sizeof(struct lpm_trie_node) * max)) &*&
		nodes_p(mem_blocks, max, max);

	predicate node_im_p(struct lpm_trie_node *node) =
		node->l_child |-> _ &*&
		node->r_child |-> _ &*&
		node->mem_index |-> _ &*&
		node->has_l_child |-> _ &*&
		node->has_r_child |-> _ &*&
		node->prefixlen |-> _ &*&
		node->flags |-> _ &*&
		node->value |-> _ &*&
		node->data[0..LPM_DATA_SIZE] |-> _;

	predicate node_p(struct lpm_trie_node* node, int max_i) =
		node->l_child |-> ?l &*&
		node->r_child |-> ?r &*&
		node->mem_index |-> ?m &*&
		node->has_l_child |-> _ &*&
		node->has_r_child |-> _ &*&
		node->prefixlen |-> _ &*&
		node->flags |-> _ &*&
		node->value |-> _ &*&
		node->data[0..LPM_DATA_SIZE] |-> _ &*&
		l >= 0 &*& l < max_i &*&
		r >= 0 &*& r < max_i &*&
		m >= 0 &*& m < max_i;

	predicate key_p(struct lpm_trie_key *key) =
		malloc_block_lpm_trie_key(key) &*&
		key->prefixlen |-> _ &*&
		key->data[0..LPM_DATA_SIZE] |-> _;

	predicate nodes_im_p(struct lpm_trie_node *node, int count) =
		count == 0 ?
			true
		:
			node_im_p(node) &*& nodes_im_p(node + 1, count - 1);

	predicate nodes_p(struct lpm_trie_node* node, int count, int max_i) =
		count == 0 ?
			true
		:
			node_p(node, max_i) &*& nodes_p(node+1, count-1, max_i);
@*/

/*@
	lemma void node_layout_assumptions(struct lpm_trie_node *node);
	requires true;
	ensures sizeof(struct lpm_trie_node) == 5*sizeof(int) +
	                                        2*sizeof(uint32_t) +
	                                        LPM_DATA_SIZE*sizeof(uint8_t) +
	                                        sizeof(int *) &*&
	        (void*) &(node->l_child) + sizeof(int) ==
	        (void*) &(node->r_child) &*&
	        (void*) &(node->r_child) + sizeof(int) ==
	        (void*) &(node->mem_index) &*&
	        (void*) &(node->mem_index) + sizeof(int) ==
	        (void*) &(node->has_l_child) &*&
	        (void*) &(node->has_l_child) + sizeof(int) ==
	        (void*) &(node->has_r_child) &*&
	        (void*) &(node->has_r_child) + sizeof(int) ==
	        (void*) &(node->prefixlen) &*&
	        (void*) &(node->prefixlen) + sizeof(uint32_t) ==
	        (void*) &(node->flags) &*&
	        (void*) &(node->flags) + sizeof(uint32_t) ==
	        (void*) &(node->value) &*&
	        (void*) &(node->value) + sizeof(int*) ==
	        (void*) node->data;
@*/

/*@
	lemma void dchain_allocate_range_time(struct DoubleChain *dchain, int max, int ni);
	requires double_chainp(?ch, dchain) &*&
	         dchain_index_range_fp(ch) == max &*&
	         dchain_high_fp(ch) <= 1;
	ensures double_chainp(dchain_allocate_fp(ch, ni, 1), dchain) &*&
	        dchain_index_range_fp(dchain_allocate_fp(ch, ni, 1)) == max &*&
	        dchain_high_fp(dchain_allocate_fp(ch, ni, 1)) <= 1;

	fixpoint bool char_equals(int i, char c){
		return i == c;
	}

	lemma void bytes_to_node_im(void* node);
	requires chars((void*)node, sizeof(struct lpm_trie_node), ?chs);
	ensures node_im_p(node);

	lemma void bytes_to_nodes_im(void* node, nat len);
	requires chars((void*)node, int_of_nat(len)*sizeof(struct lpm_trie_node), ?chs);
	ensures nodes_im_p(node, int_of_nat(len));

	lemma void node_to_bytes(struct lpm_trie_node *node);
	requires node_p(node, ?max_i);
	ensures chars((void*) node, sizeof(struct lpm_trie_node), ?cs);

	lemma void nodes_to_bytes(struct lpm_trie_node *first, nat len);
	requires nodes_p(first, int_of_nat(len), ?max_i);
	ensures chars((void*) first, int_of_nat(len)*sizeof(struct lpm_trie_node), ?cs);

	lemma void extract_node(struct lpm_trie_node *node, int i);
	requires nodes_p(node, ?size, ?max_i) &*& 0 <= i &*& i < size;
  	ensures nodes_p(node, i, max_i) &*&
	        node_p(node+i, max_i) &*&
	        nodes_p(node+i+1, size-i-1, max_i);

	lemma void extract_im_node(struct lpm_trie_node *node, int i);
	requires nodes_im_p(node, ?size) &*& 0 <= i &*& i < size;
  	ensures nodes_im_p(node, i) &*&
	        node_im_p(node+i) &*&
	        nodes_im_p(node+i+1, size-i-1);

	lemma void nodes_join(struct lpm_trie_node *node);
	requires nodes_p(node, ?n, ?max_i) &*& nodes_p(node+n, ?n0, max_i);
	ensures nodes_p(node, n+n0, max_i);

	lemma void close_nodes(struct lpm_trie_node *first, int i, int size);
	requires size > i &*& i >= 0 &*&
	         nodes_p(first, i, ?max_i) &*&
	         node_p(first+i, max_i) &*&
	         nodes_p(first+i+1, size-i-1, max_i);
	ensures nodes_p(first, size, max_i);
@*/

int lpm_trie_node_alloc(struct lpm_trie *trie, int value);
/*@ requires trie_p(trie, ?n, ?max_i); @*/
/*@ ensures trie_p(trie, n, max_i); @*/

struct lpm_trie *lpm_trie_alloc(size_t max_entries);
/*@ requires max_entries > 0 &*& max_entries <= IRANG_LIMIT &*&
             sizeof(struct lpm_trie_node) < MAX_NODE_SIZE; @*/
/*@ ensures result == NULL ? true : trie_p(result, 0, max_entries); @*/

void trie_free(struct lpm_trie *trie);
/*@ requires trie_p(trie, _, _); @*/
/*@ ensures true; @*/

bool extract_bit(const uint8_t *data, size_t index);
/*@ requires data[0..LPM_DATA_SIZE] |-> _ &*&
             index >= 0 &*& LPM_DATA_SIZE > index / 8; @*/
/*@ ensures data[0..LPM_DATA_SIZE] |-> _;@*/

size_t longest_prefix_match(const struct lpm_trie_node *node,
                            const struct lpm_trie_key *key);
/*@ requires node_p(node, ?max_i) &*& key_p(key); @*/
/*@ ensures node_p(node, max_i) &*& key_p(key); @*/

int trie_lookup_elem(struct lpm_trie *trie, struct lpm_trie_key *key);
/*@ requires trie_p(trie, ?n, ?max_i) &*& key_p(key) &*& n > 0; @*/
/*@ ensures trie_p(trie, n, max_i) &*& key_p(key); @*/

int trie_update_elem(struct lpm_trie *trie, struct lpm_trie_key *key, int value);
/*@ requires trie_p(trie, ?n1, ?max_i) &*& n1 < max_i &*&
             key_p(key); @*/
/*@ ensures trie_p(trie, ?n2, max_i) &*&
            key_p(key); @*/

int trie_delete_elem(struct lpm_trie *trie, struct lpm_trie_key *key);
/*@ requires trie_p(trie, ?n, ?max_i) &*& n > 0 &*& key_p(key); @*/
/*@ ensures trie_p(trie, _, max_i) &*& key_p(key); @*/

/**
 * fls - find last (most-significant) bit set
 * @x: the word to search
 *
 * This is defined the same way as ffs.
 * Note fls(0) = 0, fls(1) = 1, fls(0x80000000) = 32.
 */
static unsigned int fls(unsigned int x)
/*@ requires true; @*/
/*@ ensures true; @*/
{
//@ assume(false);
	int r = 32;

	if (!x)
		return 0;
	if (!(x & 0xffff0000u)) {
		//@ bitand_limits(0x0000ffffu, x, nat_of_int(16));
		//@ shiftleft_limits(0x0000ffffu & x, nat_of_int(16), nat_of_int(16));
		x <<= 16;
		r -= 16;
	}
	if (!(x & 0xff000000u)) {
		//@ bitand_limits(0x00ffffffu, x, nat_of_int(24));
		//@ shiftleft_limits(0x00ffffffu & x, nat_of_int(24), nat_of_int(8));
		x <<= 8;
		r -= 8;
	}
	if (!(x & 0xf0000000u)) {
		//@ bitand_limits(0x0fffffffu, x, nat_of_int(28));
		//@ shiftleft_limits(0x0fffffffu & x, nat_of_int(28), nat_of_int(4));
		x <<= 4;
		r -= 4;
	}
	if (!(x & 0xc0000000u)) {
		//@ bitand_limits(0x1fffffffu, x, nat_of_int(30));
		//@ shiftleft_limits(0x1fffffffu & x, nat_of_int(30), nat_of_int(2));
		x <<= 2;
		r -= 2;
	}
	if (!(x & 0x80000000u)) {
		//@ bitand_limits(0x3fffffffu, x, nat_of_int(31));
		//@ shiftleft_limits(0x3fffffffu & x, nat_of_int(31), nat_of_int(1));
		x <<= 1;
		r -= 1;
	}
	return r;
}
