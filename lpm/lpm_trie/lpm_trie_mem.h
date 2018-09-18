#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stddef.h>

//@ #include "arith.gh"
//@ #include <nat.gh>

#define SIZE_MAX 65535
#define LPM_TREE_NODE_FLAG_IM	1
#define LPM_DATA_SIZE 		4
#define LPM_PLEN_MAX		32

#define min(a, b) ((a<b) ? (a) : (b))

struct lpm_trie_node;

struct lpm_trie_node {
	//struct lpm_trie_node *child[2];
	struct lpm_trie_node l_child;
	struct lpm_trie_node r_child;
	uint32_t prefixlen;
	uint32_t flags;
	uint8_t data[LPM_DATA_SIZE];
	int *value;
};

struct lpm_trie {
	struct lpm_trie_node *root;
	size_t n_entries;
	size_t max_entries;
	void *node_mem_blocks;
	uintptr_t *node_ptr_stack;
	size_t next_ptr_index;
};

struct lpm_trie_key {
	uint32_t prefixlen;
	uint8_t data[LPM_DATA_SIZE];
};

/*@
	predicate trie_p(struct lpm_trie *trie) =
		malloc_block_lpm_trie(trie) &*&
		trie->root |-> _ &*&
		trie->n_entries |-> _ &*&
		trie->max_entries |-> ?max &*&
		trie->node_mem_blocks |-> ?mem_blocks &*&
		malloc_block_chars((void*)mem_blocks,
		                   (sizeof(struct lpm_trie_node) * max)) &*&
		chars(mem_blocks, (sizeof(struct lpm_trie_node) * max), _) &*&
		trie->node_ptr_stack |-> ?ptr_stack &*&
		malloc_block(ptr_stack, sizeof(struct lpm_trie_node*) * max) &*&
		uints(ptr_stack, max, _) &*&
		trie->next_ptr_index |-> ?next_pi &*&
		next_pi >= 0 && next_pi < max;

	predicate node_p(struct lpm_trie_node* node) =
		node->l_child |-> _ &*&
		node->r_child |-> _ &*&
		node->prefixlen |-> _ &*&
		node->flags |-> _ &*&
		node->data |-> _ &*&
		node->value |-> _;

	predicate nodes_p(struct lpm_trie_node* node, int count) =
		count == 0 ?
			true
		:
			node_p(node) &*& nodes_p(node + 1, count - 1);
@*/

/*@
	lemma void node_layout_assumptions(struct lpm_trie_node *node);
	requires true;
	ensures sizeof(struct lpm_trie_node) == 2*sizeof(struct lpm_trie_node *) +
	                                        2*sizeof(uint32_t) +
	                                        LPM_DATA_SIZE*sizeof(uint8_t) +
	                                        sizeof(int *) &*&
	        (void*) node->l_child + sizeof(struct lpm_trie_node *) ==
			(void*) node->r_child &*&
			(void*) node->r_child + sizeof(strut lpm_trie_node *) ==
	        (void*) &(node->prefixlen) &*&
	        (void*) &(node->prefixlen) + sizeof(uint32_t) ==
	        (void*) &(node->flags) &*&
	        (void*) &(node->flags) + sizeof(uint32_t) == (void*) node->data &*&
	        (void*) node->data + LPM_DATA_SIZE*sizeof(uint8_t) ==
	        (void*) &(node->value);
@*/

/*@
	lemma void bytes_to_node(void* node)
	requires chars((void*)node, sizeof(struct lpm_trie_node), ?chs);
	ensures node_p(node);
	{
		struct lpm_trie_node* node_s = node;
		node_layout_assumptions(node_s);
		chars_split((void*) node, sizeof(void*));
		chars_to_pointer((void*) node_s->l_child);
		chars_split((void*) node + sizeof(void*), sizeof(void*));
		chars_to_pointer((void*) node_s->r_child);
	 	chars_split((void*) node + 2*sizeof(void*), sizeof(uint32_t));
		chars_to_u_integer(node_s->prefixlen);
		chars_split((void*) node + 2*sizeof(void*) + sizeof(uint32_t),
		            sizeof(uint32_t));
		chars_to_u_integer(node_s->flags);
		chars_split((void*) node + 2*sizeof(void*) + 2*sizeof(uint32_t),
		            LPM_DATA_SIZE*sizeof(uint8_t));
		chars_split((void*) node + 2*sizeof(void*) + 2*sizeof(uint32_t) +
		            LPM_DATA_SIZE*sizeof(uint8_t), sizeof(void*));
		chars_to_pointer((void*) node_s->value);
		close lpm_trie_node_child(node, _);
		close lpm_trie_node_prefixlen(node, _);
		close lpm_trie_node_flags(node, _);
		close lpm_trie_node_data(node, _);
		close lpm_trie_node_value(node, _);
	}

	lemma void bytes_to_nodes(void* node, nat len)
	requires chars((void*)node, int_of_nat(len)*sizeof(struct lpm_trie_node), ?chs);
	ensures nodes_p(node, int_of_nat(len));
	{
		switch(len) {
			case zero:
				close nodes_p(dc, 0, nil);
				break;
			case succ(n):
				assert 1 <= int_of_nat(len);
				mul_mono(1, int_of_nat(len), sizeof(struct lpm_trie_node));
				assert sizeof(struct lpm_trie_node) <= int_of_nat(len)*sizeof(struct lpm_trie_node);
				chars_split(dc, sizeof(struct lpm_trie_node));
				assert int_of_nat(len)*sizeof(struct lpm_trie_node) - sizeof(struct lpm_trie_node) ==
				       (int_of_nat(len)-1)*sizeof(struct lpm_trie_node);
				assert int_of_nat(len)-1 == int_of_nat(n);
				mul_subst(int_of_nat(len)-1, int_of_nat(n), sizeof(struct lpm_trie_node));
				assert int_of_nat(len)*sizeof(struct lpm_trie_node) - sizeof(struct lpm_trie_node) ==
				       int_of_nat(n)*sizeof(struct lpm_trie_node);
				bytes_to_nodes(dc+sizeof(struct lpm_trie_node), n);
				bytes_to_node(dc);
				close nodes_p(dc, int_of_nat(len));
		}
	}

@*/

struct lpm_trie_node *lpm_trie_node_alloc(struct lpm_trie *trie, int *value);
/*@ requires trie_p(trie); @*/
/*@ ensures trie_p(trie); @*/

struct lpm_trie *lpm_trie_alloc(size_t max_entries);
/*@ requires max_entries > 0; @*/
/*@ ensures result == NULL ? true : trie_p(result); @*/

void trie_free(struct lpm_trie *trie);
/*@ requires trie_p(trie); @*/
/*@ ensures true; @*/

int extract_bit(const uint8_t *data, size_t index);
/*@ requires true; @*/
/*@ ensures true; @*/

size_t longest_prefix_match(const struct lpm_trie_node *node,
                            const struct lpm_trie_key *key);
/*@ requires malloc_block_lpm_trie_key(key); @*/
/*@ ensures malloc_block_lpm_trie_key(key); @*/

int *trie_lookup_elem(struct lpm_trie *trie, struct lpm_trie_key *key);
/*@ requires trie_p(trie) &*&
             malloc_block_lpm_trie_key(key); @*/
/*@ ensures trie_p(trie) &*&
            malloc_block_lpm_trie_key(key); @*/

int trie_update_elem(struct lpm_trie *trie, struct lpm_trie_key *key, int *value);
/*@ requires trie_p(trie) &*&
             malloc_block_lpm_trie_key(key); @*/
/*@ ensures trie_p(trie) &*&
            malloc_block_lpm_trie_key(key); @*/

int trie_delete_elem(struct lpm_trie *trie, struct lpm_trie_key *key);
/*@ requires trie_p(trie) &*&
             malloc_block_lpm_trie_key(key); @*/
/*@ ensures trie_p(trie) &*&
            malloc_block_lpm_trie_key(key); @*/

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
