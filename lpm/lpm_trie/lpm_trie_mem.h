#include "../../../vignat/nf/lib/containers/double-chain.h"
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
	struct lpm_trie_node *l_child;
	struct lpm_trie_node *r_child;
	int mem_index;
	uint32_t prefixlen;
	uint32_t flags;
	int *value;
	uint8_t data[LPM_DATA_SIZE];
};

struct lpm_trie {
	struct lpm_trie_node *root;
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
	predicate trie_p(struct lpm_trie *trie) =
		malloc_block_lpm_trie(trie) &*&
		trie->root |-> _ &*&
		trie->n_entries |-> _ &*&
		trie->max_entries |-> ?max &*&
		max > 0 &*&
		trie->dchain |-> ?dchain &*&
		double_chainp(?ch, dchain) &*&
		trie->node_mem_blocks |-> ?mem_blocks &*&
		malloc_block_chars((void*)mem_blocks,
		                   (sizeof(struct lpm_trie_node) * max)) &*&
		nodes_p(mem_blocks, max);

	predicate node_p(struct lpm_trie_node* node) =
		node->l_child |-> _ &*&
		node->r_child |-> _ &*&
		node->mem_index |-> _ &*&
		node->prefixlen |-> _ &*&
		node->flags |-> _ &*&
		node->value |-> _ &*&
		node->data[0..LPM_DATA_SIZE] |-> _ ;

	predicate nodes_p(struct lpm_trie_node* node, int count) =
		count == 0 ?
			true
		:
			node_p(node) &*& nodes_p(node + 1, count - 1);

	predicate valid_ptrs(uintptr_t *ptr_stack, void *mem_blocks, int i) =
		i == 0 ?
			true
		:
			ptr_stack + i*sizeof(uintptr_t) ==
			mem_blocks + i*sizeof(struct lpm_trie_node) &*&
			valid_ptrs(ptr_stack, mem_blocks, i-1);

	predicate valid_dchain(struct lpm_trie *trie) =
		trie->dchain |-> ?dchain &*&
		double_chainp(?ch, dchain) &*&
		dchain_high_fp(ch) <= 1 &*&
		dchain_index_range_fp(ch) == trie->max_entries;

	predicate valid_mem_index(struct lpm_trie *trie, struct lpm_trie_node *node) =
		trie->dchain |-> ?dchain &*&
		double_chainp(?ch, dchain) &*&
		node->mem_index |-> ?i &*&
		0 <= i &*& i < dchain_index_range_fp(ch);
@*/

/*@
	lemma void node_layout_assumptions(struct lpm_trie_node *node);
	requires true;
	ensures sizeof(struct lpm_trie_node) == 2*sizeof(struct lpm_trie_node *) +
	                                        sizeof(int) +
	                                        2*sizeof(uint32_t) +
	                                        LPM_DATA_SIZE*sizeof(uint8_t) +
	                                        sizeof(int *) &*&
	        (void*) &(node->l_child) + sizeof(struct lpm_trie_node *) ==
	        (void*) &(node->r_child) &*&
	        (void*) &(node->r_child) + sizeof(struct lpm_trie_node *) ==
	        (void*) &(node->mem_index) &*&
	        (void*) &(node->mem_index) + sizeof(int) ==
	        (void*) &(node->prefixlen) &*&
	        (void*) &(node->prefixlen) + sizeof(uint32_t) ==
	        (void*) &(node->flags) &*&
	        (void*) &(node->flags) + sizeof(uint32_t) == (void*) &(node->value) &*&
	        (void*) &(node->value) + sizeof(int *) ==
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

	lemma void bytes_to_node(void* node)
	requires chars((void*)node, sizeof(struct lpm_trie_node), ?chs);
	ensures node_p(node);
	{
		struct lpm_trie_node* node_s = node;
		node_layout_assumptions(node_s);
		chars_split((void*) node, sizeof(void*));
		chars_to_pointer((void*) &(node_s->l_child));
		chars_split((void*) node + sizeof(void*), sizeof(void*));
		chars_to_pointer((void*) &(node_s->r_child));
	 	chars_split((void*) node + 2*sizeof(void*), sizeof(int));
		chars_to_integer((void*) &(node_s->mem_index));
		chars_split((void*) node + 2*sizeof(void*) + sizeof(int), sizeof(uint32_t));
		chars_to_u_integer((void*) &(node_s->prefixlen));
		chars_split((void*) node + 2*sizeof(void*) + sizeof(int) + sizeof(uint32_t),
		            sizeof(uint32_t));
		chars_to_u_integer((void*) &(node_s->flags));
		chars_split((void*) node + 2*sizeof(void*) + sizeof(int) + 2*sizeof(uint32_t),
		            sizeof(void *));
		chars_to_pointer((void*) &(node_s->value));
		chars_split((void*) node + 2*sizeof(void*) + sizeof(int) + 2*sizeof(uint32_t) +
		            sizeof(void*), LPM_DATA_SIZE*sizeof(uint8_t));
		close lpm_trie_node_l_child(node, _);
		close lpm_trie_node_r_child(node, _);
		close lpm_trie_node_mem_index(node, _);
		close lpm_trie_node_prefixlen(node, _);
		close lpm_trie_node_flags(node, _);
		close lpm_trie_node_value(node, _);
		//close lpm_trie_node_data(node, _);
		close node_p(node);
	}

	lemma void bytes_to_nodes(void* node, nat len)
	requires chars((void*)node, int_of_nat(len)*sizeof(struct lpm_trie_node), ?chs);
	ensures nodes_p(node, int_of_nat(len));
	{
		switch(len) {
			case zero:
				close nodes_p(node, 0);
				break;
			case succ(n):
				assert 1 <= int_of_nat(len);
				mul_mono(1, int_of_nat(len), sizeof(struct lpm_trie_node));
				assert sizeof(struct lpm_trie_node) <= int_of_nat(len)*sizeof(struct lpm_trie_node);
				chars_split(node, sizeof(struct lpm_trie_node));
				assert int_of_nat(len)*sizeof(struct lpm_trie_node) - sizeof(struct lpm_trie_node) ==
				       (int_of_nat(len)-1)*sizeof(struct lpm_trie_node);
				assert int_of_nat(len)-1 == int_of_nat(n);
				mul_subst(int_of_nat(len)-1, int_of_nat(n), sizeof(struct lpm_trie_node));
				assert int_of_nat(len)*sizeof(struct lpm_trie_node) - sizeof(struct lpm_trie_node) ==
				       int_of_nat(n)*sizeof(struct lpm_trie_node);
				bytes_to_nodes(node+sizeof(struct lpm_trie_node), n);
				bytes_to_node(node);
				close nodes_p(node, int_of_nat(len));
		}
	}
	
	lemma void node_to_bytes(struct lpm_trie_node *node)
	requires node_p(node);
	ensures chars((void*) node, sizeof(struct lpm_trie_node), ?cs);
	{
		void *_node = node;
		node_layout_assumptions(node);
		open node_p(node);
		open lpm_trie_node_l_child(node, _);
		pointer_to_chars((void*) &node->l_child);
		open lpm_trie_node_r_child(node, _);
		pointer_to_chars((void*) &node->r_child);
		chars_join(_node);
		open lpm_trie_node_mem_index(node, _);
		integer_to_chars((void*) &node->mem_index);
		chars_join(_node);
		open lpm_trie_node_prefixlen(node, _);
		u_integer_to_chars((void*) &node->prefixlen);
		chars_join(_node);
		open lpm_trie_node_flags(node, _);
		u_integer_to_chars((void*) &node->flags);
		chars_join(_node);
		open lpm_trie_node_value(node, _);
		pointer_to_chars((void*) &node->value);
		chars_join(_node);
		uchars_to_chars((void*) node->data);
		chars_join(_node);
	}
	
	lemma void nodes_to_bytes(struct lpm_trie_node *first, nat len)
	requires nodes_p(first, int_of_nat(len));
	ensures chars((void*) first, int_of_nat(len)*sizeof(struct lpm_trie_node), ?cs);
	{
		switch(len) {
			case zero: 
				open nodes_p(first, int_of_nat(len));
				close chars((void*) first, 0, _);
				break;
			case succ(n):
				assert 1 <= int_of_nat(len);
				mul_mono(1, int_of_nat(len), sizeof(struct lpm_trie_node));
				assert sizeof(struct lpm_trie_node) <= int_of_nat(len)*sizeof(struct lpm_trie_node);
				open nodes_p(first, int_of_nat(len));
				assert int_of_nat(len)*sizeof(struct lpm_trie_node) - sizeof(struct lpm_trie_node) ==
				       (int_of_nat(len)-1)*sizeof(struct lpm_trie_node);
				assert int_of_nat(len)-1 == int_of_nat(n);
				mul_subst(int_of_nat(len)-1, int_of_nat(n), sizeof(struct lpm_trie_node));
				assert int_of_nat(len)*sizeof(struct lpm_trie_node) - sizeof(struct lpm_trie_node) ==
				       int_of_nat(n)*sizeof(struct lpm_trie_node); 
				nodes_to_bytes(first + 1, n);
				node_to_bytes(first);
				chars_join((void*) first);
				//close chars((void*) first, int_of_nat(len) * sizeof(struct lpm_trie_node), _);
					
		}
	}

	lemma void extract_node(struct lpm_trie_node *node, int i)
	requires nodes_p(node, ?size) &*& 0 <= i &*& i < size;
  	ensures nodes_p(node, i) &*&
	        node_p(node+i) &*&
	        nodes_p(node+i+1, size-i-1);
	{
		open nodes_p(node, size);
		if(i == 0){
		} else {
			extract_node(node+1, i-1);
		}
		close nodes_p(node, i);
	}

	lemma void nodes_join(struct lpm_trie_node *node);
	requires nodes_p(node, ?n) &*& nodes_p(node+n, ?n0);
	ensures nodes_p(node, n+n0);

	lemma void close_nodes(struct lpm_trie_node *first, int i, int size)
	requires size > i &*& i >= 0 &*&
	         (i == 0 ? true : nodes_p(first, i)) &*&
	         node_p(first+i) &*&
	         nodes_p(first+i+1, size-i-1);
	ensures nodes_p(first, size);
	{
		if(i == 0){
			close nodes_p(first, size);
		} else {
			close nodes_p(first+i, size-i);
			nodes_join(first);
		}
	}
@*/

struct lpm_trie_node *lpm_trie_node_alloc(struct lpm_trie *trie, int *value);
/*@ requires trie_p(trie) &*& valid_dchain(trie); @*/
/*@ ensures trie_p(trie) &*&
            result == NULL ? true : node_p(result) &*&
            valid_dchain(trie); @*/

struct lpm_trie *lpm_trie_alloc(size_t max_entries);
/*@ requires max_entries > 0 &*& max_entries <= IRANG_LIMIT; @*/
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
