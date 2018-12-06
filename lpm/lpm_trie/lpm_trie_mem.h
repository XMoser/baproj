#include "lib/double-chain.h"
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stddef.h>
#include <stdbool.h>

//@ #include "list.gh"
//@ #include <listex.gh>
//@ #include "arith.gh"
//@ #include <nat.gh>

#define SIZE_MAX 65535
#define LPM_TREE_NODE_FLAG_IM	1
#define LPM_DATA_SIZE 		4
#define LPM_PLEN_MAX		32
#define INVALID_NODE_ID -1

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
	int *value;
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
	inductive node_t = node(option<int>, int, list<int>, option<int>, option<int>);
	inductive trie_t = trie(option<int>, int, int, list<node_t>);

	predicate trie_p_2(struct lpm_trie *trie, trie_t t) =
		switch(t) { case trie(tr, tn, tm, tnodes):
			return
				malloc_block_lpm_trie(trie) &*&
				trie->root |-> ?r &*&
				trie->n_entries |-> ?n &*&
				n >= 0 &*&
				n == tn &*&
				trie->max_entries |-> ?max &*&
				max > 0 &*&
				max == tm &*&
				switch(tr) {
					case none: return n == 0;
					case some(i):
						return r >= 0 &*& r < max &*& n > 0;
				} &*&
				trie->dchain |-> ?dchain &*&
				double_chainp(?ch, dchain) &*&
				dchain_index_range_fp(ch) == max &*&
				dchain_high_fp(ch) <= 1 &*&
				trie->node_mem_blocks |-> ?mem_blocks &*&
				malloc_block_chars((void*)mem_blocks,
								   (sizeof(struct lpm_trie_node) * max)) &*&
				nodes_p(mem_blocks, max, max);
		};

	predicate node_p_2(struct lpm_trie_node *node, int max, node_t n) =
		switch(n) {
			case node(lc, m, p, v, rc):
				return
					node->l_child |-> ?l_child &*&
					node->r_child |-> ?r_child &*&
					node->mem_index |-> ?mem_index &*&
					node->has_l_child |-> ?has_l &*&
					node->has_r_child |-> ?has_r &*&
					l_child >= 0 &*& l_child < max &*&
					r_child >= 0 &*& r_child < max &*&
					mem_index >= 0 &*& mem_index < max &*&
					valid_mem_indexes(l_child, r_child, mem_index,
					                  has_l, has_r, lc, rc) &*&
					node->prefixlen |-> ?plen &*&
					plen == length(p) &*&
					plen <= LPM_PLEN_MAX &*&
					node->flags |-> ?flags &*&
					node->value |-> ?val &*&
					integer(val, v) &*&
					switch(v) {
						case none: return val == NULL &*&
						                  (flags & LPM_TREE_NODE_FLAG_IM) == 1;
						case some(vv): return v == vv &*&
						                      (flags & LPM_TREE_NODE_FLAG_IM) == 0;
					} &*&
					node->data[0..LPM_DATA_SIZE] |-> _ &*&
					chars(node->data, LPM_DATA_SIZE, ?chs) &*&
					are_bits(p) &*&
					valid_data(chs, p, p);
		};

	predicate valid_mem_indexes(int l_child, int r_child, int mem_index,
	                                 int has_l, int has_r,
	                                 int m, option<int> lc, option<int> rc) =
		switch(lc) {
			case none:
				return
					switch(rc) {
						case none:
							return has_l == 0 &*& has_r == 0;
						case some(rc_id):
							return has_l == 0 &*& has_r == 1 &*&
							       r_child != mem_index &*& r_child == rc_id &*&
							       mem_index == m;
					};
			case some(lc_id):
				return
					switch(rc) {
						case none:
							return has_l == 1 &*& has_r == 0 &*&
							       l_child != mem_index &*& l_child == lc_id &*&
							       mem_index == m;
						case some(rc_id):
							return has_l == 1 &*& has_r == 1 &*&
							       l_child != mem_index &*& r_child != mem_index &*&
							       l_child != r_child &*& l_child == lc_id &*&
							       r_child == rc_id &*& mem_index == m;
					};
		};

	predicate is_bit(int i) = i == 0 || i == 1;

	predicate are_bits(list<int> is) = foreach(is, is_bit);

	predicate valid_data(list<char> data, list<int> ps, list<int> old_ps) =
		switch(ps) {
			case nil: return true;
			case cons(p, p0s):
				return bool_to_int(extract_bit(data, index_of(p, old_ps))) == p &*&
				       valid_data(data, p0s, old_ps);
		};


	fixpoint bool extract_bit(list<char> data, int index) {
		return !!(nth(index / 8, data) & (1 << (7 - (index % 8))));
	}

	fixpoint int bool_to_int(bool b) {
		return (b ? 1 : 0);
	}

	predicate nodes_p_2(struct lpm_trie_node *node, int count, int max_i,
	                    list<node_t> ns) =
		count == 0 ?
			ns == nil;
		:
			node_p_2(node, max_i, ?n) &*& nodes_p_2(node+1, count-1, max_i, ?ns0) &*&
			ns == cons(n, ns0);

	lemma void extract_node_2(struct lpm_trie_node *nodes, int i, list<node_t> ns)
	requires nodes_p_2(nodes, length(ns), ?max_i, ns) &*&
	         0 <= i &*& i < length(ns);
	ensures nodes_p_2(nodes, i, max_i, take(i, ns)) &*&
	        node_p_2(nodes+i, max_i, nth(i, ns)) &*&
	        nodes_p_2(nodes+i+1, length(ns)-i-1, max_i, drop(i+1, ns));
	{
		open nodes_p_2(nodes, length(ns), max_i, ns);
		switch(ns) {
			case nil: return;
			case cons(n, ns0):
				if(i == 0){
				} else {
					extract_node_2(nodes+1, i-1, ns0);
				}
		}
		close nodes_p_2(nodes, i, max_i, take(i, ns));
	}

	lemma void close_nodes_2(struct lpm_trie_node *nodes, int i, list<node_t> ns)
	requires length(ns) > i &*& i >= 0 &*&
	         nodes_p_2(nodes, i, ?max_i, take(i, ns)) &*&
	         node_p_2(nodes+i, max_i, nth(i, ns)) &*&
	         nodes_p_2(nodes+i+1, length(ns)-i-1, max_i, drop(i+1, ns));
	ensures nodes_p_2(nodes, length(ns), max_i, ns);
	{
		switch(ns) {
			case nil: return;
			case cons(n, ns0):
				open nodes_p_2(nodes, i, max_i, take(i, ns));
				if(i == 0) {
				} else {
					close_nodes_2(nodes+1, i-1, ns0);
				}
				close nodes_p_2(nodes, length(ns), max_i, ns);
		}
	}

	fixpoint trie_t empty_trie(int max) {
		return trie(empty, 0, max);
	}

	fixpoint node_t init_node(int id, option<int> val) {
		return node(none, id, nil, val, none);
	}
@*/

/*@
	predicate trie_p(struct lpm_trie *trie, int n, int max) =
		malloc_block_lpm_trie(trie) &*&
		trie->root |-> ?r &*&
		trie->n_entries |-> n &*&
		n >= 0 &*&
		(n == 0 ? true : r >= 0 &*& r < max) &*&
		trie->max_entries |-> max &*&
		max > 0 &*&
		trie->dchain |-> ?dchain &*&
		double_chainp(?ch, dchain) &*&
		dchain_index_range_fp(ch) == max &*&
		dchain_high_fp(ch) <= 1 &*&
		trie->node_mem_blocks |-> ?mem_blocks &*&
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
	lemma void bytes_to_node_im(void* node)
	requires chars((void*)node, sizeof(struct lpm_trie_node), ?chs);
	ensures node_im_p(node);
	{
		struct lpm_trie_node* node_s = node;
		node_layout_assumptions(node_s);
		chars_split((void*) node, sizeof(int));
		chars_to_integer((void*) &(node_s->l_child));
		chars_split((void*) node + sizeof(int), sizeof(int));
		chars_to_integer((void*) &(node_s->r_child));
	 	chars_split((void*) node + 2*sizeof(int), sizeof(int));
		chars_to_integer((void*) &(node_s->mem_index));
		chars_split((void*) node + 3*sizeof(int), sizeof(int));
		chars_to_integer((void*) &(node_s->has_l_child));
		chars_split((void*) node + 4*sizeof(int), sizeof(int));
		chars_to_integer((void*) &(node_s->has_r_child));
		chars_split((void*) node + 5*sizeof(int), sizeof(uint32_t));
		chars_to_u_integer((void*) &(node_s->prefixlen));
		chars_split((void*) node + 5*sizeof(int) + sizeof(uint32_t),
		            sizeof(uint32_t));
		chars_to_u_integer((void*) &(node_s->flags));
		chars_split((void*) node + 5*sizeof(int) + 2*sizeof(uint32_t),
		            sizeof(int*));
		chars_to_pointer((void*) &(node_s->value));
		chars_split((void*) node + 5*sizeof(int) + 2*sizeof(uint32_t) +
		            sizeof(int*), LPM_DATA_SIZE*sizeof(uint8_t));
		close lpm_trie_node_l_child(node, _);
		close lpm_trie_node_r_child(node, _);
		close lpm_trie_node_has_l_child(node, _);
		close lpm_trie_node_has_r_child(node, _);
		close lpm_trie_node_mem_index(node, _);
		close lpm_trie_node_prefixlen(node, _);
		close lpm_trie_node_flags(node, _);
		close lpm_trie_node_value(node, _);
		//close lpm_trie_node_data(node, _);
		close node_im_p(node);
	}

	lemma void bytes_to_nodes_im(void* node, nat len)
	requires chars((void*)node, int_of_nat(len)*sizeof(struct lpm_trie_node), ?chs);
	ensures nodes_im_p(node, int_of_nat(len));
	{
		switch(len) {
			case zero:
				close nodes_im_p(node, 0);
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
				bytes_to_nodes_im(node+sizeof(struct lpm_trie_node), n);
				bytes_to_node_im(node);
				close nodes_im_p(node, int_of_nat(len));
		}
	}

	lemma void node_to_bytes(struct lpm_trie_node *node)
	requires node_p(node, ?max_i);
	ensures chars((void*) node, sizeof(struct lpm_trie_node), ?cs);
	{
		void *_node = node;
		node_layout_assumptions(node);
		open node_p(node, max_i);
		open lpm_trie_node_l_child(node, _);
		integer_to_chars((void*) &node->l_child);
		open lpm_trie_node_r_child(node, _);
		integer_to_chars((void*) &node->r_child);
		chars_join(_node);
		open lpm_trie_node_mem_index(node, _);
		integer_to_chars((void*) &node->mem_index);
		chars_join(_node);
		open lpm_trie_node_has_l_child(node, _);
		integer_to_chars((void*) &node->has_l_child);
		chars_join(_node);
		open lpm_trie_node_has_r_child(node, _);
		integer_to_chars((void*) &node->has_r_child);
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
	requires nodes_p(first, int_of_nat(len), ?max_i);
	ensures chars((void*) first, int_of_nat(len)*sizeof(struct lpm_trie_node), ?cs);
	{
		switch(len) {
			case zero:
				open nodes_p(first, int_of_nat(len), max_i);
				close chars((void*) first, 0, _);
				break;
			case succ(n):
				assert 1 <= int_of_nat(len);
				mul_mono(1, int_of_nat(len), sizeof(struct lpm_trie_node));
				assert sizeof(struct lpm_trie_node) <= int_of_nat(len)*sizeof(struct lpm_trie_node);
				open nodes_p(first, int_of_nat(len), max_i);
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
	requires nodes_p(node, ?size, ?max_i) &*& 0 <= i &*& i < size;
  	ensures nodes_p(node, i, max_i) &*&
	        node_p(node+i, max_i) &*&
	        nodes_p(node+i+1, size-i-1, max_i);
	{
		open nodes_p(node, size, max_i);
		if(i == 0){
		} else {
			extract_node(node+1, i-1);
		}
		close nodes_p(node, i, max_i);
	}

	lemma void extract_im_node(struct lpm_trie_node *node, int i)
	requires nodes_im_p(node, ?size) &*& 0 <= i &*& i < size;
  	ensures nodes_im_p(node, i) &*&
	        node_im_p(node+i) &*&
	        nodes_im_p(node+i+1, size-i-1);
	{
		open nodes_im_p(node, size);
		if(i == 0){
		} else {
			extract_im_node(node+1, i-1);
		}
		close nodes_im_p(node, i);
	}

	lemma void nodes_join(struct lpm_trie_node *node);
	requires nodes_p(node, ?n, ?max_i) &*& nodes_p(node+n, ?n0, max_i);
	ensures nodes_p(node, n+n0, max_i);

	lemma void close_nodes(struct lpm_trie_node *first, int i, int size)
	requires size > i &*& i >= 0 &*&
	         nodes_p(first, i, ?max_i) &*&
	         node_p(first+i, max_i) &*&
	         nodes_p(first+i+1, size-i-1, max_i);
	ensures nodes_p(first, size, max_i);
	{
		if(i == 0){
			open nodes_p(first, i, max_i);
			close nodes_p(first, size, max_i);
		} else {
			close nodes_p(first+i, size-i, max_i);
			nodes_join(first);
		}
	}
@*/

int lpm_trie_node_alloc(struct lpm_trie *trie, int *value);
/*@ requires trie_p(trie, ?n, ?max_i); @*/
/*@ ensures trie_p(trie, n, max_i); @*/

struct lpm_trie *lpm_trie_alloc(size_t max_entries);
/*@ requires max_entries > 0 &*& max_entries <= IRANG_LIMIT; @*/
/*@ ensures result == NULL ? true : trie_p_2(result, empty_trie(max_entries)); @*/

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

int *trie_lookup_elem(struct lpm_trie *trie, struct lpm_trie_key *key);
/*@ requires trie_p(trie, ?n, ?max_i) &*& key_p(key) &*& n > 0; @*/
/*@ ensures trie_p(trie, n, max_i) &*& key_p(key); @*/

int trie_update_elem(struct lpm_trie *trie, struct lpm_trie_key *key, int *value);
/*@ requires trie_p(trie, _, ?max_i) &*&
             key_p(key) &*& integer(value, _); @*/
/*@ ensures trie_p(trie, _, max_i) &*&
            key_p(key) &*& integer(value, _); @*/

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
static int fls(unsigned int x)
/*@ requires true; @*/
/*@ ensures true; @*/
{
//@ assume(false);
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
