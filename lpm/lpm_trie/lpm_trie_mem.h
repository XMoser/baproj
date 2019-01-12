#include "lib/double-chain.h"
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stddef.h>
#include <stdbool.h>

//@ #include <list.gh>
//@ #include "arith.gh"
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

//@ inductive node_t = node(node_t, int, list<int>, option<int>, node_t) | empty;
//@ inductive trie_t = trie(node_t, int, int);

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

	lemma void node_im_to_bytes(struct lpm_trie_node *node);
	requires node_im_p(node);
	ensures chars((void*) node, sizeof(struct lpm_trie_node), ?chs);

	lemma void nodes_im_to_bytes(struct lpm_trie_node *first, nat len);
	requires nodes_im_p(first, int_of_nat(len));
	ensures chars((void*) first, int_of_nat(len)*sizeof(struct lpm_trie_node), ?chs);

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

/*@
	fixpoint int next_index(trie_t trie);

	fixpoint int match_length_aux(list<int> p1, list<int> p2, int acc){
		switch(p1) {
			case nil: return acc;
			case cons(h1, t1): return switch(p2) {
				case nil: return acc;
				case cons(h2, t2):
					return (h1 == h2 ? match_length_aux(t1, t2, acc + 1) : acc);
			};
		}
	}

	fixpoint int match_length(node_t node, list<int> p){
		switch(node) {
			case empty: return 0;
			case node(lc, m, np, v, rc):
				return match_length_aux(np, p, 0);
		}
	}
	
	fixpoint list<int> make_im_prefix_aux(list<int> p, nat ml){
		switch(ml) {
			case zero: return nil;
			case succ(n): return switch(p) {
				case nil: return nil;
				case cons(h, t): return cons(h, make_im_prefix_aux(t, n));
			};
		}
	}
	
	fixpoint list<int> make_im_prefix(list<int> p1, list<int> p2){
		return make_im_prefix_aux(p1, nat_of_int(match_length_aux(p1, p2, 0)));
	}

	fixpoint option<int> trie_lookup_nodes(node_t par, node_t cur, list<int> p){
		switch(cur) {
			case empty: return
				switch(par) {
					case empty: return none;
					case node(p_lc, pm, pp, pv, p_rc): return pv;
				};
			case node(c_lc, cm, cp, cv, c_rc): return
				(match_length(cur, p) < length(cp) ?
					switch(par) {
						case empty: return none;
						case node(p_lc, pm, pp, pv, p_rc): return pv;
					} :
					(length(cp) == length(p) ? cv :
						(nth(length(cp), p) == 0 ?
							trie_lookup_nodes(cur, c_lc, p) :
							trie_lookup_nodes(cur, c_rc, p))
					)
				);
		}
	}

	fixpoint bool node_search(node_t root, node_t node, fixpoint (node_t, node_t, bool) fp) {
		switch(root) {
			case empty: return false;
			case node(r_lc, rm, rp, rv, r_rc): return
				(fp(root, node) ? true :
					switch(node) {
						case empty: return false;
						case node(n_lc, nm, np, nv, n_rc): return
							(match_length(root, np) < length(rp) ? false :
								(nth(length(rp), np) == 0 ?
									node_search(r_lc, node, fp) :
									node_search(r_rc, node, fp)
								)
							);
					}
				);
		}
	}

	fixpoint bool same_prefix(node_t n1, node_t n2){
		switch(n1) {
			case empty: return false;
			case node(n1_lc, n1_m, n1_p, n1_v, n1_rc): return
				switch(n2) {
					case empty: return false;
					case node(n2_lc, n2_m, n2_p, n2_v, n2_rc):
						return n1_p == n2_p;
				};
		}
	}

	fixpoint bool contains_prefix(trie_t trie, list<int> p){
		switch(trie) {
			case trie(root, n, m): return
				node_search(root, node(empty, 0, p, none, empty), same_prefix);
		}
	}

	fixpoint int lpm_trie_update_size(trie_t trie, list<int> p){
		switch(trie){
			case trie(root, n, m): return
			(contains_prefix(trie, p) ? n : n+1);
		}
	}

	fixpoint node_t lpm_trie_update_nodes(trie_t trie, node_t root, node_t new){
		switch(root) {
			case empty: return new;
			case node(r_lc, rm, rp, rv, r_rc): return
				switch(new) {
					case empty: return root;
					case node(n_lc, nm, np, nv, n_rc): return
						(match_length(root, np) == length(rp) ?
							(length(rp) == length(np) ?
							 	node(r_lc, rm, rp, nv, r_rc) :
								(nth(length(rp), np) == 0 ?
									node(lpm_trie_update_nodes(trie, r_lc, new), rm, rp, rv, r_rc) :
									node(r_lc, rm, rp, rv, lpm_trie_update_nodes(trie, r_rc, new))
								)
							) :
							(length(rp) == length(np) ?
								(nth(length(np)-1, np) == 0 ?
									node(new, next_index(trie), make_im_prefix(np, rp), none, root) :
									node(root, next_index(trie), make_im_prefix(np, rp), none, new)
								) :
								(nth(length(np), rp) == 0 ?
									node(root, nm, np, nv, n_rc) :
									node(n_lc, nm, np, nv, root)
								)
							)
						);
				};
		}
	}

	fixpoint trie_t lpm_trie_update(trie_t trie, list<int> p, option<int> v){
		switch(trie){
			case trie(root, n, m): return
				trie(lpm_trie_update_nodes(trie, root, node(empty, next_index(trie), p, v, empty)),
				     lpm_trie_update_size(trie, p), m);
		}
	}
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
