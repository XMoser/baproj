#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stddef.h>

#define LPM_TREE_NODE_FLAG_IM	1
#define LPM_DATA_SIZE 		4
#define LPM_PLEN_MAX		32

#define min(a, b) ((a<b) ? (a) : (b))

struct lpm_trie_node;

struct lpm_trie_node {
	struct lpm_trie_node *child[2];
	uint32_t prefixlen;
	uint32_t flags;
	uint8_t data[LPM_DATA_SIZE];
	int value;
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

/*@
	inductive option<t> = some(t) | nil;
	inductive lpm_node = node(lpm_node, list<int>, option<int>, lpm_node) | nil;
	inductive lpm_trie = trie(lpm_node, int, int);

	predicate lpm_trie_p(struct lpm_trie *trie, lpm_trie t);
	predicate lpm_prefix_p(struct lpm_trie_key *key, list<int>);

	fixpoint bool is_empty(option<t> opt){
		switch(opt) {
			case some(v): return false;
			case nil: return true;
		}
	}

	fixpoint t get<t>(option<t> opt){
		switch(opt) {
			case nil:
			case some(v): return v;
		}
	}

	fixpoint int trie_size(lpm_trie t){
		switch(t){
			case trie(r, n, m): return n;
		}
	}

	fixpoint int trie_max(lpm_trie t){
		switch(t){
			case trie(r, n, m): return m;
		}
	}

	fixpoint int match_length(lpm_node node, list<int> p){
		switch(node) {
			case nil: return 0;
			case node(lc, np, v, rc):
				return match_length_aux(np, p, 0);
			case im_node(lc, np, rc):
				return match_length_aux(np, p, 0);
		}
    }

    fixpoint int match_length_aux(list<int> p1, list<int> p2, int acc){
        switch(p1) {
            case nil: return acc;
            case cons(h1, t1):
                switch(p2) {
                    case nil: return acc;
                    case cons(h2, t2):
                        if(h1 == h2){
                            return match_length_aux(t1, t2, acc+1);
                        } else {
                            return acc;
                        }
                }
        }
    }

	fixpoint bool node_search(lpm_node root, lpm_node node,
                              fixpoint (lpm_node, lpm_node, bool) fp){
		if(fp(root)(node)){
			return true;
		} else {
			switch(node) {
				case nil: return false;
				case node(n_lc, np, nv, n_rc):
					switch(root) {
						case nil: return false;
						case node(r_lc, rp, rv, r_rc):
							if(match_length(root, np) < length(rp)){
								return false;
							} else {
								if(nth(length(rp), np) == 0){
									return node_search(r_lc, node);
								} else if(nth(length(rp), np) == 1){
									return node_search(r_rc, node);
								}
							}
					}
			}
		}
	}

	fixpoint bool node_equals(lpm_node n1, lpm_node n2){
		return n1 == n2;
	}

	fixpoint bool contains(lpm_trie trie, lpm_node node){
		switch(trie) {
			case trie(root, n, m):
				return node_search(root, node, node_equals);
		}
	}

	fixpoint bool same_prefix(lpm_node n1, lpm_node n2){
		switch(n1) {
			case nil: return false;
			case node(n1_lc, n1_p, n1_v, n1_rc):
				switch(n2) {
					case nil: return false;
					case node(n2_lc, n2_p, n2_v, n2_rc):
						return n1_p == n2_p;
				}
		}
	}

	fixpoint bool contains_prefix(lpm_trie trie, list<int> p){
		switch(trie) {
			case trie(root, n, m):
				lpm_node p_node = node(nil, p, nil, nil);
				return node_search(root, p_node, same_prefix);
		}
	}

	fixpoint bool trie_condition(lpm_trie trie){
		switch(trie) {
			case trie(nil, 0, m): return true;
			case trie(r, n, m):
				return trie_cond_nodes(r);
		}
	}

	fixpoint bool trie_cond_nodes(lpm_node node){
		switch(node) {
			case nil: return true;
			case node(lc, p, v, rc):
				return valid_child(lc, p, 0) && valid_child(rc, p, 1) &&
                       trie_cond_nodes(lc) && trie_cond_nodes(rc);
		}
	}

	fixpoint bool valid_child(lpm_node child, list<int> p_pref, int diff){
		switch(child) {
			case nil: return true;
			case node(c_lc, cp, cv, c_rc):
				if(match_length(child, p_pref) < length(p_pref)){
					return false;
				}
				if(nth(length(p_pref), cp) != diff){
					return false;
				}
				return true;
		}
	}

	fixpoint lpm_trie lpm_trie_update(lpm_trie trie, list<int> p, option<int> v){
		switch(trie){
			case trie(root, n, m):
				lpm_node new_node = node(nil, p, v, nil);
				return trie(lpm_trie_update_nodes(root, new_node),
			                lpm_trie_update_size(trie, p), m);
		}
	}

	fixpoint int lpm_trie_update_size(lpm_trie trie, lis<int> p){
		switch(trie){
			case trie(root, n, m):
			if(contains_prefix(trie, p)){
				return n;
			} else {
				return n+1;
			}
		}
	}

	fixpoint lpm_node lpm_trie_update_nodes(lpm_node root, lpm_node new){
		switch(root) {
			case nil: return new;
			case node(r_lc, rp, rv, r_rc):
				switch(new) {
					case nil:
					case node(n_lc, np, nv, n_rc):
						if(match_length(root, np) == length(rp)
						   && length(rp) == length(np)){
							return node(r_lc, rp, nv, l_lc);
						} else if(ml == length(rp) && length(rp) < length(np)){
							if(nth(length(rp), np) == 0){
								return node(lpm_trie_update_nodes(r_lc, new),
							                    rp, rv, r_rc);
							} else if(nth(length(rp), np) == 1){
								return node(r_lc, rp, rn,
								                lpm_trie_update_nodes(r_rc, new));
							}

						} else if(match_length(root, np) < length(rp) &&
						          length(np) < length(rp)){
							if(nth(length(np), rp) == 0){
								return node(root, np, nv, n_rc);
							} else if(nth(length(np), rp) == 1){
								return node(n_lc, np, nv, root);
							}

						} else if(match_length(root, np) < length(rp) &&
						          length(rp) == length(np)){
							if(nth(length(np)-1, np) == 0){
								return node(new, make_im_prefix(np, rp), nil, root);
							} else if(nth(length(np)-1, np) == 1){
								return node(root, make_im_prefix(np, rp), nil, new);
							}
						}

				}
		}
	}

	fixpoint list<int> make_im_prefix(list<int> p1, list<int> p2){
		int ml = match_length(p1, p2);
		return make_im_prefix_aux(p1, ml);
	}

	fixpoint list<int> make_im_prefix_aux(list<int> p, int ml){
		if(ml == 0){
			return nil;
		} else {
			switch(p) {
				case nil: return nil;
				case cons(h, t): return cons(h, make_im_prefix_aux(t, ml-1));
			}
		}
	}

	fixpoint lpm_trie lpm_trie_delete(lpm_trie trie, list<int> p){
		switch(trie) {
			case lpm_trie(root, n, m):
				return trie(lpm_trie_delete_nodes(nil, root, p), n-1, m);
		}
	}

	fixpoint lpm_node lpm_trie_delete_nodes(lpm_node g_par, lpm_node par,
                                            lpm_node cur, list<int> p){

	}

	fixpoint option<int> trie_lookup(lpm_trie trie, list<int> p){
		switch(trie) {
			case trie(root, n, m):
				return trie_lookup_nodes(root, p);
		}
	}

	fixpoint option<int> trie_lookup_nodes(lpm_node par, lpm_node cur, list<int> p){
		switch(cur) {
			case nil:
				switch(par) {
					case nil: return nil;
					case node(p_lc, pp, pv, p_rc): return pv;
				}
			case node(c_lc, cp, cv, c_rc):
				if(match_length(cur, p) < length(cp)){
					switch(par) {
						case nil: return nil;
						case node(p_lc, pp, pv, p_rc): return pv;
					}
				}

				else if(match_length(cur, p) == length(cp)){
					if(length(cp) == length(p)){
						return cv;
					} else if(length(cp) < length(p)){
						if(nth(length(cp), p) == 0){
							return trie_lookup_nodes(cur, c_lc, p);
						} else if(nth(length(cp), p) == 1){
							return trie_lookup_nodes(cur, c_rc, p);
						}
					}
				}
		}
	}

@*/

struct lpm_trie_node *lpm_trie_node_alloc(struct lpm_trie *trie, int value);
/*@ requires true; @*/
/*@ ensures true; @*/

struct lpm_trie *lpm_trie_alloc(size_t max_entries);
/*@ requires max_entries > 0; @*/
/*@ ensures lpm_trie_p(result, trie(nil, 0, max_entries)); @*/

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

int trie_lookup_elem(struct lpm_trie *trie, void *_key);
/*@ requires lpm_trie_p(trie, ?t) &*&
             lpm_prefix_p(_key, ?p) &*&
             trie_condition(t); @*/
/*@ ensures is_empty(trie_lookup(t, p)) ?
				result == -1 :
				result == get(trie_lookup(t, p)) &*&
            trie_condition(t); @*/

int trie_update_elem(struct lpm_trie *trie, void *_key, int value);
/*@ requires lpm_trie_p(trie, ?t1) &*&
             lpm_prefix_p(_key, ?p) &*& //TODO: find way to generate list<int>
             trie_size(t1) < trie_max(t1) &*&
             trie_condition(t1) == true; @*/
/*@ ensures lpm_trie_p(trie, lpm_trie_update(t1, p, v)) &*&
            trie_condition(lpm_trie_update(t1, p, v)); @*/

int trie_delete_elem(struct lpm_trie *trie, void *_key);
/*@ requires lpm_trie_p(trie, ?t1) &*&
             lpm_prefix_p(_key, ?p) &*&
             contains_prefix(t1, p) &*&
			 trie_condition(t1); @*/
/*@ ensures lpm_trie_p(trie, lpm_trie_delete(t1, p)) &*&
            trie_condition(lpm_trie_delete(t1, p)); @*/

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
