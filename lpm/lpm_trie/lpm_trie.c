#include "lpm_trie_mem.h"
#include "lib/double-chain.h"
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stddef.h>
#include <stdbool.h>

//@ #include "arith.gh"
//@ #include <nat.gh>

void init_nodes_mem(const void *node_mem_blocks, size_t max_entries)
/*@ requires max_entries > 0 &*& nodes_im_p(node_mem_blocks, max_entries) &*&
             max_entries <= IRANG_LIMIT &*&
             (void*)0 < ((void*)(node_mem_blocks)) &*&
             (void*)((struct lpm_trie_node*)node_mem_blocks + max_entries) <= (char*)UINTPTR_MAX;@*/
/*@ ensures nodes_p(node_mem_blocks, max_entries, max_entries); @*/
{
	struct lpm_trie_node *cur;
	for(size_t i = 0; i < max_entries; i++)
	/*@ invariant (i < max_entries ? i >= 0 : i == max_entries) &*&
	              max_entries <= IRANG_LIMIT &*&
	              (void*)0 < ((void*)(node_mem_blocks)) &*&
	              (void*)((struct lpm_trie_node*)node_mem_blocks + max_entries) <= (char*)UINTPTR_MAX &*&
	              (i == 0 ? true :
	               nodes_p(node_mem_blocks + (max_entries-i)*sizeof(struct lpm_trie_node), i, max_entries)) &*&
	              nodes_im_p(node_mem_blocks, max_entries - i);@*/
	{
		/*@ if(i == 0) {
		    	close nodes_p(node_mem_blocks + max_entries * sizeof(struct lpm_trie_node), ((i+1)-1),
		    	              max_entries);
		    }@*/
		int index = (int)(max_entries - 1 - i);
		//@ mul_mono_strict(index, IRANG_LIMIT, sizeof(struct lpm_trie_node));
		cur = (struct lpm_trie_node*) node_mem_blocks + index;
		//@ extract_im_node(node_mem_blocks, max_entries-1-i);
		/*@ open nodes_im_p(node_mem_blocks + ((max_entries-1-i)+1) * sizeof(struct lpm_trie_node),
		                    (max_entries-i) - (max_entries-1-i) - 1);@*/
		//@ open node_im_p(node_mem_blocks + (max_entries-1-i)*sizeof(struct lpm_trie_node));
		cur->l_child = 0;
		cur->r_child = 0;
		cur->mem_index = 0;
		cur->has_l_child = 0;
		cur->has_r_child = 0;
		//@ close node_p(node_mem_blocks + (max_entries-1-i)*sizeof(struct lpm_trie_node), max_entries);
		//@ close nodes_p(node_mem_blocks + (max_entries-1-i)*sizeof(struct lpm_trie_node), i+1, max_entries);
	}
	//@ open nodes_im_p(node_mem_blocks, max_entries-max_entries);
}

struct lpm_trie *lpm_trie_alloc(size_t max_entries)
/*@ requires max_entries > 0 &*& max_entries <= IRANG_LIMIT &*&
             sizeof(struct lpm_trie_node) < MAX_NODE_SIZE; @*/
/*@ ensures result == NULL ? true : trie_p(result, 0, max_entries); @*/
{
	if(max_entries == 0 ||
	   max_entries > TRIE_SIZE_MAX / sizeof(struct lpm_trie_node))
        return NULL;

	struct lpm_trie *trie = malloc(sizeof(struct lpm_trie));
	if(!trie)
		return trie;

	//Allocate memory for the maximum number of nodes
	int max_int = (int) max_entries;
	void *node_mem_blocks = malloc(sizeof(struct lpm_trie_node) * max_int);

	if(!node_mem_blocks){
		free(trie);
		return NULL;
	}

	//Allocate the double-chain allocator
	int res = dchain_allocate(max_int, &trie->dchain);
	if(!res){
		free(node_mem_blocks);
		free(trie);
		return NULL;
	}

	//trie->root = NULL;
	trie->n_entries = 0;
	trie->max_entries = max_entries;
	trie->node_mem_blocks = node_mem_blocks;
	//@ assert trie->max_entries |-> ?max;
	//@ assert trie->dchain |-> ?dchain;
	//@ assert double_chainp(?ch, dchain);
	//@ assert dchain_index_range_fp(ch) == max;
	//@ assert dchain_high_fp(ch) == 0;

	//@ bytes_to_nodes_im(node_mem_blocks, nat_of_int(max_entries));
	//@ assert nodes_im_p(node_mem_blocks, max_entries);
	init_nodes_mem(node_mem_blocks, max_entries);

	//@ close trie_p(trie, 0, max_entries);

	return trie;
}

int lpm_trie_node_alloc(struct lpm_trie *trie, int value)
/*@ requires trie_p(trie, ?n, ?max_i); @*/
/*@ ensures trie_p(trie, n, max_i) &*&
            (result == INVALID_NODE_ID ? true : result >= 0 &*& result < max_i); @*/
{
	//@ open trie_p(trie, n, max_i);
	int index;
	//@ assert trie->dchain |-> ?dchain;
	//@ assert double_chainp(?ch, dchain);
	int res = dchain_allocate_new_index(trie->dchain, &index, 1);
	//@ allocate_preserves_index_range(ch, index, 1);
	//@ allocate_keeps_high_bounded(ch, index, 1);
	if(!res){
		//@ close trie_p(trie, n, max_i);
		return INVALID_NODE_ID;
	}

	//Allocate next index to the new node
	struct lpm_trie_node *node = trie->node_mem_blocks + index;
	//@ extract_node(trie->node_mem_blocks, index);
	//@ open node_p(node, max_i);

	node->flags = 0;
	node->value = value;
	//node->l_child = NULL;
	//node->r_child = NULL;
	node->mem_index = index;

	//@ close node_p(node, max_i);
	//@ close_nodes(trie->node_mem_blocks, index, trie->max_entries);
	//@ close trie_p(trie, n, max_i);
	return index;
}

int node_free(int i, struct lpm_trie *trie)
/*@ requires trie_p(trie, _, ?max_i) &*&
             i >= 0 &*& i < max_i; @*/
/*@ ensures trie_p(trie, _, max_i); @*/
{
	//@ open trie_p(trie, _, max_i);
	//@ assert trie->dchain |-> ?dchain;
	//@ assert double_chainp(?ch, dchain);
	//@ assert dchain_index_range_fp(ch) == max_i;
	//@ assert i >= 0 &*& i < dchain_index_range_fp(ch);
	//@ remove_index_keeps_high_bounded(ch, i);
	if(dchain_is_index_allocated(trie->dchain, i)) {
		int res = dchain_free_index(trie->dchain, i);
		//@ dchain_remove_keeps_ir(ch, i);
		//@ close trie_p(trie, _, max_i);
		return res;
	} else {
		//@ close trie_p(trie, _, max_i);
		return 0;
	}

}

//void trie_free(struct lpm_trie *trie)
///*@ requires trie_p(trie); @*/
///*@ ensures true; @*/
//{
//	//@ open trie_p(trie);
//	//@ nodes_to_bytes(trie->node_mem_blocks, nat_of_int(trie->max_entries));
//	free((void*) trie->node_mem_blocks);
//	free(trie->dchain);
//	free(trie);
//}

bool extract_bit(const uint8_t *data, size_t index)
/*@ requires data[0..LPM_DATA_SIZE] |-> _ &*&
             index >= 0 &*& LPM_DATA_SIZE > index / 8; @*/
/*@ ensures data[0..LPM_DATA_SIZE] |-> _;@*/
{
	//show index > 0 => index/8 > 0;
	//@ div_rem(index, 8);
	//@ uchars_split(data, index/8);
	//@ open uchars(data + index/8, LPM_DATA_SIZE - index/8, _);
	//@ shiftleft_limits(1, nat_of_int(1), nat_of_int(7 - (index % 8)));
	return !!(data[index / 8] & (1 << (7 - (index % 8))));
	//@ close uchars(data + index/8, LPM_DATA_SIZE - index/8, _);
	//@ uchars_join(data);
}

size_t longest_prefix_match(const struct lpm_trie_node *node,
                            const struct lpm_trie_key *key)
/*@ requires node_p(node, ?max_i) &*& key_p(key); @*/
/*@ ensures node_p(node, max_i) &*& key_p(key); @*/
{
	size_t prefixlen = 0;
	uint32_t last_set = 0;
	size_t i;

	//@ open node_p(node, max_i);
	//@ open key_p(key);
	//@ open uchars(node->data, LPM_DATA_SIZE, _);
	//@ open uchars(key->data, LPM_DATA_SIZE, _);
	for (i = 0; i < LPM_DATA_SIZE; i++)
	/*@ invariant node->prefixlen |-> _ &*& key->prefixlen |-> _ &*&
	              uchars((void*) node->data + i, LPM_DATA_SIZE - i, _) &*&
	              uchars(node->data, i, _) &*&
	              uchars((void*) key->data + i, LPM_DATA_SIZE - i, _) &*&
	              uchars(key->data, i, _) &*& prefixlen <= 8*i; @*/
	{
		size_t b;

		//@ open uchars((void*) node->data + i, LPM_DATA_SIZE - i, _);
		//@ open uchars((void*) key->data + i, LPM_DATA_SIZE - i, _);
		//@ u_character_limits(&node->data[i]);
		//@ u_character_limits(&key->data[i]);
		//@ bitxor_limits(node->data[i], key->data[i], nat_of_int(8));
		uint32_t nxk_i = (uint32_t) node->data[i] ^ key->data[i];
		last_set = fls(nxk_i);
		//TODO: add condition to last_set on 1 byte
		if(last_set > 8) {
			//@ close uchars((void*) node->data + i, LPM_DATA_SIZE - i, _);
			//@ close uchars((void*) key->data + i, LPM_DATA_SIZE - i, _);
			//@ uchars_join(node->data);
			//@ uchars_join(key->data);
			break;
		}
		b = 8 - last_set;
		//@ assert prefixlen + b <= prefixlen + 8;
		prefixlen += b;

		if (prefixlen >= node->prefixlen || prefixlen >= key->prefixlen){
			uint32_t node_plen = node->prefixlen;
			uint32_t key_plen = key->prefixlen;
			//@ close uchars((void*) node->data + i, LPM_DATA_SIZE - i, _);
			//@ close uchars((void*) key->data + i, LPM_DATA_SIZE - i, _);
			//@ uchars_join(node->data);
			//@ uchars_join(key->data);
			prefixlen = min(node_plen, key_plen);
			break;
		}

		if (b < 8){
			//@ close uchars((void*) node->data + i, LPM_DATA_SIZE - i, _);
			//@ close uchars((void*) key->data + i, LPM_DATA_SIZE - i, _);
			//@ uchars_join(node->data);
			//@ uchars_join(key->data);
			break;
		}

		//@ close uchars((void*) node->data + i, 1, _);
		//@ uchars_join(node->data);
		//@ close uchars((void*) key->data + i, 1, _);
		//@ uchars_join(key->data);
	}

	//@ close node_p(node, max_i);
	//@ close key_p(key);
	return prefixlen;
}

int trie_lookup_elem(struct lpm_trie *trie, struct lpm_trie_key *key)
/*@ requires trie_p(trie, ?n, ?max_i) &*& key_p(key) &*& n > 0; @*/
/*@ ensures trie_p(trie, n, max_i) &*& key_p(key); @*/
{
	//@ open trie_p(trie, n, max_i);
	struct lpm_trie_node *node_base = trie->node_mem_blocks;
	//struct lpm_trie_node *found = NULL;
	struct lpm_trie_node *node;
	int found_id = INVALID_NODE_ID;
	int node_id;
	int old_id;

	/* Start walking the trie from the root node ... */

	struct lpm_trie_node *root = trie->node_mem_blocks + trie->root;
	//@ extract_node(trie->node_mem_blocks, trie->root);
	//@ assert node_p(root, max_i);
	int max_id = (int) trie->max_entries;
	for (node_id = trie->root; node_id >= 0 && node_id < max_id;)
	/*@ invariant key_p(key) &*& node_id >= 0 &*& node_id < max_id &*&
	              (found_id == -1 ? true : found_id >= 0 &*& found_id < max_id) &*&
	              nodes_p(node_base, node_id, max_i) &*&
	              node_p(node_base + node_id, max_i) &*&
	              nodes_p(node_base + node_id+1, max_i - node_id-1, max_i); @*/
	{
		bool next_bit;
		size_t matchlen;
		node = node_base + node_id;

		/* Determine the longest prefix of @node that matches @key.
		 * If it's the maximum possible prefix for this trie, we have
		 * an exact match and can return it directly.
		 */
		matchlen = longest_prefix_match(node, key);
		if (matchlen == LPM_PLEN_MAX) {
			//@ open node_p(node, max_i);
			found_id = node->mem_index;
			//@ close node_p(node, max_i);
			break;
		}

		/* If the number of bits that match is smaller than the prefix
		 * length of @node, bail out and return the node we have seen
		 * last in the traversal (ie, the parent).
		 */
		//@ open node_p(node, max_i);
		if (matchlen < node->prefixlen) {
			//@ close node_p(node, max_i);
			break;
		}

		/* Consider this node as return candidate unless it is an
		 * artificially added intermediate one.
		 */
		if (!(node->flags & LPM_TREE_NODE_FLAG_IM))
			found_id = node->mem_index;

		/* If the node match is fully satisfied, let's see if we can
		 * become more specific. Determine the next bit in the key and
		 * traverse down.
		 */

		/* This is there only for verification,
		 * TODO: restrict the value of node->prefixlen and the result
		 * of longest_prefix_match.
		 */
		if(LPM_DATA_SIZE <= node->prefixlen / 8) {
			//@ close node_p(node, max_i);
			break;
		}

		old_id = node_id;
		//@ open key_p(key);
		next_bit = extract_bit(key->data, node->prefixlen);
		//@ close key_p(key);
		if(!next_bit){
			if(!node->has_l_child){
				//@ close node_p(node, max_i);
				break;
			}
			node_id = node->l_child;
			//@ close node_p(node, max_i);
			//@ close_nodes(node_base, old_id, max_i);
			//@ extract_node(node_base, node_id);
		} else {
			if(!node->has_r_child){
				//@ close node_p(node, max_i);
				break;
			}
			node_id = node->r_child;
			//@ close node_p(node, max_i);
			//@ close_nodes(node_base, old_id, max_i);
			//@ extract_node(node_base, node_id);
		}
	}

	if (found_id == INVALID_NODE_ID) {
		//@ close_nodes(node_base, node_id, max_i);
		//@ close trie_p(trie, n, max_i);
		return INVALID_VAL;
	}

	//@ close_nodes(node_base, node_id, max_i);
	struct lpm_trie_node *found = node_base + found_id;
	//@ extract_node(node_base, found_id);
	//@ open node_p(found, max_i);
	int res = found->value;
	//@ close node_p(found, max_i);
	//@ close_nodes(node_base, found_id, max_i);
	//@ close trie_p(trie, n, max_i);
	return res;
}

int trie_update_elem(struct lpm_trie *trie, struct lpm_trie_key *key, int value)
/*@ requires trie_p(trie, ?n1, ?max_i) &*& n1 < max_i &*&
             key_p(key); @*/
/*@ ensures trie_p(trie, _, max_i) &*&
            key_p(key); @*/
{
	struct lpm_trie_node *node;
	struct lpm_trie_node *im_node = NULL;
	struct lpm_trie_node *new_node = NULL;
	struct lpm_trie_node **slot;
	struct lpm_trie_node *root;
	struct lpm_trie_node *parent;
	bool next_bit;
	size_t matchlen = 0;
	int ret = 0;
	int res = 0;

	int new_node_id = INVALID_NODE_ID;
	int node_id = 0;
	int old_id = INVALID_NODE_ID;
	int im_node_id = INVALID_NODE_ID;
	int insert_left = 0;
	int insert_right = 0;

	//@ open key_p(key);
	if (key->prefixlen > LPM_PLEN_MAX){
		//@ close key_p(key);
		return -1;
	}

	//@ open trie_p(trie, n1, max_i);
	/* Allocate and fill a new node */
	if (trie->n_entries == trie->max_entries) {
		ret = -1;
		//@ close key_p(key);
		//@ close trie_p(trie, n1, max_i);
		goto out;
	}

	//@ close trie_p(trie, n1, max_i);
	new_node_id = lpm_trie_node_alloc(trie, value);
	if (new_node_id == INVALID_NODE_ID) {
		ret = -1;
		//@ close key_p(key);
		goto out;
	}

	//@ open trie_p(trie, n1, max_i);
	struct lpm_trie_node *node_base = trie->node_mem_blocks;
	new_node = node_base + new_node_id;
	//@ extract_node(node_base, new_node_id);
	//@ open node_p(new_node, max_i);
	new_node->prefixlen = key->prefixlen;
	memcpy(new_node->data, key->data, LPM_DATA_SIZE);
	//@ close node_p(new_node, max_i);

	trie->n_entries++;
	if(trie->n_entries == 1) {
		//@ open node_p(new_node, max_i);
		trie->root = new_node->mem_index;
		//@ close node_p(new_node, max_i);
		//@ close_nodes(node_base, new_node_id, max_i);
		//@ close trie_p(trie, 1, max_i);
		//@ close key_p(key);
		goto out;
	}

	//@ close_nodes(node_base, new_node_id, max_i);

	/* Now find a slot to attach the new node. To do that, walk the tree
	 * from the root and match as many bits as possible for each node until
	 * we either find an empty slot or a slot that needs to be replaced by
	 * an intermediate node.
	 */
	node_id = trie->root;

	//@ extract_node(node_base, node_id);
	//@ close key_p(key);

	int max_int = (int) trie->max_entries;
	//@ assert max_int == max_i;
	for (node_id = trie->root; node_id >= 0 && node_id < max_int;)
	/*@ invariant nodes_p(node_base, node_id, max_i) &*&
	              node_p(node_base + node_id, max_i) &*&
	              nodes_p(node_base + node_id+1, max_i - node_id-1, max_i)
	              &*& key_p(key) &*& node_id >= 0 &*& node_id < max_i; @*/
	{
		node = node_base + node_id;
		matchlen = longest_prefix_match(node, key);

		//@ open node_p(node, max_i);
		//@ open key_p(key);
		if (node->prefixlen != matchlen ||
		    node->prefixlen == key->prefixlen ||
		    node->prefixlen == LPM_PLEN_MAX) {
		    	//@ close node_p(node, max_i);
			break;
		}

		if(node->prefixlen >= 0 && LPM_DATA_SIZE > node->prefixlen / 8) {
			next_bit = extract_bit(key->data, node->prefixlen);
		}
		insert_left = 0;
		insert_right = 0;
		if(!next_bit){
			insert_left = 1;
			if(!node->has_l_child){
				old_id = node_id;
				node_id = INVALID_NODE_ID;
				//@ close key_p(key);
				//@ close node_p(node, max_i);
				break;
			}
			old_id = node_id;
			node_id = node->l_child;
			//@ close key_p(key);
			//@ close node_p(node, max_i);
			//@ close_nodes(node_base, old_id, max_i);
			//@ extract_node(node_base, node_id);

		} else {
			insert_right = 1;
			if(!node->has_r_child){
				old_id = node_id;
				node_id = INVALID_NODE_ID;
				//@ close key_p(key);
				//@ close node_p(node, max_i);
				break;
			}
			old_id = node_id;
			node_id = node->r_child;
			//@ close key_p(key);
			//@ close node_p(node, max_i);
			//@ close_nodes(node_base, old_id, max_i);
			//@ extract_node(node_base, node_id);
		}
	}

	/*@ assert (node_id == INVALID_NODE_ID ?
	            nodes_p(node_base, old_id, max_i) &*&
		        node_p(node_base + old_id, max_i) &*&
		        nodes_p(node_base + old_id+1, max_i - old_id-1, max_i)
	            :
	            nodes_p(node_base, node_id, max_i) &*&
	            node_p(node_base + node_id, max_i) &*&
		        nodes_p(node_base + node_id+1, max_i - node_id-1, max_i)
	            );
	@*/

	/* If the slot is empty (a free child pointer or an empty root),
	 * simply assign the @new_node to that slot and be done.
	 */
	if (/*!node*/node_id == INVALID_NODE_ID) {
		parent = node_base + old_id;
		//@ open node_p(parent, max_i);
		if(insert_left) {
			parent->l_child = new_node_id;
			parent->has_l_child = 1;
		} else if(insert_right) {
			parent->r_child = new_node_id;
			parent->has_r_child = 1;
		}
		//@ close node_p(parent, max_i);
		//@ close_nodes(node_base, old_id, max_i);
		//@ close trie_p(trie, n1+1, max_i);
		goto out;
	}

	/* If the slot we picked already exists, replace it with @new_node
	 * which already has the correct data array set.
	 */
	 node = node_base + node_id;
	//@ open node_p(node, max_i);
	if (node->prefixlen == matchlen) {
		int node_l_child = node->l_child;
		int node_r_child = node->r_child;
		int node_has_l_child = node->has_l_child;
		int node_has_r_child = node->has_r_child;
		//@ close node_p(node, max_i);
		//@ close_nodes(node_base, node_id, max_i);

		//@ extract_node(node_base, new_node_id);
		//@ open node_p(new_node, max_i);
		new_node->l_child = node_l_child;
		new_node->r_child = node_r_child;
		new_node->has_l_child = node_has_l_child;
		new_node->has_r_child = node_has_r_child;
		//@ close node_p(new_node, max_i);
		//@ close_nodes(node_base, new_node_id, max_i);

		//@ extract_node(node_base, node_id);
		//@ open node_p(node, max_i);
		if (!(node->flags & LPM_TREE_NODE_FLAG_IM)) {
			trie->n_entries--;
		}
		//@ close node_p(node, max_i);
		//@ close_nodes(node_base, node_id, max_i);

		if(old_id >= 0 && old_id < max_int) {
			//@ extract_node(node_base, old_id);
			parent = node_base + old_id;
			//@ open node_p(parent, max_i);
			if(insert_left) {
				parent->l_child = new_node_id;
				parent->has_l_child = 1;
			} else if(insert_right) {
				parent->r_child = new_node_id;
				parent->has_r_child = 1;
			}
			//@ close node_p(parent, max_i);
			//@ close_nodes(node_base, old_id, max_i);
		}

		//@ close trie_p(trie, _, max_i);
		//@ assert node_id >= 0 &*& node_id < max_i;
		res = node_free(node_id, trie);
		if(!res) {
			ret = -1;
			//@ close key_p(key);
			goto out;
		}

		//@ close key_p(key);
		goto out;
	}

	/* If the new node matches the prefix completely, it must be inserted
	 * as an ancestor. Simply insert it between @node and *@slot.
	 */
	if (matchlen == key->prefixlen && LPM_DATA_SIZE > matchlen / 8) {
		next_bit = extract_bit(node->data, matchlen);
		if(!next_bit){
			int node_mem_index = node->mem_index;
			node->has_l_child = 1;
			//@ close node_p(node, max_i);
			//@ close_nodes(node_base, node_id, max_i);

			//@ extract_node(node_base, new_node_id);
			//@ open node_p(new_node, max_i);
			new_node->l_child = node_mem_index;
		} else {
			int node_mem_index = node->mem_index;
			node->has_r_child = 1;
			//@ close node_p(node, max_i);
			//@ close_nodes(node_base, node_id, max_i);

			//@ extract_node(node_base, new_node_id);
			//@ open node_p(new_node, max_i);
			new_node->r_child = node_mem_index;
		}

		//@ close node_p(new_node, max_i);
		//@ close_nodes(node_base, new_node_id, max_i);

		if(old_id >= 0 && old_id < max_int) {
			parent = node_base + old_id;
			//@ extract_node(node_base, old_id);
			//@ open node_p(parent, max_i);
			if(insert_left) {
				parent->l_child = new_node_id;
				parent->has_l_child = 1;
			} else if(insert_right) {
				parent->r_child = new_node_id;
				parent->has_r_child = 1;
			}
			//@ close node_p(parent, max_i);
			//@ close_nodes(node_base, old_id, max_i);
		}
		//@ close trie_p(trie, n1+1, max_i);
		//@ close key_p(key);

		goto out;
	}

	//@ close node_p(node, max_i);
	//@ close_nodes(node_base, node_id, max_i);
	//@ close trie_p(trie, n1+1, max_i);
	im_node_id = lpm_trie_node_alloc(trie, NULL);
	if (im_node_id == INVALID_NODE_ID) {
		ret = -1;
		//@ close key_p(key);
		goto out;
	}

	//@ open trie_p(trie, n1+1, max_i);
	node_base = trie->node_mem_blocks;
	node = node_base + node_id;
	im_node = node_base + im_node_id;
	//@ extract_node(node_base, node_id);
	//@ open node_p(node, max_i);
	uint8_t *node_data = malloc(sizeof(uint8_t) * LPM_DATA_SIZE);
	if(!node_data) {
		ret = -1;
		//@ close node_p(node, max_i);
		//@ close_nodes(node_base, node_id, max_i);
		//@ close trie_p(trie, n1+1, max_i);
		//@ close key_p(key);
		goto out;
	}
	memcpy(node_data, node->data, LPM_DATA_SIZE);
	//@ close node_p(node, max_i);
	//@ close_nodes(node_base, node_id, max_i);
	//@ extract_node(node_base, im_node_id);
	//@ open node_p(im_node, max_i);
	im_node->prefixlen = matchlen;
	//@ bitor_limits(im_node->flags, LPM_TREE_NODE_FLAG_IM, nat_of_int(32));
	im_node->flags |= LPM_TREE_NODE_FLAG_IM;
	memcpy(im_node->data, node_data, LPM_DATA_SIZE);
	free(node_data);

	/* Now determine which child to install in which slot */
	//@ close node_p(im_node, max_i);
	//@ close_nodes(node_base, im_node_id, max_i);
	//@ extract_node(node_base, node_id);
	//@ open node_p(node, max_i);
	int node_mem_index = node->mem_index;

	//@ close node_p(node, max_i);
	//@ close_nodes(node_base, node_id, max_i);
	new_node = node_base + new_node_id;
	//@ extract_node(node_base, new_node_id);
	//@ open node_p(new_node, max_i);
	int new_node_mem_index = new_node->mem_index;

	//@ close node_p(new_node, max_i);
	//@ close_nodes(node_base, new_node_id, max_i);
	//@ extract_node(node_base, im_node_id);
	//@ open node_p(im_node, max_i);
	if (matchlen >= 0 && LPM_DATA_SIZE > matchlen / 8) {
		next_bit = extract_bit(key->data, matchlen);
		if(next_bit) {
			im_node->l_child = node_mem_index;
			im_node->r_child = new_node_mem_index;
		} else {
			im_node->l_child = new_node_mem_index;
			im_node->r_child = node_mem_index;
		}
	}
	//@ close key_p(key);
	im_node->has_l_child = 1;
	im_node->has_r_child = 1;
	//@ close node_p(im_node, max_i);
	//@ close_nodes(node_base, im_node_id, max_i);

	/* Finally, assign the intermediate node to the determined spot */
    	if(old_id >= 0 && old_id < max_int) {
		parent = node_base + old_id;
		//@ extract_node(node_base, old_id);
		//@ open node_p(parent, max_i);
		if(insert_left) {
			parent->l_child = im_node_id;
			parent->has_l_child = 1;
		} else if(insert_right) {
			parent->r_child = im_node_id;
			parent->has_r_child = 1;
		}
		//@ close node_p(parent, max_i);
		//@ close_nodes(node_base, old_id, max_i);
	}
	//@ close trie_p(trie, n1+1, max_i);

out:
	//@ assert trie_p(trie, _, max_i);
	//@ assert key_p(key);
	if (ret) {
		if (new_node_id != INVALID_NODE_ID) {
			//@ open trie_p(trie, _, max_i);
			if(trie->n_entries > 0) {
				trie->n_entries--;
			}
			//@ close trie_p(trie, _, max_i);
			//@ assert new_node_id >= 0 &*& new_node_id < max_i;
			res = node_free(new_node_id, trie);
		}
		//node_free(new_node, trie);

		if (im_node_id != INVALID_NODE_ID) {
			//@ assert im_node_id >= 0 &*& im_node_id < max_i;
			res = node_free(im_node_id, trie);
		}
		//node_free(im_node, trie);
	}

	return ret;
}

int trie_delete_elem(struct lpm_trie *trie, struct lpm_trie_key *key)
/*@ requires trie_p(trie, ?n, ?max_i) &*& n > 0 &*& key_p(key); @*/
/*@ ensures trie_p(trie, _, max_i) &*& key_p(key); @*/
{
	struct lpm_trie_node *node;
	struct lpm_trie_node *parent;
	struct lpm_trie_node *gparent;
	bool next_bit;
	size_t matchlen = 0;
	int ret = 0;
	int res = 0;

	int node_id = INVALID_NODE_ID;
	int parent_id = INVALID_NODE_ID;
	int gparent_id = INVALID_NODE_ID;

	int delete_left = 0;
	int delete_right = 0;

	//@ open key_p(key);
	if (key->prefixlen > LPM_PLEN_MAX) {
		//@ close key_p(key);
		return -1;
	}

	/* Walk the tree looking for an exact key/length match and keeping
	 * track of the path we traverse.  We will need to know the node
	 * we wish to delete, and the slot that points to the node we want
	 * to delete.  We may also need to know the nodes parent and the
	 * slot that contains it.
	 */

	//@ open trie_p(trie, _, max_i);
	int max_int = (int) trie->max_entries;
	//@ assert max_int == max_i;
	struct lpm_trie_node *node_base = trie->node_mem_blocks;
	int root_id = trie->root;
	//@ extract_node(node_base, root_id);

	//@ close key_p(key);
	for (node_id = trie->root; node_id >= 0 && node_id < max_int;)
	/*@ invariant key_p(key) &*& node_id >= 0 && node_id < max_i &*&
	       	      nodes_p(node_base, node_id, max_i) &*&
	              node_p(node_base + node_id, max_i) &*&
	              nodes_p(node_base + node_id+1, max_i - node_id-1, max_i); @*/
	{
		node = node_base + node_id;

		matchlen = longest_prefix_match(node, key);

		//@ open node_p(node, max_i);
		//@ open key_p(key);
		if (node->prefixlen != matchlen ||
		    node->prefixlen == key->prefixlen) {
			//@ close node_p(node, max_i);
			//@ close key_p(key);
			break;
		}

		gparent_id = parent_id;
		parent_id = node_id;

		if(node->prefixlen >= 0 && LPM_DATA_SIZE > node->prefixlen / 8) {
			next_bit = extract_bit(key->data, node->prefixlen);
		}

		delete_left = 0;
		delete_right = 0;

		if(!next_bit){
			delete_left = 1;
			if(!node->has_l_child) {
				node_id = INVALID_NODE_ID;
				//@ close node_p(node, max_i);
				//@ close key_p(key);
				break;
			} else {
				node_id = node->l_child;
				//@ close key_p(key);
				//@ close node_p(node, max_i);
				//@ close_nodes(node_base, parent_id, max_i);
				//@ extract_node(node_base, node_id);
			}
		} else {
			delete_right = 1;
			if(!node->has_r_child) {
				node_id = INVALID_NODE_ID;
				//@ close node_p(node, max_i);
				//@ close key_p(key);
				break;
			} else {
				node_id = node->r_child;
				//@ close key_p(key);
				//@ close node_p(node, max_i);
				//@ close_nodes(node_base, parent_id, max_i);
				//@ extract_node(node_base, node_id);
			}
		}
	}

	if(node_id == INVALID_NODE_ID) {
		//@ close_nodes(node_base, parent_id, max_i);
		//@ close trie_p(trie, _, max_i);
		ret = -1;
		goto out;
	}

	//@ open node_p(node, max_i);
	//@ open key_p(key);
	if (node->prefixlen != key->prefixlen ||
	    (node->flags & LPM_TREE_NODE_FLAG_IM)) {
		ret = -1;
		//@ close node_p(node, max_i);
		//@ close_nodes(node_base, node_id, max_i);
		//@ close trie_p(trie, _, max_i);
		//@ close key_p(key);
		goto out;
	}

	trie->n_entries--;

	/* If the node we are removing has two children, simply mark it
	 * as intermediate and we are done.
	 */
	if (node->has_l_child && node->has_r_child) {
		//@ bitor_limits(node->flags, LPM_TREE_NODE_FLAG_IM, nat_of_int(32));
		node->flags |= LPM_TREE_NODE_FLAG_IM;
		//@ close node_p(node, max_i);
		//@ close_nodes(node_base, node_id, max_i);
		//@ close trie_p(trie, _, max_i);
		//@ close key_p(key);
		goto out;
	}

	/* If the parent of the node we are about to delete is an intermediate
	 * node, and the deleted node doesn't have any children, we can delete
	 * the intermediate parent as well and promote its other child
	 * up the tree.  Doing this maintains the invariant that all
	 * intermediate nodes have exactly 2 children and that there are no
	 * unnecessary intermediate nodes in the tree.
	 */
	if(parent_id != INVALID_NODE_ID && parent_id >= 0 && parent_id < max_int) {
		parent = node_base + parent_id;
		int node_has_l_child = node->has_l_child;
		int node_has_r_child = node->has_r_child;
		//@ close node_p(node, max_i);
		//@ close_nodes(node_base, node_id, max_i);
		//@ extract_node(node_base, parent_id);
		//@ open node_p(parent, max_i);
		if ((parent->flags & LPM_TREE_NODE_FLAG_IM) &&
		    !node_has_l_child && !node_has_r_child) {
		    	//@ close node_p(parent, max_i);
		    	//@ close_nodes(node_base, parent_id, max_i);
			if(gparent_id != INVALID_NODE_ID &&
			   gparent_id >= 0 && gparent_id < max_int) {
				gparent = node_base + gparent_id;
				//@ extract_node(node_base, parent_id);
				//@ open node_p(parent, max_i);
				int parent_l_child = parent->l_child;
				int parent_r_child = parent->r_child;
				//@ close node_p(parent, max_i);
				//@ close_nodes(node_base, parent_id, max_i);
				//@ extract_node(node_base, gparent_id);
				//@ open node_p(gparent, max_i);
				if(parent_id == gparent->l_child) {
					if (delete_left) {
						gparent->l_child = parent_r_child;
					} else if(delete_right) {
						gparent->l_child = parent_l_child;
					}
				} else if(parent_id == gparent->r_child) {
					if(delete_left) {
						gparent->r_child = parent_r_child;
					} else if(delete_right) {
						gparent->r_child = parent_r_child;
					}
				}
				//@ close node_p(gparent, max_i);
				//@ close_nodes(node_base, gparent_id, max_i);
			}
			//@ close trie_p(trie, _, max_i);
			//@ assert parent_id >= 0 &*& parent_id < max_i;
			res = node_free(parent_id, trie);
			if(!res) {
				ret = -1;
				//@ close key_p(key);
				goto out;
			}
			//@ assert node_id >= 0 &*& node_id < max_i;
			res = node_free(node_id, trie);
			if(!res) {
				ret = -1;
				//@ close key_p(key);
				goto out;
			}
			//@ close key_p(key);
			goto out;
		}

	/* The node we are removing has either zero or one child. If there
	 * is a child, move it into the removed node's slot then delete
	 * the node.  Otherwise just clear the slot and delete the node.
	 */
	 	//@ close node_p(parent, max_i);
		//@ close_nodes(node_base, parent_id, max_i);
		//@ extract_node(node_base, node_id);
		//@ open node_p(node, max_i);
		int node_l_child = node->l_child;
		int node_r_child = node->r_child;
		//@ close node_p(node, max_i);
		//@ close_nodes(node_base, node_id, max_i);
		//@ extract_node(node_base, parent_id);
		//@ open node_p(parent, max_i);
		if(node_has_l_child) {
			if(delete_right){
				parent->r_child = node_l_child;
			} else if(delete_left) {
				parent->l_child = node_l_child;
			}
		} else if(node_has_r_child) {
			if(delete_right) {
				parent->r_child = node_r_child;
			} else if(delete_left) {
				parent->l_child = node_r_child;
			}
		} else {
			if(delete_left) {
				parent->has_l_child = 0;
			} else if(delete_right) {
				parent->has_r_child = 0;
			}
		}
		//@ close node_p(parent, max_i);
		//@ close_nodes(node_base, parent_id, max_i);
	} else {
		//We are deleting the root
		if(node->has_l_child) {
			trie->root = node->l_child;
		} else if(node->has_r_child) {
			trie->root = node->r_child;
		}
		//@ close node_p(node, max_i);
		//@ close_nodes(node_base, node_id, max_i);
	}
	//@ close trie_p(trie, _, max_i);
	//@ close key_p(key);
	//@ assert node_id >= 0 &*& node_id < max_i;
	res = node_free(node_id, trie);
	if(!res) {
		ret = -1;
		goto out;
	}

out:
	return ret;
}
