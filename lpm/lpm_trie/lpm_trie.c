#include "lpm_trie_mem.h"
#include "../../../vignat/nf/lib/containers/double-chain.h"
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stddef.h>

//@ #include "arith.gh"
//@ #include <nat.gh>

void init_nodes_mem(const void *node_mem_blocks, size_t max_entries)
/*@ requires max_entries > 0 &*& nodes_im_p(node_mem_blocks, max_entries);@*/
/*@ ensures nodes_p(node_mem_blocks, max_entries, max_entries); @*/
{
	struct lpm_trie_node *cur;
	for(int i = 0; i < (int) max_entries; i++)
	/*@ invariant (i < max_entries ? i >= 0 : i == max_entries) &*&
	              (i == 0 ? true :
	               nodes_p(node_mem_blocks + (max_entries-i)*sizeof(struct lpm_trie_node), i, max_entries)) &*&
	              nodes_im_p(node_mem_blocks, max_entries - i);@*/
	{
		/*@ if(i == 0) {
		    	close nodes_p(node_mem_blocks + max_entries * sizeof(struct lpm_trie_node), ((i+1)-1),
		    	              max_entries);
		    }@*/
		cur = (struct lpm_trie_node*) node_mem_blocks + (int) max_entries-1-i;
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
/*@ requires max_entries > 0 &*& max_entries <= IRANG_LIMIT; @*/
/*@ ensures result == NULL ? true : trie_p(result, 0, max_entries); @*/
{
	if(max_entries == 0 ||
	   max_entries > SIZE_MAX / sizeof(struct lpm_trie_node))
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

	//TODO: Initialize pre-allocated nodes, produce assertions for bytes_to_nodes
	//@ bytes_to_nodes_im(node_mem_blocks, nat_of_int(max_entries));
	//@ assert nodes_im_p(node_mem_blocks, max_entries);
	init_nodes_mem(node_mem_blocks, max_entries);

	//@ close trie_p(trie, 0, max_entries);

	return trie;
}

int lpm_trie_node_alloc(struct lpm_trie *trie, int *value)
/*@ requires trie_p(trie, ?n, ?max_i) &*& valid_dchain(trie); @*/
/*@ ensures trie_p(trie, n, max_i) &*& valid_dchain(trie) &*&
            (result == INVALID_NODE_ID ? true : result >= 0 &*& result < max_i); @*/
{
	//@ open trie_p(trie, n, max_i);
	//@ open valid_dchain(trie);
	int index;
	int res = dchain_allocate_new_index(trie->dchain, &index, 1);
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
	//@ close valid_dchain(trie);
	//@ close trie_p(trie, n, max_i);
	return index;
}

void node_free(struct lpm_trie_node *node, struct lpm_trie *trie)
/*@ requires trie_p(trie, ?n, ?max_i) &*&
             node_p(node, max_i) &*&
             valid_mem_index(trie, node); @*/
/*@ ensures trie_p(trie, n, max_i); @*/
{
	int index;

	//@ open trie_p(trie, n, max_i);
	//@ open node_p(node, max_i);
	//@ open valid_mem_index(trie, node);
	int res = dchain_rejuvenate_index(trie->dchain, node->mem_index, 0);
	res = dchain_expire_one_index(trie->dchain, &index, 1);
	//@ close trie_p(trie, n, max_i);

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
	              uchars(key->data, i, _); @*/
	{
		size_t b;

		//@ open uchars((void*) node->data + i, LPM_DATA_SIZE - i, _);
		//@ open uchars((void*) key->data + i, LPM_DATA_SIZE - i, _);
		uint32_t nxk_i = (uint32_t) node->data[i] ^ key->data[i];
		int last_set = fls(nxk_i);
		b = 8 - (uint32_t) last_set;
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

int *trie_lookup_elem(struct lpm_trie *trie, struct lpm_trie_key *key)
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
	//if(!key)
		//return NULL;

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
			//node = node->l_child;
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
		return NULL;
	}

	//@ close_nodes(node_base, node_id, max_i);
	struct lpm_trie_node *found = node_base + found_id;
	//@ extract_node(node_base, found_id);
	//@ open node_p(found, max_i);
	int *res = found->value;
	//@ close node_p(found, max_i);
	//@ close_nodes(node_base, found_id, max_i);
	//@ close trie_p(trie, n, max_i);
	return res;
}

int trie_update_elem(struct lpm_trie *trie, struct lpm_trie_key *key, int *value)
/*@ requires trie_p(trie, _, ?max_i) &*& valid_dchain(trie) &*&
             key_p(key) &*& integer(value, _); @*/
/*@ ensures trie_p(trie, _, max_i) &*& valid_dchain(trie) &*&
            key_p(key) &*& integer(value, _); @*/
{
	struct lpm_trie_node *node;
	struct lpm_trie_node *im_node = NULL;
	struct lpm_trie_node *new_node = NULL;
	struct lpm_trie_node **slot;
	struct lpm_trie_node *root;
	struct lpm_trie_node *parent;
	unsigned int next_bit;
	size_t matchlen = 0;
	int ret = 0;

	int new_node_id = 0;
	int node_id = 0;
	int old_id = 0;
	int insert_left = 0;
	int insert_right = 0;

	//@ open key_p(key);
	if (/*!trie || !trie->node_mem_blocks || !trie->dchain ||
		!key || */key->prefixlen > LPM_PLEN_MAX){
		//@ close key_p(key);
		return -1;
	}

	//@ open trie_p(trie, _, max_i);
	/* Allocate and fill a new node */
	if (trie->n_entries == trie->max_entries) {
		ret = -1;
		//@ close key_p(key);
		//@ close trie_p(trie, _, max_i);
		goto out;
	}

	//@ close trie_p(trie, _, max_i);
	new_node_id = lpm_trie_node_alloc(trie, value);
	if (new_node_id == INVALID_NODE_ID) {
		ret = -1;
		//@ close key_p(key);
		goto out;
	}

	//@ open trie_p(trie, _, max_i);
	struct lpm_trie_node *node_base = trie->node_mem_blocks;
	new_node = node_base + new_node_id;
	//@ extract_node(node_base, new_node_id);

	if(trie->n_entries == 0) {
		//@ open node_p(new_node, max_i);
		trie->root = new_node->mem_index;
		//@ close node_p(new_node, max_i);
		//@ close_nodes(node_base, new_node_id, max_i);
		//@ close trie_p(trie, _, max_i);
		//@ close key_p(key);
		goto out;
	}
	trie->n_entries++;

	//@ open node_p(new_node, max_i);
	new_node->prefixlen = key->prefixlen;
	//new_node->l_child = NULL;
	//new_node->r_child = NULL;
	memcpy(new_node->data, key->data, LPM_DATA_SIZE);
	//@ close node_p(new_node, max_i);
	//@ close_nodes(node_base, new_node_id, max_i);

	/* Now find a slot to attach the new node. To do that, walk the tree
	 * from the root and match as many bits as possible for each node until
	 * we either find an empty slot or a slot that needs to be replaced by
	 * an intermediate node.
	 */
	//slot = &trie->root;
	root = node_base + trie->root;
	slot = &root;
	node_id = trie->root;

	//@ extract_node(node_base, node_id);

	for (node_id = trie->root; node_id >= 0 && node_id < max_i;)
	/*@ invariant nodes_p(node_base, node_id, max_i) &*&
	              node_p(node_base + node_id, max_i) &*&
	              nodes_p(node_base + node_id+1, max_i - node_id-1, max_i); @*/
	{
		old_id = node_id;
		matchlen = longest_prefix_match(node, key);

		//@ open node_p(node, max_i);
		if (node->prefixlen != matchlen ||
		    node->prefixlen == key->prefixlen ||
		    node->prefixlen == LPM_PLEN_MAX)
		    	//@ close node_p(node, max);
			break;

		next_bit = extract_bit(key->data, node->prefixlen);
		insert_left = 0;
		insert_right = 0;
		//slot = &node->child[next_bit];
		if(next_bit == 0){
			insert_left = 1;
			if(!node->has_l_child){
				node_id = INVALID_NODE_ID;
				//@ close node_p(node, max_i);
				break;
			}
			//slot = &(trie->node_mem_blocks + node->l_child);
			node_id = node->l_child;
			//@ close_nodes(node_base, old_id, max_i);
			//@ extract_node(node_base, node_id, max_i);

		} else {
			insert_right = 1;
			if(!node->has_r_child){
				node_id = INVALID_NODE_ID;
				no_right_child = 1;
				//@ close node_p(node, max_i);
				break;
			}
			//slot = &(trie->node_mem_blocks + node->r_child);
			node_id = node->r_child;
			//@ close_nodes(node_base, old_id, max_i);
			//@ extract_node(node_base, node_id);
		}
	}

	/*@ assert (node_id == INVALID_NODE_ID ?
	            nodes_p(node_base, old_id, max_i) &*&
		        node_p(node_base + old_id, max_i) &*&
		        nodes_p(node_base + old_id+1, max_i - old_id-1, max_i)
	            :
	            nodes_p(node_base + node_id, max_i) &*&
	            node_p(node_base + node_id, max_i) &*&
		        nodes_p(node_base + node_id+1, max_i - node_id-1, max_i)
	            );
	@*/

	/* If the slot is empty (a free child pointer or an empty root),
	 * simply assign the @new_node to that slot and be done.
	 */
	if (/*!node*/node_id == INVALID_NODE_ID) {
		//*slot = new_node;
		parent = node_base + old_id;
		if(no_left_child) {
			parent->l_child = new_node_id;
			parent->has_l_child = 1;
		} else if(no_right_child) {
			parent->r_child = new_node_id;
			parent->has_r_child = 1;
		}
		goto out;
	}

	/* If the slot we picked already exists, replace it with @new_node
	 * which already has the correct data array set.
	 */
	if (node->prefixlen == matchlen) {
		new_node->l_child = node->l_child;
		new_node->r_child = node->r_child;
		new_node->has_l_child = node->has_l_child;
		new_node->has_r_child = node->has_r_child;

		if (!(node->flags & LPM_TREE_NODE_FLAG_IM))
			trie->n_entries--;

		//*slot = new_node;
		parent = node_base + old_id;
		if(insert_left) {
			parent->l_child = new_node_id;
			parent->has_l_child = 1;
		} else if(insert_right) {
			parent->r_child = new_node_id;
			parent->has_r_child = 1;
		}

		node_free(node, trie);

		goto out;
	}

	/* If the new node matches the prefix completely, it must be inserted
	 * as an ancestor. Simply insert it between @node and *@slot.
	 */
	if (matchlen == key->prefixlen) {
		next_bit = extract_bit(node->data, matchlen);
        //new_node->child[next_bit] = node;
		if(next_bit == 0){
			new_node->l_child = node->mem_index;
			node->has_l_child = 1;
		} else {
			new_node->r_child = node->mem_index;
			node->has_r_child = 1;
		}
        //*slot = new_node;
		parent = node_base + old_id;
		if(insert_left) {
			parent->l_child = new_node_id;
			parent->has_l_child = 1;
		} else if(insert_right) {
			parent->r_child = new_node_id;
			parent->has_r_child = 1;
		}

		goto out;
	}

	im_node_id = lpm_trie_node_alloc(trie, NULL);
	if (im_node_id == INVALID_NODE_ID) {
		ret = -1;
		goto out;
	}

	im_node = node_base + im_node_id;
	im_node->prefixlen = matchlen;
	im_node->flags |= LPM_TREE_NODE_FLAG_IM;
	memcpy(im_node->data, node->data, LPM_DATA_SIZE);

	/* Now determine which child to install in which slot */
	if (extract_bit(key->data, matchlen)) {
        im_node->l_child = node->mem_index;
        im_node->r_child = new_node->mem_index;
	} else {
        im_node->l_child = new_node->mem_index;
        im_node->r_child = node->mem_index;
	}
	im_node->has_l_child = 1;
	im_node->has_r_child = 1;

	/* Finally, assign the intermediate node to the determined spot */
    //*slot = im_node;
	parent = node_base + old_id;
	if(insert_left) {
		parent->l_child = im_node_id;
		parent->has_l_child = 1;
	} else if(insert_right) {
		parent->r_child = im_node_id;
		parent->has_r_child = 1;
	}

out:
	if (ret) {
		if (new_node_id != INVALID_NODE_ID) {
			trie->n_entries--;
			node_free(new_node, trie);
		}
		//node_free(new_node, trie);

		if (im_node != INVALID_NODE_ID) {
			node_free(im_node, trie);
		}
		//node_free(im_node, trie);
	}

	return ret;
}

int trie_delete_elem(struct lpm_trie *trie, struct lpm_trie_key *key)
/*@ requires trie_p(trie, ?n, ?max_i) &*& n > 0 &*&
             malloc_block_lpm_trie_key(key); @*/
/*@ ensures trie_p(trie, ?n2, max_i) &*&
            malloc_block_lpm_trie_key(key); @*/
{
	struct lpm_trie_node **trim;
	struct lpm_trie_node **trim2;
	struct lpm_trie_node *node;
	struct lpm_trie_node *parent;
	unsigned int next_bit;
	size_t matchlen = 0;
	int ret = 0;

	if (!trie || !trie->node_mem_blocks || !trie->dchain ||
		!key || key->prefixlen > LPM_PLEN_MAX)
		return -1;

	/* Walk the tree looking for an exact key/length match and keeping
	 * track of the path we traverse.  We will need to know the node
	 * we wish to delete, and the slot that points to the node we want
	 * to delete.  We may also need to know the nodes parent and the
	 * slot that contains it.
	 */
	trim = &trie->root;
	trim2 = trim;
	parent = NULL;
	while ((node = *trim)) {
		matchlen = longest_prefix_match(node, key);

		if (node->prefixlen != matchlen ||
		    node->prefixlen == key->prefixlen)
			break;

		parent = node;
		trim2 = trim;
		next_bit = extract_bit(key->data, node->prefixlen);
		//trim = &node->child[next_bit];
		if(next_bit == 0){
			trim = &node->l_child;
		} else {
			trim = &node->r_child;
		}
	}

	if (!node || node->prefixlen != key->prefixlen ||
	    (node->flags & LPM_TREE_NODE_FLAG_IM)) {
		ret = -1;
		goto out;
	}

	trie->n_entries--;

	/* If the node we are removing has two children, simply mark it
	 * as intermediate and we are done.
	 */
	if (node->l_child && node->r_child) {
		node->flags |= LPM_TREE_NODE_FLAG_IM;
		goto out;
	}

	/* If the parent of the node we are about to delete is an intermediate
	 * node, and the deleted node doesn't have any children, we can delete
	 * the intermediate parent as well and promote its other child
	 * up the tree.  Doing this maintains the invariant that all
	 * intermediate nodes have exactly 2 children and that there are no
	 * unnecessary intermediate nodes in the tree.
	 */
	if (parent && (parent->flags & LPM_TREE_NODE_FLAG_IM) &&
	    !node->l_child && !node->r_child) {
		if (node == parent->l_child)
            *trim2 = parent->r_child;
		else
            *trim2 = parent->l_child;
        node_free(parent, trie);
        node_free(node, trie);
		goto out;
	}

	/* The node we are removing has either zero or one child. If there
	 * is a child, move it into the removed node's slot then delete
	 * the node.  Otherwise just clear the slot and delete the node.
	 */
	if (node->l_child)
        *trim = node->l_child;
	else if (node->r_child)
        *trim = node->r_child;
	else
        *trim = NULL;
    node_free(node, trie);

out:
	return ret;
}
