#include "lpm_trie_mem.h"
#include "../../dchain/double-chain.h"
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stddef.h>

//@ #include "arith.gh"
//@ #include <nat.gh>

struct lpm_trie *lpm_trie_alloc(size_t max_entries)
/*@ requires max_entries > 0; @*/
/*@ ensures result == NULL ? true : trie_p(result); @*/
{
	if(max_entries == 0 ||
	   max_entries > SIZE_MAX / sizeof(struct lpm_trie_node))
        return NULL;

	struct lpm_trie *trie = malloc(sizeof(struct lpm_trie));
	if(!trie)
		return trie;

	//Allocate memory for the maximum number of nodes
	int max_int = (int) max_entries;
	struct lpm_trie_node *node_mem_blocks = malloc(sizeof(struct lpm_trie_node) * max_int);

	if(!node_mem_blocks){
		free(trie);
		return NULL;
	}

	//Allocate the double-chain allocator
	int res = dchain_allocate(max_entries, &trie->dchain);
	if(!res){
		free(node_mem_blocks);
		free(trie);
		return NULL;
	}

	trie->root = NULL;
	trie->n_entries = 0;
	trie->max_entries = max_entries;
	trie->node_mem_blocks = node_mem_blocks;

	//@ bytes_to_nodes(trie->node_mem_blocks, nat_of_int(max_entries));
	//@ close trie_p(trie);

	return trie;
}

struct lpm_trie_node *lpm_trie_node_alloc(struct lpm_trie *trie, int *value)
/*@ requires trie_p(trie); @*/
/*@ ensures trie_p(trie) &*& node_p(result); @*/
{
	int index;
	int res = dchain_allocate_new_index(trie->dchain, &index, 1);
	if(!res){
		return NULL;
	}

	//Allocate next index to the new node
	//struct lpm_trie_node *node = (struct lpm_trie_node *) ptr_stack[ptr_index];
	struct lpm_trie_node *node = &(trie->node_mem_blocks[index]);
	//@ extract_node(trie->node_mem_blocks, ptr_index);
	//@ assert node == trie->node_mem_blocks + ptr_index * sizeof(struct lpm_trie_node);
	//@ open node_p(node);

	node->flags = 0;
	node->value = value;
	node->l_child = NULL;
	node->r_child = NULL;
	node->mem_index = index;

	//@ close node_p(node);
	//@ close nodes_p(trie->node_mem_blocks, trie->max_entries);
	//@ close trie_p(trie);
	return node;
}

void node_free(struct lpm_trie_node *node, struct lpm_trie *trie)
/*@ requires true; @*/
/*@ ensures true; @*/
{
	int index;
	int res = dchain_rejuvenate_index(trie->dchain, node->mem_index, 0);
	res = dchain_expire_one_index(trie->dchain, &index, 1);

}

void trie_free(struct lpm_trie *trie)
/*@ requires trie_p(trie); @*/
/*@ ensures true; @*/
{
	free(trie->node_mem_blocks);
	free(trie->dchain);
    free(trie);
}

int extract_bit(const uint8_t *data, size_t index)
/*@ requires true; @*/
/*@ ensures true; @*/
{
	return !!(data[index / 8] & (1 << (7 - (index % 8))));
}

size_t longest_prefix_match(const struct lpm_trie_node *node,
                            const struct lpm_trie_key *key)
/*@ requires malloc_block_lpm_trie_key(key); @*/
/*@ ensures malloc_block_lpm_trie_key(key); @*/
{
	size_t prefixlen = 0;
	size_t i;

	for (i = 0; i < LPM_DATA_SIZE; i++) {
		size_t b;

		b = 8 - fls(node->data[i] ^ key->data[i]);
		prefixlen += b;

		if (prefixlen >= node->prefixlen || prefixlen >= key->prefixlen)
			return min(node->prefixlen, key->prefixlen);

		if (b < 8)
			break;
	}

	return prefixlen;
}

int *trie_lookup_elem(struct lpm_trie *trie, struct lpm_trie_key *key)
/*@ requires trie_p(trie) &*&
             malloc_block_lpm_trie_key(key); @*/
/*@ ensures trie_p(trie) &*&
            malloc_block_lpm_trie_key(key); @*/
{
	struct lpm_trie_node *node;
	struct lpm_trie_node *found = NULL;
	if(!key)
		return NULL;

	/* Start walking the trie from the root node ... */

	for (node = trie->root; node;) {
		unsigned int next_bit;
		size_t matchlen;

		/* Determine the longest prefix of @node that matches @key.
		 * If it's the maximum possible prefix for this trie, we have
		 * an exact match and can return it directly.
		 */
		matchlen = longest_prefix_match(node, key);
		if (matchlen == LPM_PLEN_MAX) {
			found = node;
			break;
		}

		/* If the number of bits that match is smaller than the prefix
		 * length of @node, bail out and return the node we have seen
		 * last in the traversal (ie, the parent).
		 */
		if (matchlen < node->prefixlen)
			break;

		/* Consider this node as return candidate unless it is an
		 * artificially added intermediate one.
		 */
		if (!(node->flags & LPM_TREE_NODE_FLAG_IM))
			found = node;

		/* If the node match is fully satisfied, let's see if we can
		 * become more specific. Determine the next bit in the key and
		 * traverse down.
		 */
		next_bit = extract_bit(key->data, node->prefixlen);
		if(next_bit == 0){
			node = node->l_child;
		} else {
			node = node->r_child;
		}
		//node = node->child[next_bit];
	}

	if (!found)
		return NULL;

	return found->value;
}

int trie_update_elem(struct lpm_trie *trie, struct lpm_trie_key *key, int *value)
/*@ requires trie_p(trie) &*&
             malloc_block_lpm_trie_key(key); @*/
/*@ ensures trie_p(trie) &*&
            malloc_block_lpm_trie_key(key); @*/
{
	struct lpm_trie_node *node;
	struct lpm_trie_node *im_node = NULL;
	struct lpm_trie_node *new_node = NULL;
	struct lpm_trie_node **slot;
	unsigned int next_bit;
	size_t matchlen = 0;
	int ret = 0;

	if (!trie || !trie->node_mem_blocks || !trie->dchain ||
		!key || key->prefixlen > LPM_PLEN_MAX)
		return -1;

	/* Allocate and fill a new node */
	if (trie->n_entries == trie->max_entries) {
		ret = -1;
		goto out;
	}

	new_node = lpm_trie_node_alloc(trie, value);
	if (!new_node) {
		ret = -1;
		goto out;
	}

	trie->n_entries++;

	new_node->prefixlen = key->prefixlen;
    new_node->l_child = NULL;
    new_node->r_child = NULL;
	memcpy(new_node->data, key->data, LPM_DATA_SIZE);

	/* Now find a slot to attach the new node. To do that, walk the tree
	 * from the root and match as many bits as possible for each node until
	 * we either find an empty slot or a slot that needs to be replaced by
	 * an intermediate node.
	 */
	slot = &trie->root;

	while ((node = *slot)) {
		matchlen = longest_prefix_match(node, key);

		if (node->prefixlen != matchlen ||
		    node->prefixlen == key->prefixlen ||
		    node->prefixlen == LPM_PLEN_MAX)
			break;

		next_bit = extract_bit(key->data, node->prefixlen);
		if(next_bit == 0){
			slot = &node->l_child;
		} else {
			slot = &node->r_child;
		}
		//slot = &node->child[next_bit];
	}

	/* If the slot is empty (a free child pointer or an empty root),
	 * simply assign the @new_node to that slot and be done.
	 */
	if (!node) {
        *slot = new_node;
		goto out;
	}

	/* If the slot we picked already exists, replace it with @new_node
	 * which already has the correct data array set.
	 */
	if (node->prefixlen == matchlen) {
		new_node->l_child = node->l_child;
		new_node->r_child = node->r_child;

		if (!(node->flags & LPM_TREE_NODE_FLAG_IM))
			trie->n_entries--;

        *slot = new_node;
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
			new_node->l_child = node;
		} else {
			new_node->r_child = node;
		}
        *slot = new_node;
		goto out;
	}

	im_node = lpm_trie_node_alloc(trie, NULL);
	if (!im_node) {
		ret = -1;
		goto out;
	}

	im_node->prefixlen = matchlen;
	im_node->flags |= LPM_TREE_NODE_FLAG_IM;
	memcpy(im_node->data, node->data, LPM_DATA_SIZE);

	/* Now determine which child to install in which slot */
	if (extract_bit(key->data, matchlen)) {
        im_node->l_child = node;
        im_node->r_child = new_node;
	} else {
        im_node->l_child = new_node;
        im_node->r_child = node;
	}

	/* Finally, assign the intermediate node to the determined spot */
    *slot = im_node;

out:
	if (ret) {
		if (new_node)
			trie->n_entries--;

		node_free(new_node, trie);
		node_free(im_node, trie);
	}

	return ret;
}

int trie_delete_elem(struct lpm_trie *trie, struct lpm_trie_key *key)
/*@ requires trie_p(trie) &*&
             malloc_block_lpm_trie_key(key); @*/
/*@ ensures trie_p(trie) &*&
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
