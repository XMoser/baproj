#include "lpm_trie.h"
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <stddef.h>

struct lpm_trie_node *lpm_trie_node_alloc(const struct lpm_trie *trie,
						 const void *value)
{
	struct lpm_trie_node *node;
	size_t size = sizeof(struct lpm_trie_node) + trie->data_size;

	if (value)
		size += trie->value_size;

    node = malloc(size);
	if (!node)
		return NULL;

	node->flags = 0;

	if (value)
		memcpy(node->data + trie->data_size, value,
		       trie->value_size);

	node->child[0] = NULL;
	node->child[1] = NULL;		   

	return node;
}

struct lpm_trie *lpm_trie_alloc(size_t max_entries, size_t max_prefixlen,
                                    size_t data_size, size_t value_size)
{
    if(max_entries == 0 || data_size == 0 || value_size == 0)
        return NULL;

    struct lpm_trie *trie = malloc(sizeof(struct lpm_trie));

	trie->root = NULL;
    trie->n_entries = 0;
    trie->max_entries = max_entries;
    trie->max_prefixlen = max_prefixlen;
    trie->data_size = data_size;
    trie->value_size = value_size;

    return trie;
}


void trie_free(struct lpm_trie *trie)
{
	struct lpm_trie_node **slot;
	struct lpm_trie_node *node;

	/* Always start at the root and walk down to a node that has no
	 * children. Then free that node, nullify its reference in the parent
	 * and start over.
	 */

	for (;;) {
		slot = &trie->root;

		for (;;) {
			node = *slot;
			if (!node)
				goto out;

			if (node->child[0]) {
				slot = &node->child[0];
				continue;
			}

			if (node->child[1]) {
				slot = &node->child[1];
				continue;
			}

            free(node);
            *slot = NULL;
			break;
		}
	}

out:
    free(trie);
}

int extract_bit(const uint8_t *data, size_t index)
{
	return !!(data[index / 8] & (1 << (7 - (index % 8))));
}

size_t longest_prefix_match(const struct lpm_trie *trie,
				   const struct lpm_trie_node *node,
                   const struct lpm_trie_key *key)
{
	size_t prefixlen = 0;
	size_t i;

	for (i = 0; i < trie->data_size; i++) {
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

void *trie_lookup_elem(struct lpm_trie *trie, void *_key)
{
	struct lpm_trie_node *node, *found = NULL;
	struct lpm_trie_key *key = _key;

	/* Start walking the trie from the root node ... */

	for (node = trie->root; node;) {
		unsigned int next_bit;
		size_t matchlen;

		/* Determine the longest prefix of @node that matches @key.
		 * If it's the maximum possible prefix for this trie, we have
		 * an exact match and can return it directly.
		 */
		matchlen = longest_prefix_match(trie, node, key);
		if (matchlen == trie->max_prefixlen) {
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
		node = node->child[next_bit];
	}

	if (!found)
		return NULL;

	return found->data + trie->data_size;
}

/* Called from syscall or from eBPF program */
int trie_update_elem(struct lpm_trie *trie, void *_key, void *value,
                            uint64_t flags)
{
	struct lpm_trie_node *node, *im_node = NULL, *new_node = NULL;
	struct lpm_trie_node **slot;
	struct lpm_trie_key *key = _key;
	unsigned long irq_flags;
	unsigned int next_bit;
	size_t matchlen = 0;
	int ret = 0;

	if (key->prefixlen > trie->max_prefixlen)
		return -EINVAL;

	/* Allocate and fill a new node */
	if (trie->n_entries == trie->max_entries) {
		ret = -ENOSPC;
		goto out;
	}

	new_node = lpm_trie_node_alloc(trie, value);
	if (!new_node) {
		ret = -ENOMEM;
		goto out;
	}

	trie->n_entries++;

	new_node->prefixlen = key->prefixlen;
    new_node->child[0] = NULL;
    new_node->child[1] = NULL;
	memcpy(new_node->data, key->data, trie->data_size);

	/* Now find a slot to attach the new node. To do that, walk the tree
	 * from the root and match as many bits as possible for each node until
	 * we either find an empty slot or a slot that needs to be replaced by
	 * an intermediate node.
	 */
	slot = &trie->root;

	while ((node = *slot)) {
		matchlen = longest_prefix_match(trie, node, key);

		if (node->prefixlen != matchlen ||
		    node->prefixlen == key->prefixlen ||
		    node->prefixlen == trie->max_prefixlen)
			break;

		next_bit = extract_bit(key->data, node->prefixlen);
		slot = &node->child[next_bit];
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
		new_node->child[0] = node->child[0];
		new_node->child[1] = node->child[1];

		if (!(node->flags & LPM_TREE_NODE_FLAG_IM))
			trie->n_entries--;

        *slot = new_node;
        free(node);

		goto out;
	}

	/* If the new node matches the prefix completely, it must be inserted
	 * as an ancestor. Simply insert it between @node and *@slot.
	 */
	if (matchlen == key->prefixlen) {
		next_bit = extract_bit(node->data, matchlen);
        new_node->child[next_bit] = node;
        *slot = new_node;
		goto out;
	}

	im_node = lpm_trie_node_alloc(trie, NULL);
	if (!im_node) {
		ret = -ENOMEM;
		goto out;
	}

	im_node->prefixlen = matchlen;
	im_node->flags |= LPM_TREE_NODE_FLAG_IM;
	memcpy(im_node->data, node->data, trie->data_size);

	/* Now determine which child to install in which slot */
	if (extract_bit(key->data, matchlen)) {
        im_node->child[0] = node;
        im_node->child[1] = new_node;
	} else {
        im_node->child[0] = new_node;
        im_node->child[1] = node;
	}

	/* Finally, assign the intermediate node to the determined spot */
    *slot = im_node;

out:
	if (ret) {
		if (new_node)
			trie->n_entries--;

		free(new_node);
		free(im_node);
	}

	return ret;
}

int trie_delete_elem(struct lpm_trie *trie, void *_key)
{
	struct lpm_trie_key *key = _key;
	struct lpm_trie_node **trim, **trim2;
	struct lpm_trie_node *node, *parent;
	unsigned long irq_flags;
	unsigned int next_bit;
	size_t matchlen = 0;
	int ret = 0;

	if (key->prefixlen > trie->max_prefixlen)
		return -EINVAL;

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
		matchlen = longest_prefix_match(trie, node, key);

		if (node->prefixlen != matchlen ||
		    node->prefixlen == key->prefixlen)
			break;

		parent = node;
		trim2 = trim;
		next_bit = extract_bit(key->data, node->prefixlen);
		trim = &node->child[next_bit];
	}

	if (!node || node->prefixlen != key->prefixlen ||
	    (node->flags & LPM_TREE_NODE_FLAG_IM)) {
		ret = -ENOENT;
		goto out;
	}

	trie->n_entries--;

	/* If the node we are removing has two children, simply mark it
	 * as intermediate and we are done.
	 */
	if (node->child[0] && node->child[1]) {
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
	    !node->child[0] && !node->child[1]) {
		if (node == parent->child[0])
            *trim2 = parent->child[1];
		else
            *trim2 = parent->child[0];
        free(parent);
        free(node);
		goto out;
	}

	/* The node we are removing has either zero or one child. If there
	 * is a child, move it into the removed node's slot then delete
	 * the node.  Otherwise just clear the slot and delete the node.
	 */
	if (node->child[0])
        *trim = node->child[0];
	else if (node->child[1])
        *trim = node->child[1];
	else
        *trim = NULL;
    free(node);

out:
	return ret;
}

int trie_get_next_key(struct lpm_trie *trie, void *_key, void *_next_key)
{
	struct lpm_trie_node *node, *next_node = NULL, *parent, *search_root;
	struct lpm_trie_key *key = _key, *next_key = _next_key;
	struct lpm_trie_node **node_stack = NULL;
	int err = 0, stack_ptr = -1;
	unsigned int next_bit;
	size_t matchlen;

	/* The get_next_key follows postorder. For the 4 node example in
	 * the top of this file, the trie_get_next_key() returns the following
	 * one after another:
	 *   192.168.0.0/24
	 *   192.168.1.0/24
	 *   192.168.128.0/24
	 *   192.168.0.0/16
	 *
	 * The idea is to return more specific keys before less specific ones.
	 */

	/* Empty trie */
	search_root = trie->root;
	if (!search_root)
		return -ENOENT;

	/* For invalid key, find the leftmost node in the trie */
	if (!key || key->prefixlen > trie->max_prefixlen)
		goto find_leftmost;

    node_stack = calloc(trie->max_prefixlen, sizeof(struct lpm_trie_node *));
	if (!node_stack)
		return -ENOMEM;

	/* Try to find the exact node for the given key */
	for (node = search_root; node;) {
		node_stack[++stack_ptr] = node;
		matchlen = longest_prefix_match(trie, node, key);
		if (node->prefixlen != matchlen ||
		    node->prefixlen == key->prefixlen)
			break;

		next_bit = extract_bit(key->data, node->prefixlen);
		node = node->child[next_bit];
	}
	if (!node || node->prefixlen != key->prefixlen ||
	    (node->flags & LPM_TREE_NODE_FLAG_IM))
		goto find_leftmost;

	/* The node with the exactly-matching key has been found,
	 * find the first node in postorder after the matched node.
	 */
	node = node_stack[stack_ptr];
	while (stack_ptr > 0) {
		parent = node_stack[stack_ptr - 1];
		if (parent->child[0] == node) {
			search_root = parent->child[1];
			if (search_root)
				goto find_leftmost;
		}
		if (!(parent->flags & LPM_TREE_NODE_FLAG_IM)) {
			next_node = parent;
			goto do_copy;
		}

		node = parent;
		stack_ptr--;
	}

	/* did not find anything */
	err = -ENOENT;
	goto free_stack;

find_leftmost:
	/* Find the leftmost non-intermediate node, all intermediate nodes
	 * have exact two children, so this function will never return NULL.
	 */
	for (node = search_root; node;) {
		if (!(node->flags & LPM_TREE_NODE_FLAG_IM))
			next_node = node;
		node = node->child[0];
	}
do_copy:
	next_key->prefixlen = next_node->prefixlen;
	memcpy((void *)next_key + offsetof(struct lpm_trie_key, data),
	       next_node->data, trie->data_size);
free_stack:
    free(node_stack);
	return err;
}
