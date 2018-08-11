#include "lpm_trie.h"
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <stddef.h>

struct lpm_trie_key *lpm_trie_key_alloc(size_t prefixlen, uint8_t *data)
{
    struct lpm_trie_key *key = malloc(sizeof(struct lpm_trie_key) + sizeof(data));
    key->prefixlen = prefixlen;
    memcpy(key->data, data, sizeof(data));

    return key;
}

//Print data stored in a node in as data[0].data[1]. ... /prefixlen
void print_node_data(struct lpm_trie_node *node, struct lpm_trie *trie)
{
    for(int i = 0; i < trie->data_size; i++){
        printf("%d", node->data[i]);
        if(i < trie->data_size - 1)
            printf(".");
    }
    printf("/%d\n", node->prefixlen);
}

//Print representation of a node
void print_node(struct lpm_trie_node *node, struct lpm_trie *trie)
{
    printf("=============================\n");

    uint8_t *value = node->data + trie->data_size;
    printf("value: ");
    for(int i = 0; i < trie->value_size; i++){
        printf("%d", value[i]);
    }
    printf("\n");

    print_node_data(node, trie);

    printf("child0: ");
    if(!node->child[0])
        printf("---\n");
    else
        print_node_data(node->child[0], trie);

    printf("child1: ");
    if(!node->child[1])
        printf("---\n");
    else
        print_node_data(node->child[1], trie);

    printf("=============================\n");
}

int test_update_elem()
{
    size_t max_entries = 256;
    size_t max_prefixlen = 32;
    size_t data_size = 4;
    size_t value_size = 1;

    struct lpm_trie *trie = lpm_trie_alloc(max_entries, max_prefixlen,
                                            data_size, value_size);

    //Create keys for insertion
    //First key:
    uint8_t data_1[4] = {192, 168, 0, 0};
    struct lpm_trie_key *key_1 = lpm_trie_key_alloc(16, data_1);

    //Second key:
    uint8_t data_2[4] = {192, 168, 0, 0};
    struct lpm_trie_key *key_2 = lpm_trie_key_alloc(24, data_2);

    //Third key
    uint8_t data_3[4] = {192, 168, 128, 0};
    struct lpm_trie_key *key_3 = lpm_trie_key_alloc(24, data_3);

    //Fourth key:
    uint8_t data_4[4] = {192, 168, 1, 0};
    struct lpm_trie_key *key_4 = lpm_trie_key_alloc(24, data_4);

    uint64_t flags = 0;

    //Insert nodes
    uint8_t value_1 = 1;
    int res = trie_update_elem(trie, key_1, &value_1, flags);
    if(res)
        goto out;

    uint8_t value_2 = 2;
    res = trie_update_elem(trie, key_2, &value_2, flags);
    if(res)
        goto out;

    uint8_t value_3 = 3;
    res = trie_update_elem(trie, key_3, &value_3, flags);
    if(res)
        goto out;

    uint8_t value_4 = 4;
    res = trie_update_elem(trie, key_4, &value_4, flags);
    if(res)
        goto out;

    //Comparing values stored in nodes with keys
    struct lpm_trie_node *node_1 = trie->root;
    res = memcmp(node_1->data, key_1->data, data_size);
    if(res)
        goto out;
    print_node(trie->root, trie);

    struct lpm_trie_node *node_2 = trie->root->child[0]->child[0];
    res = memcmp(node_2->data, key_2->data, data_size);
    if(res)
        goto out;
    print_node(trie->root->child[0], trie);
    print_node(trie->root->child[0]->child[0], trie);

    struct lpm_trie_node *node_4 = trie->root->child[0]->child[1];
    res = memcmp(node_4->data, key_4->data, data_size);
    if(res)
    goto out;
    print_node(trie->root->child[0]->child[1], trie);

    struct lpm_trie_node *node_3 = trie->root->child[1];
    res = memcmp(node_3->data, key_3->data, data_size);
    if(res)
        goto out;
    print_node(trie->root->child[1], trie);

out:
    free(key_2);
    free(key_1);
    trie_free(trie);

    return res;
}

void main()
{
    int test_res = test_update_elem();
    if(test_res)
        printf("Something went wrong: %d\n", test_res);
    printf("End of test\n");
}
