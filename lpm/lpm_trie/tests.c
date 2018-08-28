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
    for(int i = 0; i < LPM_DATA_SIZE; i++){
        printf("%d", node->data[i]);
        if(i < LPM_DATA_SIZE - 1)
            printf(".");
    }
    printf("/%d\n", node->prefixlen);
}

//Print representation of a node
void print_node(struct lpm_trie_node *node, struct lpm_trie *trie)
{
    printf("=============================\n");

    uint8_t *value = node->data + LPM_DATA_SIZE;
    printf("value: %d\n", node->value);

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

    struct lpm_trie *trie = lpm_trie_alloc(max_entries);

    //Create keys for insertion
    uint8_t data_1[4] = {192, 168, 0, 0};
    struct lpm_trie_key *key_1 = lpm_trie_key_alloc(16, data_1);
    uint8_t data_2[4] = {192, 168, 0, 0};
    struct lpm_trie_key *key_2 = lpm_trie_key_alloc(24, data_2);
    uint8_t data_3[4] = {192, 168, 128, 0};
    struct lpm_trie_key *key_3 = lpm_trie_key_alloc(24, data_3);
    uint8_t data_4[4] = {192, 168, 1, 0};
    struct lpm_trie_key *key_4 = lpm_trie_key_alloc(24, data_4);

    uint64_t flags = 0;

    //Insert nodes
    printf("##### Inserting first node #####\n");
    uint8_t value_1 = 1;
    int res = trie_update_elem(trie, key_1, value_1);
    if(res)
        goto out;

    struct lpm_trie_node *node_1 = trie->root;
    res = memcmp(node_1->data, key_1->data, LPM_DATA_SIZE);
    if(res)
        goto out;

    print_node(trie->root, trie);

    printf("##### Inserting second node ######\n");
    uint8_t value_2 = 2;
    res = trie_update_elem(trie, key_2, value_2);
    if(res)
        goto out;

    struct lpm_trie_node *node_2 = trie->root->child[0];
    res = memcmp(node_2->data, key_2->data, LPM_DATA_SIZE);
    if(res)
        goto out;

    print_node(trie->root, trie);
    print_node(trie->root->child[0], trie);

    printf("##### Inserting third node #####\n");
    uint8_t value_3 = 3;
    res = trie_update_elem(trie, key_3, value_3);
    if(res)
        goto out;

    struct lpm_trie_node *node_3 = trie->root->child[1];
    res = memcmp(node_3->data, key_3->data, LPM_DATA_SIZE);
    if(res)
        goto out;

    print_node(trie->root, trie);
    print_node(trie->root->child[0], trie);
    print_node(trie->root->child[1], trie);

    printf("##### Inserting fourth node #####\n");
    uint8_t value_4 = 4;
    res = trie_update_elem(trie, key_4, value_4);
    if(res)
        goto out;

    struct lpm_trie_node *node_4 = trie->root->child[0]->child[1];
    res = memcmp(node_4->data, key_4->data, LPM_DATA_SIZE);
    if(res)
        goto out;

    print_node(trie->root, trie);
    print_node(trie->root->child[0], trie);
    print_node(trie->root->child[0]->child[0], trie);
    print_node(trie->root->child[0]->child[1], trie);
    print_node(trie->root->child[1], trie);

out:
    free(key_4);
    free(key_3);
    free(key_2);
    free(key_1);
    trie_free(trie);

    return res;
}

int test_delete_elem()
{
    size_t max_entries = 256;

    struct lpm_trie *trie = lpm_trie_alloc(max_entries);

    //Insert nodes manually, the insertion function is not tested here.
    uint8_t value_1 = 1;
    uint8_t value_2 = 2;
    uint8_t value_3 = 3;
    uint8_t value_4 = 4;
    uint8_t value_im = 0;

    struct lpm_trie_node *node_1 = lpm_trie_node_alloc(trie, value_1);
    struct lpm_trie_node *node_2 = lpm_trie_node_alloc(trie, value_2);
    struct lpm_trie_node *node_3 = lpm_trie_node_alloc(trie, value_3);
    struct lpm_trie_node *node_4 = lpm_trie_node_alloc(trie, value_4);
    struct lpm_trie_node *node_im = lpm_trie_node_alloc(trie, value_im);

    uint8_t data_1[4] = {192, 168, 0, 0};
    uint8_t data_2[4] = {192, 168, 0, 0};
    uint8_t data_3[4] = {192, 168, 128, 0};
    uint8_t data_4[4] = {192, 168, 1, 0};
    uint8_t data_im[4] = {192, 168, 0, 0};

    node_1->prefixlen = 16;
    node_2->prefixlen = 24;
    node_3->prefixlen = 24;
    node_4->prefixlen = 24;
    node_im->prefixlen = 23;

    memcpy(node_1->data, data_1, LPM_DATA_SIZE);
    memcpy(node_2->data, data_2, LPM_DATA_SIZE);
    memcpy(node_3->data, data_3, LPM_DATA_SIZE);
    memcpy(node_4->data, data_4, LPM_DATA_SIZE);
    memcpy(node_im->data, data_im, LPM_DATA_SIZE);

    node_im->flags = LPM_TREE_NODE_FLAG_IM;

    trie->root = node_1;
    node_1->child[0] = node_im;
    node_1->child[1] = node_3;
    node_im->child[0] = node_2;
    node_im->child[1] = node_4;

    struct lpm_trie_key *key_4 = lpm_trie_key_alloc(24, data_4);
    struct lpm_trie_key *key_3 = lpm_trie_key_alloc(24, data_3);
    struct lpm_trie_key *key_2 = lpm_trie_key_alloc(24, data_2);

    printf("#####Deleting first node#####\n");
    int res = trie_delete_elem(trie, key_4);
    if(res)
        goto out;

    res = memcmp(trie->root->child[0]->data, data_2, LPM_DATA_SIZE);
    if(res)
        goto out;

    print_node(trie->root, trie);
    print_node(trie->root->child[0], trie);
    print_node(trie->root->child[1], trie);

    printf("#####Deleting second node#####\n");
    res = trie_delete_elem(trie, key_3);
    if(res)
        goto out;

    print_node(trie->root, trie);
    print_node(trie->root->child[0], trie);

    printf("#####Deleting third node#####\n");
    res = trie_delete_elem(trie, key_2);
    if(res)
        goto out;

    print_node(trie->root, trie);

out:
    free(key_2);
    free(key_3);
    free(key_4);
    trie_free(trie);
    return res;
}

void test_lookup_elem()
{
    size_t max_entries = 256;

    struct lpm_trie *trie = lpm_trie_alloc(max_entries);

    //Insert nodes manually, the insertion function is not tested here.
    uint8_t value_1 = 1;
    uint8_t value_2 = 2;
    uint8_t value_3 = 3;
    uint8_t value_4 = 4;
    uint8_t value_im = 0;

    struct lpm_trie_node *node_1 = lpm_trie_node_alloc(trie, value_1);
    struct lpm_trie_node *node_2 = lpm_trie_node_alloc(trie, value_2);
    struct lpm_trie_node *node_3 = lpm_trie_node_alloc(trie, value_3);
    struct lpm_trie_node *node_4 = lpm_trie_node_alloc(trie, value_4);
    struct lpm_trie_node *node_im = lpm_trie_node_alloc(trie, value_im);

    uint8_t data_1[4] = {192, 168, 0, 0};
    uint8_t data_2[4] = {192, 168, 0, 0};
    uint8_t data_3[4] = {192, 168, 128, 0};
    uint8_t data_4[4] = {192, 168, 1, 0};
    uint8_t data_im[4] = {192, 168, 0, 0};

    node_1->prefixlen = 16;
    node_2->prefixlen = 24;
    node_3->prefixlen = 24;
    node_4->prefixlen = 24;
    node_im->prefixlen = 23;

    memcpy(node_1->data, data_1, LPM_DATA_SIZE);
    memcpy(node_2->data, data_2, LPM_DATA_SIZE);
    memcpy(node_3->data, data_3, LPM_DATA_SIZE);
    memcpy(node_4->data, data_4, LPM_DATA_SIZE);
    memcpy(node_im->data, data_im, LPM_DATA_SIZE);

    node_im->flags = LPM_TREE_NODE_FLAG_IM;

    trie->root = node_1;
    node_1->child[0] = node_im;
    node_1->child[1] = node_3;
    node_im->child[0] = node_2;
    node_im->child[1] = node_4;

    uint8_t key_data_1[4] = {192, 168, 0, 1};
    uint8_t key_data_2[4] = {192, 168, 1, 1};
    uint8_t key_data_3[4] = {192, 168, 128, 1};
    uint8_t key_data_4[4] = {192, 168, 128, 0};

    struct lpm_trie_key *key_1 = lpm_trie_key_alloc(32, key_data_1);
    struct lpm_trie_key *key_2 = lpm_trie_key_alloc(32, key_data_2);
    struct lpm_trie_key *key_3 = lpm_trie_key_alloc(32, key_data_3);
    struct lpm_trie_key *key_4 = lpm_trie_key_alloc(32, key_data_4);

    int res_1 = trie_lookup_elem(trie, key_1);
    printf("First result: %d\n", res_1);//2

    int res_2 = trie_lookup_elem(trie, key_2);
    printf("Second result: %d\n", res_2);//4

    int res_3 = trie_lookup_elem(trie, key_3);
    printf("Third result: %d\n", res_3);//3

    int res_4 = trie_lookup_elem(trie, key_4);
    printf("Fourths result: %d\n", res_4);//3

    free(key_4);
    free(key_3);
    free(key_2);
    free(key_1);
    trie_free(trie);
}

void main()
{
    printf("########## Beginning of test_update_elem ##########\n");
    int test_res = test_update_elem();
    if(test_res)
        printf("Something went wrong: %d\n", test_res);
    printf("########## End of test_update_elem ##########\n\n");

    printf("########## Beginning of test_delete_elem ###########\n");
    test_res = test_delete_elem();
    if(test_res)
        printf("Something went wrong: %d\n", test_res);
    printf("########## End of test_delete_elem ##########\n\n");

    printf("########## Beginning of test_lookup_elem ###########\n");
    test_lookup_elem();
    printf("########## End of test_lookup_elem ##########\n");
}
