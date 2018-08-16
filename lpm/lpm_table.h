struct lpm_table;
struct lpm_key;

//@ #include <list.gh>
//@ #include <listex.gh>

/*@
    inductive lpmKey = lpmKey(list<int>, size_t);
    inductive lpmTable = lpmTable(list<pair<lpmKey, int>>, size_t);

    predicate lpmTable_p(lpmTable tbl, struct lpm_table *lpm_table);
    predicate lpmKey_p(lpmKey key, struct lpm_key *lpm_key);

    fixpoint size_t lpmTable_max(lpmTable tbl){
        switch(tbl) { case lpmTable(entries, max):
            return max;
        }
    }

    fixpoint list<pair<lpmKey, int>> lpmTable_entries(lpmTable tbl){
        switch(tbl) { case lpmTable(entries, max):
            return entries;
        }
    }

    fixpoint lpmTable lpmTable_empty_fp(size_t max){
        return lpmTable(nil, max);
    }

    fixpoint int lpmTable_n_entries(lpmTable tbl){
        switch(tbl){
            case lpmTable(entries, max):
                return length(entries);
        }
    }

    fixpoint bool lpmTable_contains_key(lpmTable tbl, lpmKey key){
        switch(tbl){
            case lpmTable(entries, max):
                return exists(entries, (lpm_entry_contains_key)(key));
        }
    }

    fixpoint bool lpm_entry_contains_key(lpmKey key, pair<lpmKey, int> entry){
        switch(entry) { case pair(k, val):
            return k == key;
        }
    }

    fixpoint bool lpmTable_contains_value(lpmTable tbl, int value){
        switch(tbl) { case lpmTable(entries, max):
            return exists(entries, (lpm_entry_contains_value)(value));
        }
    }

    fixpoint bool lpm_entry_contains_value(int val, pair<lpmKey, int> entry){
        switch(entry) { case pair(k, v):
            return v == val;
        }
    }

    fixpoint bool lpmTable_contains_pair(lpmTable tbl, pair<lpmKey, int> entry){
        switch(tbl) { case lpmTable(entries, max):
            return contains(entries, entry);
        }
    }


    fixpoint lpmTable lpmTable_remove_key(lpmTable tbl, lpmKey key){
        swicth(tbl) { case lpmTable(entries, max):
            return lpmTable(lpm_entries_remove_key(entries), max);
        }
    }

    fixpoint list<pair<lpmKey, int>> lpm_entries_remove_key(
                                    list<pair<lpmKey, in>> entries, lpmKey key)
    {
        switch(entries) {
            case nil:
                return entries;
            case cons(h, t):
                switch(h) { case pair(k, v):
                    if(k == key){
                        return lpm_entries_remove_key(t, key);
                    } else {
                        return cons(h, lpm_entries_remove_key(t, key));
                    }
                }
        }
    }

    fixpoint lpmTable lpmTable_remove_pair(lpmTable tbl, pair<lpmKey, int> pair){
        switch(tbl) { case lpmTable(entries, max):
            return lpmTable(remove(pair, entries), max);
        }
    }

    fixpoint int match_length(lpmKey k1, lpmKey k2){
        switch(k1) { case lpmKey(p1, l1):
            switch(k2) { case lpmKey(p2, l2):
                return l2 - length(remove_all(p1, p2));
            }
        }
    }

    fixpoint lpmKey lpmTable_get_key_for_value(lpmTable tbl, int val){
        switch(tbl) { case lpmTable(entries, max):
            return lpm_entries_get_key_for_value(entries, val);
        }
    }

    fixpoint lpmKey lpm_entries_get_key_for_value(
                                    list<pair<lpmKey, int>> entries, int val)
    {
        switch(entries) {
            case nil: return lpmKey(nil, 0);
            case cons(h, t):
                switch(h) { case pair(key, v):
                    if(v == val){
                        return key;
                    } else {
                        return lpm_entries_get_key_for_value(t, val);
                    }
                }
        }
    }

    fixpoint bool lpmKey_lower_matchlength(int matchlen, lpmKey key,
                                            pair<lpmKey, int> entry)
    {
        switch(entry) { case pair(k, val):
            return matchlength(key, k) <= matchlen;
        }
    }
}
@*/

int lpm_table_allocate(struct lpm_table **table_out, size_t max_entries);
/*@ requires max_entries > 0 &*&
             *table_out |-> ?old_val; @*/
/*@ ensures result == 0 ?
                *table_out |-> ?tbl &*&
                lpmTable_p(lpmTable_empty_fp(max_entries), tbl) :
                *table_out |-> old_val; @*/

int lpm_table_update_elem(struct lpm_table *table, struct lpm_key *key, int value);
/*@ requires lpmTable_p(?old_tbl, table) &*&
              lpmTable_n_entries(old_tbl) < lpmTable_max(old_tbl); @*/
/*@ ensures lpmTable_p(?new_tbl, table) &*&
            lpmKey_p(?k, key) &*&
            lpmTable_contains_pair(new_tbl, pair(k, value)) &*&
            lpmTable_remove_pair(new_tbl, pair(k, value)) ==
                lpmTable_remove_key(old_tbl, k) &*&
            lpmTable_n_entries(new_tbl) = lpmTable_contains_key(old_tbl, k) ?
                lpmTable_n_entries(old_tbl):
                lpmTable_n_entries(old_tbl) + 1;
            @*/

int lpm_table_delete_elem(struct lpm_table *table, struct lpm_key *key);
/*@ requires lpmTable_p(?old_tbl, table) &*&
             lpmKey_p(?k, key) &*&
             lpmTable_contains_key(old_tbl, k); @*/
/*@ ensures lpmTable_p(?new_tbl, table) &*&
            new_tbl == lpmTable_remove_key(old_tbl, k) &*&
            lpmTable_n_entries(new_tbl) == lpmTable_n_entries(old_tbl) - 1; @*/

int lpm_table_lookup(struct lpm_table *table, struct lpm_key *key);
/*@ requires lpmTable_p(?tbl, table) &*&
             lpmTable_n_entries(tbl) > 0; @*/
/*@ ensures lpmKey_p(?k, key) &*&
            lpmTable_contains_value(tbl, result) &*&
            forall(lpmTable_entries(tbl),
                    (lpmKey_lower_matchlength)
                    (matchlength(k, lpmTable_get_key_for_value(tbl, result)))
                    (k)
                );@*/
