-- Copyright © 2019 François G. Dorais. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.

import .exceptional

def list.range' : nat → opt_param nat 0 → list ℕ
| 0 _ := []
| (len+1) fst := fst :: list.range' len (fst+1)

-- name.append in core is unfortunately marked meta
def name.append' : name → name → name
| a (name.anonymous) := a
| a (name.mk_string s b) := name.mk_string s (name.append' a b)
| a (name.mk_numeral n b) := name.mk_numeral n (name.append' a b)

instance name.has_append' : has_append name := ⟨name.append'⟩

def name.add_sub_str : name → string → name
| (name.mk_string str pfx) sub := name.mk_string (str ++ "_" ++ sub) pfx
| pfx sub := name.mk_string ("_" ++ sub) pfx

def name.add_subscript {α : Sort*} [has_to_string α] : name → α → name :=
λ n x, name.add_sub_str n $ to_string x

def name.add_sub_num : name → nat → name := name.add_subscript

def name.get_suffix : name → name := λ n, n.update_prefix name.anonymous

def name.update_suffix : name → name → name := λ n s, n.get_prefix ++ s

def mk_num_names (root : name) (len : nat) (fst : nat := 0) : list name :=
list.map (mk_num_name root) (list.range' len fst)

def mk_sub_name : name → nat → name
| (name.mk_string s n) i := name.mk_string (s ++ "_" ++ to_string i) n
| n i := name.mk_string ("_" ++ to_string i) n

def mk_sub_names (root : name) (len : nat) (fst : nat := 0) : list name :=
list.map (mk_sub_name root) (list.range' len fst)
