-- Copyright © 2019 François G. Dorais. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.

reserve prefix `¬`:40 -- core := not
reserve prefix `~`:40 -- core
reserve prefix `-`:100 -- core := has_neg.neg

reserve infixl `; `:1 -- core := has_andthen.andthen
reserve infixl ` ⬝ `:75 -- core
reserve infixl ` + `:65 -- core := has_add.add
reserve infixl ` - `:65 -- core := has_sub.sub
reserve infixl ` * `:70 -- core := has_mul.mul
reserve infixl ` / `:70 -- core := has_div.div
reserve infixl ` % `:70 -- core := has_mod.mod
reserve infixl ` && `:70 -- core := band
reserve infixl ` || `:65 -- core := bor
reserve infixl ` ∩ `:70 -- core := has_inter.inter
reserve infixl ` ∪ `:65 -- core := has_union.union
reserve infixl ` ++ `:65 -- core := has_append.append
reserve infixl ` ∙ `:70

reserve infixr ` ^ `:80 -- core := has_pow.pow
reserve infixr ` ∧ `:35 -- core := and
reserve infixr ` /\ `:35 -- core := and
reserve infixr ` \/ `:30 -- core := or
reserve infixr ` ∨ `:30 -- core := or
reserve infixr ` :: `:67 -- core := list.cons
reserve infixr ` ▸ `:75 -- core := eq.subst
reserve infixr ` ▹ `:75 -- core
reserve infixr ` ⊕ `:30 -- core := sum
reserve infixr ` × `:35 -- core := prod
reserve infixr ` ∘ `:90 -- core := function.comp

reserve infix ` \ `:70 -- core := has_sdiff.sdiff
reserve infix ` <-> `:20 -- core := iff
reserve infix ` ↔ `:20 -- core := iff
reserve infix ` = `:50 -- core := eq
reserve infix ` == `:50 -- core := heq
reserve infix ` ≠ `:50 -- core := ne
reserve infix ` ≈ `:50 -- core := has_equiv.equiv
reserve infix ` ~ `:50 -- core
reserve infix ` ≡ `:50 -- core
reserve infix ` <= `:50 -- core := has_le.le
reserve infix ` ≤ `:50 -- core := has_le.le
reserve infix ` < `:50 -- core := has_lt.lt
reserve infix ` >= `:50 -- core := ge
reserve infix ` ≥ `:50 -- core := ge
reserve infix ` > `:50 -- core := gt
reserve infix ` ∈ `:50 -- core := has_mem.mem
reserve infix ` ∉ `:50 -- core := not (has_mem.mem #1 #0)
reserve infix ` ⊆ `:50 -- core := has_subset.subset
reserve infix ` ⊇ `:50 -- core := superset
reserve infix ` ⊂ `:50 -- core := has_ssubset.ssubset
reserve infix ` ⊃ `:50 -- core := ssuperset
reserve infix ` ∣ `:50 -- core
