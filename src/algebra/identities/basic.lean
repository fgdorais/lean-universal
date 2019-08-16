-- Copyright © 2019 François G. Dorais. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.

import util.identities

variables {α : Sort*} {β : Sort*} {γ : Sort*} {δ : Sort*} {ε : Sort*} {η : Sort*}

namespace algebra.identity

@[identity]
protected abbreviation op_commutative (op : α → α → α) : Prop := ∀ x y, op x y = op y x

@[identity]
protected abbreviation op_symmetric (op : α → α → β) : Prop := ∀ x y, op x y = op y x

@[identity]
protected abbreviation op_opposite (op : α → β → γ) (op' : out_param $ β → α → γ) : Prop := ∀ x y, op x y = op' y x

@[identity]
protected abbreviation op_left_commutative (op : α → β → β) : Prop := ∀ x y z, op x (op y z) = op y (op x z)

@[identity]
protected abbreviation op_right_commutative (op : α → β → α) : Prop := ∀ x y z, op (op x y) z = op (op x z) y

@[identity]
protected abbreviation op_associative (op : α → α → α) : Prop := ∀ x y z, op (op x y) z = op x (op y z)

@[identity]
protected abbreviation op_left_compatible (op : α → β → β) (op' : out_param $ α → α → α) : Prop := ∀ x y z, op (op' x y) z = op x (op y z)

@[identity]
protected abbreviation op_right_compatible (op : α → β → α) (op' : out_param $ β → β → β) : Prop := ∀ x y z, op (op x y) z = op x (op' y z)

@[identity]
protected abbreviation op_compatibility (op₁ : α → β → γ) (op₂ : δ → ε → α) (op₃ : δ → η → γ) (op₄ : ε → β → η) : Prop := ∀ x y z, op₁ (op₂ x y) z = op₃ x (op₄ y z)

@[identity]
protected abbreviation op_left_identity (op : α → β → β) (ct : out_param $ α) : Prop := ∀ x, op ct x = x

@[identity]
protected abbreviation op_right_identity (op : α → β → α) (ct : out_param $ β) : Prop := ∀ x, op x ct = x

@[identity]
protected abbreviation op_left_inverse (op : α → β → γ) (fn : out_param $ β → α) (ct : out_param $ γ) : Prop := ∀ x, op (fn x) x = ct

@[identity]
protected abbreviation op_right_inverse (op : α → β → γ) (fn : out_param $ α → β) (ct : out_param $ γ) : Prop := ∀ x, op x (fn x) = ct

@[identity]
protected abbreviation op_left_division (op : α → β → γ) (op' : out_param $ α → γ → β) : Prop := ∀ x y, op x (op' x y) = y

@[identity]
protected abbreviation op_right_division (op : α → β → γ) (op' : out_param $ γ → β → α) : Prop := ∀ x y, op (op' y x) x = y

@[identity]
protected abbreviation op_left_cancellative (op : α → β → γ) : Prop := ∀ {{x y z}}, op x y = op x z → y = z

@[identity]
protected abbreviation op_right_cancellative (op : α → β → γ) : Prop := ∀ {{x y z}}, op x y = op z y → x = z

@[identity]
protected abbreviation op_idempotent (op : α → α → α) : Prop := ∀ x, op x x = x

@[identity]
protected abbreviation op_left_absorptive (op₁ : α → β → β) (op₂ : γ → β → α) : Prop := ∀ x y, op₁ (op₂ x y) y = y

@[identity]
protected abbreviation op_right_absorptive (op₁ : α → β → α) (op₂ : α → γ → β) : Prop := ∀ x y, op₁ x (op₂ x y) = x

@[identity]
protected abbreviation op_op_left_cancellative (op₁ : α → β → γ) (op₂ : α → β → δ) : Prop := ∀ {{x y z}}, op₁ x y = op₁ x z → op₂ x y = op₂ x z → y = z

@[identity]
protected abbreviation op_op_right_cancellative (op₁ : α → β → γ) (op₂ : α → β → δ) : Prop := ∀ (x y z), op₁ x y = op₁ z y → op₂ x y = op₂ z y → x = z

@[identity]
protected abbreviation fn_fixpoint (fn : α → α) (ct : out_param $ α) : Prop := fn ct = ct

@[identity]
protected abbreviation fn_idempotent (fn : α → α) : Prop := ∀ x, fn (fn x) = fn x

@[identity]
protected abbreviation fn_injective (fn : α → β) : Prop := ∀ {{x y}}, fn x = fn y → x = y

@[identity]
protected abbreviation fn_fn_commutative (fn_1 : α → α) (fn_2 : α → α) : Prop := ∀ x, fn_1 (fn_2 x) = fn_2 (fn_1 x)

@[identity]
protected abbreviation fn_fn_inverse (fn_1 : α → β) (fn_2 : β → α) : Prop := ∀ x, fn_1 (fn_2 x) = x

@[identity]
protected abbreviation fn_fn_inverse' (fn_1 : α → β) (fn_2 : β → α) : Prop := ∀ x y, fn_1 x = y → fn_2 y = x

@[identity]
protected abbreviation fn_involutive (fn : α → α) : Prop := ∀ x, fn (fn x) = x

@[identity]
protected abbreviation op_left_fixpoint (op : α → β → α) (ct : out_param $ α) : Prop := ∀ x, op ct x = ct

@[identity]
protected abbreviation op_right_fixpoint (op : α → β → β) (ct : out_param $ β) : Prop := ∀ x, op x ct = ct

@[identity]
protected abbreviation fn_ct_homomorphism (fn : α → β) (ct_1 : out_param $ α) (ct_2 : out_param $ β) : Prop := fn ct_1 = ct_2

@[identity]
protected abbreviation fn_fn_homomorphism (fn : α → β) (fn_1 : out_param $ α → α) (fn_2 : out_param $ β → β) : Prop := ∀ x, fn (fn_1 x) = fn_2 (fn x)

@[identity]
protected abbreviation fn_op_homomorphism (fn : α → β) (op_1 : out_param $ α → α → α) (op_2 : out_param $ β → β → β) : Prop := ∀ x y, fn (op_1 x y) = op_2 (fn x) (fn y)

@[identity]
protected abbreviation fn_op_antimorphism (fn : α → β) (op_1 : out_param $ α → α → α) (op_2 : out_param $ β → β → β) : Prop := ∀ x y, fn (op_1 x y) = op_2 (fn y) (fn x)

@[identity]
protected abbreviation op_left_ct_homomorphism (op : α → β → γ) (ct_1 : out_param $ α) (ct_2 : out_param $ γ) : Prop := ∀ x, op ct_1 x = ct_2

@[identity]
protected abbreviation op_right_ct_homomorphism (op : α → β → γ) (ct_1 : out_param $ β) (ct_2 : out_param $ γ) : Prop := ∀ x, op x ct_1 = ct_2

@[identity]
protected abbreviation op_left_fn_homomorphism (op : α → β → γ) (fn_1 : out_param $ α → α) (fn_2 : out_param $ γ → γ) : Prop := ∀ x y, op (fn_1 x) y = fn_2 (op x y)

@[identity]
protected abbreviation op_right_fn_homomorphism (op : α → β → γ) (fn_1 : out_param $ β → β) (fn_2 : out_param $ γ → γ) : Prop := ∀ x y, op x (fn_1 y) = fn_2 (op x y)

@[identity]
protected abbreviation op_left_op_homomorphism (op : α → β → γ) (op_1 : out_param $ α → α → α) (op_2 : out_param $ γ → γ → γ) : Prop := ∀ x y z, op (op_1 x y) z = op_2 (op x z) (op y z)

@[identity]
protected abbreviation op_right_op_homomorphism (op : α → β → γ) (op_1 : out_param $ β → β → β) (op_2 : out_param $ γ → γ → γ) : Prop := ∀ x y z, op x (op_1 y z) = op_2 (op x y) (op x z)

@[identity]
protected abbreviation op_left_distributive (op_1 : α → β → α) (op_2 : out_param $ α → α → α) : Prop := ∀ x y z, op_1 (op_2 x y) z = op_2 (op_1 x z) (op_1 y z)

@[identity]
protected abbreviation op_right_distributive (op_1 : α → β → β) (op_2 : out_param $ β → β → β) : Prop := ∀ x y z, op_1 x (op_2 y z) = op_2 (op_1 x y) (op_1 x z)

end algebra.identity

namespace algebra.class
set_option default_priority 0

instance op_left_compatible_of_op_compatibility (op : α → β → β) (op' : α → α → α) [op_compatibility op op' op op] : op_left_compatible op op' :=
op_left_compatible.of_pattern _ _

instance op_right_compatible_of_op_compatibility (op : α → β → α) (op' : β → β → β) [op_compatibility op op op op'] : op_right_compatible op op' :=
op_right_compatible.of_pattern _ _

instance op_associative_of_op_left_compatible (op : α → α → α) [op_left_compatible op op] : op_associative op :=
op_associative.of_pattern _

instance op_associative_of_op_right_compatible (op : α → α → α) [op_right_compatible op op] : op_associative op :=
op_associative.of_pattern _

instance op_symmetric_of_op_opposite (op : α → α → β) [op_opposite op op] : op_symmetric op :=
op_symmetric.of_pattern _

instance op_commutative_of_op_symmetric (op : α → α → α) [op_symmetric op] : op_commutative op :=
op_commutative.of_pattern _

instance fn_fixpoint_of_fn_ct_homomorphism (fn : α → α) (ct : α) [fn_ct_homomorphism fn ct ct] : fn_fixpoint fn ct :=
fn_fixpoint.of_pattern _ _

instance fn_fn_commutative_of_fn_fn_homomorphism (fn_1 : α → α) (fn_2 : α → α) [fn_fn_homomorphism fn_1 fn_2 fn_2] : fn_fn_commutative fn_1 fn_2 :=
fn_fn_commutative.of_pattern _ _

instance fn_involutive_of_fn_fn_inverse (fn : α → α) [fn_fn_inverse fn fn] : fn_involutive fn :=
fn_involutive.of_pattern _

instance op_left_fixpoint_of_op_left_ct_homomorphism_of_op_left_fixpoint (op : α → β → α) (ct : α) [op_left_ct_homomorphism op ct ct] : op_left_fixpoint op ct :=
op_left_fixpoint.of_pattern _ _

instance op_right_fixpoint_of_op_right_ct_homomorphism_of_op_right_fixpoint (op : α → β → β) (ct : β) [op_right_ct_homomorphism op ct ct] : op_right_fixpoint op ct :=
op_right_fixpoint.of_pattern _ _

instance op_left_distributive_of_op_left_op_homomorphism (op_1 : α → β → α) (op_2 : α → α → α) [op_left_op_homomorphism op_1 op_2 op_2] : op_left_distributive op_1 op_2 :=
op_left_distributive.of_pattern _ _

instance op_right_distributive_of_op_right_op_homomorphism (op_1 : α → β → β) (op_2 : β → β → β) [op_right_op_homomorphism op_1 op_2 op_2] : op_right_distributive op_1 op_2 :=
op_right_distributive.of_pattern _ _

end algebra.class
