-- Copyright © 2019 François G. Dorais. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.

import .basic

section relation
variables {α : Sort*} (r : α → α → Prop)

definition euclidean : Prop := ∀ {{x y z}}, r x y → r x z → r y z

definition equivalence.mk : reflexive r → euclidean r → equivalence r :=
λ hr he, mk_equivalence r hr (λ _ _ hxy, he hxy (hr _)) (λ _ _ _ hxy hyz, he (he hxy (hr _)) hyz)

inductive ec : α → α → Prop
| base {{x y}} : r x y → ec x y
| refl {} (x) : ec x x
| eucl {{x y z}} : ec x y → ec x z → ec y z

theorem tc_transitive : transitive (tc r) := tc.trans

theorem ec_equivalence : equivalence (ec r) := equivalence.mk (ec r) ec.refl ec.eucl

variable {r}

theorem equivalence.refl : equivalence r → reflexive r := λ ⟨hr, _, _⟩, hr

theorem equivalence.symm : equivalence r → symmetric r := λ ⟨_, hs, _⟩, hs

theorem equivalence.trans : equivalence r → transitive r := λ ⟨_, _, ht⟩, ht

theorem equivalence.eucl : equivalence r → euclidean r :=  λ ⟨_, hs, ht⟩ x y z h₁ h₂, ht (hs h₁) h₂ 

theorem tc.mono {s : α → α → Prop} : (∀ {{x y}}, r x y → s x y) → ∀ {{x y}}, tc r x y → tc s x y :=
λ hrs x y htc, tc.rec_on htc (λ _ _ hxy, tc.base _ _ (hrs hxy)) (λ _ _ _ _ _ ixy iyz, tc.trans _ _ _ ixy iyz)

theorem tc.elim {s : α → α → Prop} (hs : transitive s) : (∀ {{x y}}, r x y → s x y) → ∀ {{x y}}, tc r x y → s x y :=
λ hrs x y htc, tc.rec_on htc hrs (λ _ _ _ _ _ ixy iyz, hs ixy iyz)

theorem tc.elim_self (hr : transitive r) : ∀ {{x y}}, tc r x y → r x y := tc.elim hr (λ _ _, id)

theorem ec_of_eq : ∀ {{x y}}, x = y → ec r x y
| _ _ rfl := ec.refl _

theorem ec.symm {{x y}} : ec r x y → ec r y x :=
λ h, ec.eucl h $ ec.refl x

theorem ec.trans {{x y z}} : ec r x y → ec r y z → ec r x z :=
λ h₁ h₂, ec.eucl (ec.symm h₁) h₂

theorem ec.mono {s : α → α → Prop} : (∀ {{x y}}, r x y → s x y) → ∀ {{x y}}, ec r x y → ec s x y :=
λ h x y hec, ec.rec_on hec (λ _ _ hr, ec.base (h hr)) (λ x, ec.refl x) (λ _ _ _ _ _ ixy ixz, ec.eucl ixy ixz)

theorem ec.elim {s : α → α → Prop} (hs : equivalence s) : (∀ {{x y}}, r x y → s x y) → ∀ {{x y}}, ec r x y → s x y :=
λ hrs x y, ec.rec hrs (λ x, hs.refl x) (λ _ _ _ _ _ ixy ixz, hs.eucl ixy ixz)

theorem ec.elim_self (hr : equivalence r) : ∀ {{x y}}, ec r x y → r x y := ec.elim hr (λ _ _, id)

theorem tc_iff_self_of_transitive (hr : transitive r) (x y) : tc r x y ↔ r x y :=
⟨λ h, tc.elim_self hr h, λ h, tc.base _ _ h⟩  

theorem tc_eq_self_of_transitive (hr : transitive r) : tc r = r :=
funext $ λ x, funext $ λ y, propext $ tc_iff_self_of_transitive hr x y

theorem ec_iff_self_of_equivalence (hr : equivalence r) (x y) : ec r x y ↔ r x y :=
⟨λ h, ec.elim_self hr h, λ h, ec.base h⟩

theorem ec_eq_self_of_equivalence (hr : equivalence r) : ec r = r :=
funext $ λ x, funext $ λ y, propext $ ec_iff_self_of_equivalence hr x y

theorem ec_of_ec_rc {{x y}} : ec (λ x y, r x y ∨ x = y) x y → ec r x y :=
λ e, ec.rec_on e
(λ _ _ hxy, or.elim hxy (λ h, ec.base h) (λ h, ec_of_eq h))
(λ _, ec.refl _)
(λ _ _ _ _ _ hxy hxz, ec.eucl hxy hxz)

theorem ec_rc_of_ec {{x y}} : ec r x y → ec (λ x y, r x y ∨ x = y) x y :=
λ h, ec.mono (λ _ _, or.inl) h

variable (r)

theorem ec_rc_eq_ec : ec (λ x y, r x y ∨ x = y) = ec r :=
funext $ λ x, funext $ λ y, propext $ ⟨λ h, ec_of_ec_rc h, λ h, ec_rc_of_ec h⟩

theorem tc_idempotent : tc (tc r) = tc r := tc_eq_self_of_transitive (tc_transitive r)

theorem ec_idempotent : ec (ec r) = ec r := ec_eq_self_of_equivalence (ec_equivalence r)

lemma ec_of_eqv_gen {α : Type*} {r : α → α → Prop} {{x y : α}} : eqv_gen r x y → ec r x y :=
λ h, eqv_gen.rec_on h
  (λ _ _ h, ec.base h)
  (λ _, ec.refl _)
  (λ _ _ _ ixy, ec.symm ixy)
  (λ _ _ _ _ _ ixy iyz, ec.trans ixy iyz)

lemma eqv_gen_of_ec {α : Type*} {r : α → α → Prop} {{x y : α}} : ec r x y → eqv_gen r x y :=
λ h, ec.rec_on h
  (λ _ _ h, eqv_gen.rel _ _ h)
  (λ _, eqv_gen.refl _)
  (λ _ _ _ _ _ ixy ixz, eqv_gen.trans _ _ _ (eqv_gen.symm _ _ ixy) ixz)

theorem eqv_gen_iff_ec {α : Type*} (r : α → α → Prop) (x y : α) : eqv_gen r x y ↔ ec r x y :=
⟨λ h, ec_of_eqv_gen h, λ h, eqv_gen_of_ec h⟩

theorem eqv_gen_eq_ec {α : Type*} (r : α → α → Prop) : eqv_gen r = ec r :=
funext $ λ x, funext $ λ y, propext $ eqv_gen_iff_ec r x y

end relation

namespace quot
variables {α : Sort*} {r : α → α → Prop}

private def ecq : quot r → quot r → Prop :=
have h₀ : ∀ x₁ x₂, r x₁ x₂ → ec r x₁ = ec r x₂,
from λ x₁ x₂ h, funext $ λ y, propext $ ⟨ec.eucl (ec.base h), ec.eucl (ec.symm (ec.base h))⟩,
let r₁ : quot r → α → Prop := quot.lift (ec r) h₀ in
have h₁ : ∀ x y₁ y₂, r y₁ y₂ → r₁ x y₁ = r₁ x y₂,
from λ x, quot.induction_on x (λ x y₁ y₂ h, show ec r x y₁ = ec r x y₂, from propext ⟨λ h₁, ec.trans h₁ (ec.base h), λ h₂, ec.trans h₂ (ec.symm (ec.base h))⟩),
λ x, quot.lift (r₁ x) $ (h₁ x)

private lemma ecq_refl (x : quot r) : ecq x x := quot.induction_on x ec.refl

private lemma ecq_of_eq : ∀ {x y : quot r}, x = y → ecq x y | _ _ rfl := ecq_refl _

theorem ec_exact {x y : α} : quot.mk r x = quot.mk r y → ec r x y := ecq_of_eq

theorem ec_sound {x y : α} : ec r x y → quot.mk r x = quot.mk r y :=
λ h, ec.rec_on h
  (λ _ _ h, quot.sound h)
  (λ _, rfl)
  (λ _ _ _ _ _ hxy hxz, eq.subst hxy hxz)

end quot

definition relation.pi {α : Sort*} {β : α → Sort*} (r : Π i, β i → β i → Prop) (x y : Π i, β i) : Prop := ∀ i, r i (x i) (y i)

namespace relation
variables {α : Sort*} {β : α → Sort*} {r : Π i, β i → β i → Prop}

theorem pi_reflexive : (∀ i, reflexive (r i)) → reflexive (pi r) := λ h x i, h i (x i)

theorem pi_symmetric : (∀ i, symmetric (r i)) → symmetric (pi r) := λ h x y hxy i, h i (hxy i)

theorem pi_transitive : (∀ i, transitive (r i)) → transitive (pi r) := λ h x y z hxy hyz i, h i (hxy i) (hyz i)

theorem pi_euclidean : (∀ i, euclidean (r i)) → euclidean (pi r) := λ h x y z hxy hxz i, h i (hxy i) (hxz i)

theorem pi_equivalence : (∀ i, equivalence (r i)) → equivalence (pi r) :=
λ heq, equivalence.mk (pi r) (pi_reflexive $ λ i, equivalence.refl (heq i)) (pi_euclidean $ λ i, equivalence.eucl (heq i))

theorem pi_tc_of_tc_pi {t₁ t₂ : Π i, β i} : tc (pi r) t₁ t₂ → pi (λ i, tc (r i)) t₁ t₂ :=
have htr : transitive (pi (λ i, tc (r i))), from pi_transitive (λ i, tc_transitive (r i)),
have hin : ∀ {{t₁ t₂}}, pi r t₁ t₂ → pi (λ i, tc (r i)) t₁ t₂, from λ _ _ h i, tc.base _ _ (h i),
λ h, tc.elim htr hin h

theorem pi_ec_of_ec_pi {t₁ t₂ : Π i, β i} : ec (pi r) t₁ t₂ → pi (λ i, ec (r i)) t₁ t₂ :=
have heq : equivalence (pi (λ i, ec (r i))), from pi_equivalence (λ i, ec_equivalence (r i)),
have hin : ∀ {{t₁ t₂}}, pi r t₁ t₂ → pi (λ i, ec (r i)) t₁ t₂, from λ _ _ h i, ec.base (h i),
λ h, ec.elim heq hin h

end relation

definition {u v} relation.pr {α₁ : Sort u} {α₂ : Sort v} (r : pprod (α₁ → α₁ → Prop) (α₂ → α₂ → Prop)) (x y : pprod α₁ α₂) : Prop := r.fst x.fst y.fst ∧ r.snd x.snd y.snd

namespace relation
variables {α₁ : Sort*} {α₂ : Sort*} {r : pprod (α₁ → α₁ → Prop) (α₂ → α₂ → Prop)}

theorem pr_reflexive : reflexive r.fst → reflexive r.snd → reflexive (pr r) :=
λ h₁ h₂ ⟨x₁, x₂⟩, ⟨h₁ x₁, h₂ x₂⟩

theorem pr_symmetric : symmetric r.fst → symmetric r.snd → symmetric (pr r) :=
λ h₁ h₂ _ _ ⟨hxy₁, hxy₂⟩, ⟨h₁ hxy₁, h₂ hxy₂⟩

theorem pr_transitive : transitive r.fst → transitive r.snd → transitive (pr r) :=
λ h₁ h₂ _ _ _ ⟨hxy₁, hxy₂⟩ ⟨hyz₁, hyz₂⟩, ⟨h₁ hxy₁ hyz₁, h₂ hxy₂ hyz₂⟩

theorem pr_euclidean : euclidean r.fst → euclidean r.snd → euclidean (pr r) :=
λ h₁ h₂ _ _ _ ⟨hxy₁, hxy₂⟩ ⟨hxz₁, hxz₂⟩, ⟨h₁ hxy₁ hxz₁, h₂ hxy₂ hxz₂⟩

theorem pr_equivalence : equivalence r.fst → equivalence r.snd → equivalence (pr r) :=
λ h₁ h₂, equivalence.mk (pr r) (pr_reflexive (equivalence.refl h₁) (equivalence.refl h₂)) (pr_euclidean (equivalence.eucl h₁) (equivalence.eucl h₂))

theorem pr_tc_of_tc_pr {x y : pprod α₁ α₂} : tc (pr r) x y → pr ⟨tc r.fst, tc r.snd⟩ x y :=
have htr : transitive (pr ⟨tc r.fst, tc r.snd⟩), from pr_transitive (tc_transitive r.fst) (tc_transitive r.snd),
have hin : ∀ {{x y}}, pr r x y → pr ⟨tc r.fst, tc r.snd⟩ x y, from λ _ _ ⟨hxy₁, hxy₂⟩, ⟨tc.base _ _ hxy₁, tc.base _ _ hxy₂⟩,
λ h, tc.elim htr hin h

theorem pr_ec_of_ec_pr {x y : pprod α₁ α₂} : ec (pr r) x y → pr ⟨ec r.fst, ec r.snd⟩ x y :=
have heq : equivalence (pr ⟨ec r.fst, ec r.snd⟩), from pr_equivalence (ec_equivalence r.fst) (ec_equivalence r.snd),
have hin : ∀ {{x y}}, pr r x y → pr ⟨ec r.fst, ec r.snd⟩ x y, from λ _ _ ⟨hxy₁, hxy₂⟩, ⟨ec.base hxy₁, ec.base hxy₂⟩,
λ h, ec.elim heq hin h

end relation
