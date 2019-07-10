-- Copyright © 2019 François G. Dorais. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.

import .basic
import .relation

@[derive decidable_eq]
inductive {u} index {α : Type u} : list α → Type u
| head (x : α) (xs : list α) : index (x :: xs)
| tail (x : α) (xs : list α) : index xs → index (x :: xs)

namespace index
variable {α : Type*}

@[reducible]
definition val : Π {xs : list α}, index xs → α
| _ (index.head x _) := x
| _ (index.tail _ _ i) := val i

@[simp] theorem val_head (x : α) (xs : list α) : val (index.head x xs) = x := rfl

@[simp] theorem val_tail (x : α) (xs : list α) (i : index xs) : val (index.tail x xs i) = val i := rfl

definition nil_elim {C : Sort*} : Π (i : index (@list.nil α)), C .

section map
variables {β : Type*} (f : α → β)

definition map : Π {xs : list α}, index xs → index (xs.map f)
| _ (index.head _ _) := index.head _ _
| _ (index.tail _ _ i) := index.tail _ _ (map i)

@[simp] theorem map_head (x : α) (xs : list α) : map f (index.head x xs) = index.head (f x) (xs.map f) := rfl

@[simp] theorem map_tail (x : α) (xs : list α) (i : index xs) : map f (index.tail x xs i) = index.tail (f x) (xs.map f) (map f i) := rfl

@[simp] theorem val_map : ∀ {xs : list α} (i : index xs), (i.map f).val = f i.val
| _ (index.head _ _) := rfl
| _ (index.tail _ _ i) := val_map i

definition unmap : Π {xs : list α}, index (xs.map f) → index xs
| (_::_) (index.head _ _) := index.head _ _
| (_::_) (index.tail _ _ i) := index.tail _ _ (unmap i)

@[simp] theorem map_unmap : ∀ {xs : list α} (i : index (xs.map f)), map f (unmap f i) = i
| (_::_) (index.head _ _) := rfl
| (_::_) (index.tail _ _ i) := congr_arg (index.tail _ _) (map_unmap i)

@[simp] theorem unmap_map : ∀ {xs : list α} (i : index xs), unmap f (map f i) = i
| _ (index.head _ _) := rfl
| _ (index.tail _ _ i) := congr_arg (index.tail _ _) (unmap_map i)

end map

definition iota : Π (xs : list α), list (index xs)
| [] := []
| (x :: xs) := (index.head x xs) :: list.map (index.tail x xs) (iota xs)

definition iota_index : Π {xs : list α}, index xs → index (iota xs)
| _ (index.head _ _) := index.head _ _
| _ (index.tail _ _ i) := index.tail _ _ (map _ $ iota_index i)

@[simp] theorem iota_index_val : Π {xs : list α} (i : index xs), (iota_index i).val = i
| _ (index.head _ _) := rfl
| _ (index.tail x xs i) := by rw [iota_index, val_tail, val_map, iota_index_val i]

definition to_fin : Π {xs : list α}, index xs → fin xs.length
| _ (index.head x xs) := eq.rec_on (eq.symm $ list.length_cons x xs) 0
| _ (index.tail x xs i) := eq.rec_on (eq.symm $ list.length_cons x xs) (fin.succ $ to_fin i)

definition of_fin : Π {xs : list α}, fin xs.length → index xs
| [] ⟨i, hi⟩ := absurd hi (nat.not_lt_zero i)
| (x :: xs) ⟨0, _⟩ := index.head x xs
| (x :: xs) ⟨i+1, hi⟩ := index.tail x xs (of_fin ⟨i, nat.lt_of_succ_lt_succ hi⟩)

abbreviation to_nat {xs : list α} (i : index xs) : nat := (to_fin i).val

theorem to_nat_lt_lenth {xs : list α} (i : index xs) : i.to_nat < xs.length := (to_fin i).is_lt

definition of_nat {xs : list α} (i : nat) : option (index xs) :=
if hi : i < xs.length then some (of_fin ⟨i, hi⟩) else none

abbreviation of_nat_lt_length {xs : list α} (i : nat) : i < xs.length → index xs := λ hi, of_fin ⟨i, hi⟩

abbreviation dtup {xs : list α} (β : index xs → Sort*) := Π i, β i

namespace dtup

section nil
variable {β : index (@list.nil α) → Sort*}

definition nil : Π i, β i .

@[simp] theorem eq_nil (t : Π i, β i) : t = nil := funext $ λ i, nil i

theorem eq_of_nil (t₁ t₂ : Π i, β i) : t₁ = t₂ := by rw [dtup.eq_nil t₁, dtup.eq_nil t₂]

end nil

section cons
variables {x : α} {xs : list α} {β : index (x :: xs) → Sort*}

abbreviation head : (Π i, β i) → β (index.head x xs) := λ t, t (index.head x xs) 

abbreviation tail : (Π i, β i) → (Π i, β (index.tail x xs i)) := λ t i, t (index.tail x xs i) 

definition cons : head β → (Π i, tail β i) → (Π i, β i)
| h _ (index.head _ _) := h
| _ t (index.tail _ _ i) := t i

@[simp] theorem cons_head_tail (t : Π i, β i) : cons (head t) (tail t) = t :=
funext $ λ i, match i with
| (index.head _ _) := rfl
| (index.tail _ _ i) := rfl
end

variables (h : head β) (t : Π i, tail β i)

@[simp] theorem cons_of_index_head : cons h t (index.head x xs) = h := rfl

@[simp] theorem cons_of_index_tail (i : index xs) : cons h t (index.tail x xs i) = t i := rfl

@[simp] theorem head_cons : head (cons h t) = h := rfl

@[simp] theorem tail_cons : tail (cons h t) = t := rfl

end cons

section enum
variables {xs : list α} {β : index xs → Type*} (t : Π i, β i) 

abbreviation enum : list (sigma β) := list.map (λ i, ⟨i, t i⟩) (iota xs)

abbreviation enum_index : index xs → index (enum t) := λ i, map _ (iota_index i)

@[simp] theorem enum_index_val (i : index xs) : (enum_index t i).val = ⟨i, t i⟩ :=
by rw [val_map, iota_index_val]

end enum

definition to_list {xs : list α} {β : Type*} (t : index xs → β) : list β :=
list.map (λ (z : sigma (λ _, β)), sigma.snd z) (enum t)

section fold

definition foldl : Π {xs : list α} {β : index xs → Sort*} {γ : Sort*} (f : Π {{i}}, γ → β i → γ), γ → (Π i, β i) → γ
| [] _ _ _ z _ := z
| (_::_) _ _ f z t := f (foldl (tail f) z (tail t)) (head t)

definition foldr : Π {xs : list α} {β : index xs → Sort*} {γ : Sort*} (f : Π {{i}}, β i → γ → γ), γ → (Π i, β i) → γ
| [] _ _ _ z _ := z
| (_::_) _ _ f z t := f (head t) (foldr (tail f) z (tail t))

@[simp] theorem foldl_nil {β : index (@list.nil α) → Sort*} {γ : Sort*} (f : Π {{i}}, γ → β i → γ) (z : γ) :
foldl f z nil = z := rfl

@[simp] theorem foldr_nil {β : index (@list.nil α) → Sort*} {γ : Sort*} (f : Π {{i}}, β i → γ → γ) (z : γ) :
foldr f z nil = z := rfl

variables {x : α} {xs : list α} {β : index (x :: xs) → Sort*} {γ : Sort*}

@[simp] theorem foldl_cons (f : Π {{i}}, γ → β i → γ) (z : γ) (h : head β) (t : Π i, tail β i) :
foldl f z (cons h t) = f (foldl (tail f) z t) h := rfl

@[simp] theorem foldr_cons (f : Π {{i}}, β i → γ → γ) (z : γ) (h : head β) (t : Π i, tail β i) :
foldr f z (cons h t) = f h (foldr (tail f) z t) := rfl

@[simp] theorem foldl_head_tail (f : Π {{i}}, γ → β i → γ) (z : γ) (t : Π i, β i) :
foldl f z t = f (foldl (tail f) z (tail t)) (head t) := rfl

@[simp] theorem foldr_head_tail (f : Π {{i}}, β i → γ → γ) (z : γ) (t : Π i, β i) :
foldr f z t = f (head t) (foldr (tail f) z (tail t)) := rfl

end fold

end dtup

definition decidable_exists_def : Π {xs : list α} (p : index xs → Prop) (dp : ∀ i, decidable (p i)), decidable (∃ i, p i)
| [] _ _ := decidable.is_false (λ ⟨i,_⟩, nil_elim i)
| (_::_) p dp :=
  match decidable_exists_def (dtup.tail p) (dtup.tail dp) with
  | decidable.is_true ht := decidable.is_true (exists.elim ht $ λ i hi, ⟨_, hi⟩)
  | decidable.is_false ht :=
    match dtup.head dp with
    | decidable.is_true hh := decidable.is_true ⟨_, hh⟩
    | decidable.is_false hh :=
      have ¬ ∃ i, p i, 
      begin
      intro h,
      cases h with i hi,
      cases i,
      exact hh hi,
      exact ht ⟨_, hi⟩,
      end,
      decidable.is_false this
    end
  end

instance decidable_exists {xs : list α} (p : index xs → Prop) [dp : Π i, decidable (p i)] : decidable (∃ i, p i) := decidable_exists_def p dp

definition decidable_forall_def : Π {xs : list α} (p : index xs → Prop) (dp : ∀ i, decidable (p i)), decidable (∀ i, p i)
| [] _ _ := decidable.is_true (λ i, nil_elim i)
| (_::_) p dp :=
  match decidable_forall_def (dtup.tail p) (dtup.tail dp) with
  | decidable.is_false ht := decidable.is_false (λ h, ht (dtup.tail h))
  | decidable.is_true ht :=
    match dtup.head dp with
    | decidable.is_false hh := decidable.is_false (λ h, hh (dtup.head h))
    | decidable.is_true hh := decidable.is_true (dtup.cons hh ht)
    end
  end

instance decidable_forall {xs : list α} (p : index xs → Prop) [dp : Π i, decidable (p i)] : decidable (∀ i, p i) := decidable_forall_def p dp

theorem choice : ∀ {xs : list α} {β : index xs → Sort*}, (∀ i, nonempty (β i)) → nonempty (Π i, β i)
| [] _ _ := nonempty.intro dtup.nil
| (_::_) C H := 
  have Hh : nonempty (dtup.head C), from dtup.head H,
  have Ht : nonempty (Π i, dtup.tail C i), from choice (dtup.tail H),
  nonempty.elim Hh $ λ h, nonempty.elim Ht $ λ t, nonempty.intro (dtup.cons h t)

section relation
open relation

theorem ec_of_ec_tail {x : α} {xs : list α} {β : index (x :: xs) → Sort*} {r : Π i, β i → β i → Prop} (hhr : reflexive (dtup.head r)) {h : dtup.head β} {t₁ t₂ : Π i, dtup.tail β i} :
ec (pi (dtup.tail r)) t₁ t₂ → ec (pi r) (dtup.cons h t₁) (dtup.cons h t₂) :=
λ e, ec.rec_on e
  (λ _ _ hxy, ec.base $ dtup.cons (hhr h) hxy) 
  (λ _, ec.refl _) 
  (λ _ _ _ _ _ hxy hxz, ec.eucl hxy hxz)

theorem ec_of_ec_head {x : α} {xs : list α} {β : index (x :: xs) → Sort*} {r : Π i, β i → β i → Prop} (htr : reflexive (pi (dtup.tail r))) {h₁ h₂ : dtup.head β} {t : Π i, dtup.tail β i} :
ec (dtup.head r) h₁ h₂ → ec (pi r) (dtup.cons h₁ t) (dtup.cons h₂ t) :=
λ e, ec.rec_on e
  (λ _ _ hxy, ec.base $ dtup.cons hxy (htr _)) 
  (λ _, ec.refl _) 
  (λ _ _ _ _ _ hxy hxz, ec.eucl hxy hxz)

theorem ec_of_ec_head_tail {x : α} {xs : list α} {β : index (x :: xs) → Sort*} {r : Π i, β i → β i → Prop} (hr : ∀ i, reflexive (r i)) {h₁ h₂ : dtup.head β} {t₁ t₂ : Π i, dtup.tail β i} :
ec (dtup.head r) h₁ h₂ → ec (pi (dtup.tail r)) t₁ t₂ → ec (pi r) (dtup.cons h₁ t₁) (dtup.cons h₂ t₂) :=
λ eh et,
have hhr : reflexive (dtup.head r), from dtup.head hr,
have htr : reflexive (pi (dtup.tail r)), from pi_reflexive (dtup.tail hr),
have e₁ : ec (pi r) (dtup.cons h₁ t₁) (dtup.cons h₂ t₁), from ec_of_ec_head htr eh, 
have e₂ : ec (pi r) (dtup.cons h₂ t₁) (dtup.cons h₂ t₂), from ec_of_ec_tail hhr et,
ec.trans e₁ e₂

theorem ec_pi_of_pi_ec : ∀ {xs : list α} {β : index xs → Sort*} {r : Π i, β i → β i → Prop} (hr : ∀ i, reflexive (r i)) {t₁ t₂ : Π i, β i}, pi (λ i, ec (r i)) t₁ t₂ → ec (pi r) t₁ t₂
| [] _ _ _ t₁ t₂ _ := by { rw [dtup.eq_nil t₁, dtup.eq_nil t₂], apply ec.refl _ }
| (_::_) _ r hr t₁ t₂ h :=
  have eh : ec (dtup.head r) (dtup.head t₁) (dtup.head t₂), from dtup.head h,
  have et : ec (pi (dtup.tail r)) (dtup.tail t₁) (dtup.tail t₂), from ec_pi_of_pi_ec (dtup.tail hr) (dtup.tail h),
  by {rw [← dtup.cons_head_tail t₁, ← dtup.cons_head_tail t₂], exact ec_of_ec_head_tail hr eh et }

variables {xs : list α} {β : index xs → Sort*} {r : Π i, β i → β i → Prop} (hr : ∀ i, reflexive (r i))

theorem pi_ec_iff_ec_pi (t₁ t₂ : Π i, β i) : pi (λ i, ec (r i)) t₁ t₂ ↔ ec (pi r) t₁ t₂ :=
⟨ec_pi_of_pi_ec hr, pi_ec_of_ec_pi⟩

theorem pi_ec_eq_ec_pi : pi (λ i, ec (r i)) = ec (pi r) :=
funext $ λ t₁, funext $ λ t₂, propext $ pi_ec_iff_ec_pi hr t₁ t₂

end relation

section setoid

instance setoid {xs : list α} (β : index xs → Sort*) [Π i, setoid (β i)] : setoid (Π i, β i) :=
{ r := λ x y, ∀ i, x i ≈ y i
, iseqv := mk_equivalence _
  (λ x i, setoid.refl (x i))
  (λ _ _ h i, setoid.symm (h i))
  (λ _ _ _ hxy hyz i, setoid.trans (hxy i) (hyz i))
}

theorem setoid.r_iff {xs : list α} {C : index xs → Sort*} [Π i, setoid (C i)] (t₁ t₂ : Π i, C i) :
t₁ ≈ t₂ ↔ (∀ i, t₁ i ≈ t₂ i) := iff.rfl

theorem setoid.r_cons_iff {x : α} {xs : list α} {C : index (x :: xs) → Sort*} [Π i, setoid (C i)] (t₁ t₂ : Π i, C i) :
t₁ ≈ t₂ ↔ dtup.head t₁ ≈ dtup.head t₂ ∧ dtup.tail t₁ ≈ dtup.tail t₂ :=
⟨ λ h, have h : ∀ i, t₁ i ≈ t₂ i, from (setoid.r_iff t₁ t₂).mp h, ⟨dtup.head h, dtup.tail h⟩
, λ ⟨hh, ht⟩, have h : ∀ i, t₁ i ≈ t₂ i, from dtup.cons hh ht, (setoid.r_iff t₁ t₂).mpr h
⟩

theorem setoid.r_cons {x : α} {xs : list α} {C : index (x :: xs) → Sort*} [Π i, setoid (C i)]
(h₁ h₂ : dtup.head C) (t₁ t₂ : Π i, dtup.tail C i) : h₁ ≈ h₂ → t₁ ≈ t₂ → dtup.cons h₁ t₁ ≈ dtup.cons h₂ t₂ :=
begin
intros eh et,
rw setoid.r_cons_iff,
simp only [dtup.head_cons, dtup.tail_cons],
split; assumption
end

end setoid

end index

namespace quot
open index
open relation
variable {α : Type*}

abbreviation index_mk {xs : list α} {β : index xs → Sort*} (r : Π i, β i → β i → Prop) (t : Π i, β i) : Π i, quot (r i) := λ i, quot.mk (r i) (t i)

@[elab_as_eliminator]
theorem index_ind : ∀ {xs : list α} {β : index xs → Sort*} {r : Π i, β i → β i → Prop} (hr : ∀ i, reflexive (r i)) {P : (Π i, quot (r i)) → Prop},
(∀ (t : Π i, β i), P (λ i, quot.mk (r i) (t i))) → ∀ q, P q
| [] β r hr P H q := by { rw [dtup.eq_nil q, ← dtup.eq_nil (λ i, @quot.mk (β i) (r i) (dtup.nil i))], apply H }
| (x::xs) β r hr P H q :=
  have ∀ (h : dtup.head β) (t : Π i, dtup.tail β i), (λ i, quot.mk (r i) (dtup.cons h t i)) = dtup.cons (quot.mk (dtup.head r) h) (λ i, quot.mk (dtup.tail r i) (t i)), by { intros, funext i, cases i; reflexivity },
  have IH : ∀ (h : dtup.head β) (q : Π i, quot (dtup.tail r i)), P (dtup.cons (quot.mk (dtup.head r) h) q),
  from λ h q, index_ind (dtup.tail hr) (by {introv, rw ← this, apply H}) q,
  begin
  rw [← dtup.cons_head_tail q],
  induction (dtup.head q) using quot.ind with h,
  apply IH,
  end

@[elab_as_eliminator]
theorem index_induction_on {xs : list α} {β : index xs → Sort*} {r : Π i, β i → β i → Prop} (hr : ∀ i, reflexive (r i)) {P : (Π i, quot (r i)) → Prop} (q : Π i, quot (r i)) :
(∀ (t : Π i, β i), P (λ i, quot.mk (r i) (t i))) → P q :=
λ H, index_ind hr H q

def index_map {xs : list α} {β : index xs → Sort*} (r : Π i, β i → β i → Prop) :
quot (pi r) → Π i, quot (r i) :=
quot.lift (λ (t : Π i, β i) (i : index xs), quot.mk (r i) (t i)) $
λ (t₁ t₂ : Π i, β i) (h : pi r t₁ t₂), funext $ λ i, quot.sound (h i)

def index_map_beta {xs : list α} {β : index xs → Sort*} {r : Π i, β i → β i → Prop} (t : Π i, β i) :
index_map r (quot.mk (pi r) t) = λ i, quot.mk (r i) (t i) := rfl

section index_cons
variables {x : α} {xs : list α} {β : index (x :: xs) → Sort*} {r : Π i, β i → β i → Prop}

def index_cons_func (hr : reflexive (dtup.head r)) : dtup.head β → quot (pi (dtup.tail r)) → quot (pi r) :=
λ h, quot.lift (λ t, quot.mk (pi r) (dtup.cons h t)) $
λ t₁ t₂ ht, quot.sound (dtup.cons (hr h) ht)

theorem index_cons_func_beta {hr : reflexive (dtup.head r)} (h : dtup.head β) (t : Π i, dtup.tail β i) :
index_cons_func hr h (quot.mk (pi (dtup.tail r)) t) = quot.mk (pi r) (dtup.cons h t) := rfl

def index_cons (hr : ∀ i, reflexive (r i)) : quot (dtup.head r) → quot (pi (dtup.tail r)) → quot (pi r) :=
quot.lift (index_cons_func (dtup.head hr)) $
begin
intros h₁ h₂ hh,
funext t,
induction t using quot.ind,
rw index_cons_func_beta,
rw index_cons_func_beta,
apply quot.sound,
apply dtup.cons,
exact hh,
exact pi_reflexive (dtup.tail hr) t,
end

theorem index_cons_beta {hr : ∀ i, reflexive (r i)} (h : dtup.head β) (t : Π i, dtup.tail β i) :
index_cons hr (quot.mk (dtup.head r) h) (quot.mk (pi (dtup.tail r)) t) = quot.mk (pi r) (dtup.cons h t) := rfl

end index_cons

def index_inv : Π {xs : list α} {β : index xs → Sort*} {r : Π i, β i → β i → Prop} (hr : Π i, reflexive (r i)), 
(Π i, quot (r i)) → quot (pi r)
| [] _ r _ _ := quot.mk (pi r) dtup.nil
| (_::_) _ _ hr q := index_cons hr (dtup.head q) (index_inv (dtup.tail hr) (dtup.tail q))

theorem index_inv_nil {β : index (@list.nil α) → Sort*} {r : Π i, β i → β i → Prop} {hr : Π i, reflexive (r i)} :
index_inv hr dtup.nil = quot.mk (pi r) dtup.nil := rfl

theorem index_inv_cons {x : α} {xs : list α} {β : index (x :: xs) → Sort*} {r : Π i, β i → β i → Prop} {hr : Π i, reflexive (r i)} (h : quot (dtup.head r)) (t : Π i, quot (dtup.tail r i)) :
index_inv hr (dtup.cons h t) = index_cons hr h (index_inv (dtup.tail hr) t) := rfl

theorem index_inv_head_tail {x : α} {xs : list α} {β : index (x :: xs) → Sort*} {r : Π i, β i → β i → Prop} {hr : Π i, reflexive (r i)} (q : Π i, quot (r i)) :
index_inv hr q = index_cons hr (dtup.head q) (index_inv (dtup.tail hr) (dtup.tail q)) := rfl

theorem index_inv_beta : Π {xs : list α} {β : index xs → Sort*} {r : Π i, β i → β i → Prop} {hr : Π i, reflexive (r i)} (t : Π i, β i), 
index_inv hr (λ i, quot.mk (r i) (t i)) = quot.mk (pi r) t
| [] _ _ _ t := by { rw [dtup.eq_nil t], reflexivity }
| (x::xs) β r hr t := by { rw [index_inv_head_tail, index_inv_beta, index_cons_beta], simp }

theorem index_inv_map {xs : list α} {β : index xs → Sort*} {r : Π i, β i → β i → Prop} {hr : ∀ i, reflexive (r i)} :
∀ (q : quot (pi r)), index_inv hr (index_map r q) = q := quot.ind (by intro; rw [index_map_beta, index_inv_beta])

theorem index_map_inv {xs : list α} {β : index xs → Sort*} {r : Π i, β i → β i → Prop} {hr : ∀ i, reflexive (r i)} :
∀ (q : Π i, quot (r i)), index_map r (index_inv hr q) = q := quot.index_ind hr (by intro; rw [index_inv_beta, index_map_beta])

@[elab_as_eliminator, reducible]
def index_lift {xs : list α} {β : index xs → Sort*} {r : Π i, β i → β i → Prop} (hr : Π i, reflexive (r i)) {γ : Sort*} (f : (Π i, β i) → γ) :
(∀ t₁ t₂, pi r t₁ t₂ → f t₁ = f t₂) → (Π i, quot (r i)) → γ := λ H q, quot.lift f H (index_inv hr q)

@[elab_as_eliminator, reducible]
abbreviation index_lift_on {xs : list α} {β : index xs → Sort*} {r : Π i, β i → β i → Prop} (hr : Π i, reflexive (r i)) (q : Π i, quot (r i)) {γ : Sort*} (f : (Π i, β i) → γ) :
(∀ t₁ t₂, pi r t₁ t₂ → f t₁ = f t₂) → γ := λ H, index_lift hr f H q

theorem index_lift_def {xs : list α} {β : index xs → Sort*} {r : Π i, β i → β i → Prop} {hr : Π i, reflexive (r i)} {γ : Sort*} (f : (Π i, β i) → γ) {H : ∀ t₁ t₂, pi r t₁ t₂ → f t₁ = f t₂} (q : Π i, quot (r i)) :
index_lift hr f H q = quot.lift f H (index_inv hr q) := rfl

theorem index_lift_map {xs : list α} {β : index xs → Sort*} {r : Π i, β i → β i → Prop} {hr : Π i, reflexive (r i)} {γ : Sort*} (f : (Π i, β i) → γ) {H : ∀ t₁ t₂, pi r t₁ t₂ → f t₁ = f t₂} (q : quot (pi r)) :
index_lift hr f H (index_map r q) = quot.lift f H q := by rw [← index_inv_map q] {occs:=occurrences.pos[2]}

theorem index_lift_beta {xs : list α} {β : index xs → Sort*} {r : Π i, β i → β i → Prop} {hr : Π i, reflexive (r i)} {γ : Sort*} (f : (Π i, β i) → γ) {H : ∀ t₁ t₂, pi r t₁ t₂ → f t₁ = f t₂} (t : Π i, β i) :
index_lift hr f H (λ i, quot.mk (r i) (t i)) = f t := by rw [← index_map_beta, index_lift_map]

end quot

namespace quotient
open index
variables {α : Type*} {xs : list α} {β : index xs → Sort*} [s : Π i, setoid (β i)]
include s

definition index_lift {γ : Sort*} (f : (Π i, β i) → γ) :
(∀ (t₁ t₂ : Π i, β i), (∀ i, t₁ i ≈ t₂ i) → f t₁ = f t₂) → (Π i, quotient (s i)) → γ :=
have hr : ∀ i, reflexive (setoid.r : β i → β i → Prop), from λ i, (s i).iseqv.refl,
quot.index_lift hr f

theorem index_lift_beta {γ : Sort*} (f : (Π i, β i) → γ) {H : ∀ (t₁ t₂ : Π i, β i), (∀ i, t₁ i ≈ t₂ i) → f t₁ = f t₂} :
∀ (t : Π i, β i), index_lift f H (λ i, ⟦t i⟧) = f t := 
have hr : ∀ i, reflexive (setoid.r : β i → β i → Prop), from λ i, (s i).iseqv.refl,
begin
intro,
dunfold index_lift,
apply quot.index_lift_beta,
end

theorem index_ind {P : (Π i, quotient (s i)) → Prop} :
(∀ (t : Π i, β i), P (λ i, ⟦t i⟧)) → ∀ q, P q := 
have hr : ∀ i, reflexive (setoid.r : β i → β i → Prop), from λ i, (s i).iseqv.refl,
λ H, quot.index_ind hr H

theorem index_induction_on {P : (Π i, quotient (s i)) → Prop} (q : Π i, quotient (s i)) :
(∀ (t : Π i, β i), P (λ i, ⟦t i⟧)) → P q := λ H, index_ind H q

end quotient
