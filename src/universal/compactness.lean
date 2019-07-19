import .basic
import .model
import .proof

namespace universal
variables {τ : Type} {σ : Type*} {sig : signature τ σ} {ι : Type} {ax : ι → identity sig}

namespace proof
variables {ι' : Type} {ax' : ι' → identity sig} (ht : Π (i : ι), proof ax' (ax i).lhs (ax i).rhs)

definition transfer {dom} : Π {cod} {t₁ t₂ : term sig dom cod} (p : proof ax t₁ t₂), proof ax' t₁ t₂
| _ _ _ (proof.ax i sub) := proof.subst sub (ht i) 
| _ _ _ (proof.proj _) := proof.proj _
| _ _ _ (proof.func f ps) := proof.func f (λ i, transfer (ps i))
| _ _ _ (proof.eucl p₁ p₂) := proof.eucl (transfer p₁) (transfer p₂)

definition transfer_of_map (f : ι → ι') (hf : ∀ i, ax' (f i) = ax i) (i : ι) : proof ax' (ax i).lhs (ax i).rhs :=
eq.rec_on (hf i) $ proof.ax_id (f i)

end proof

definition proof.occurs {dom} : Π {cod} {t₁ t₂ : term sig dom cod}, proof ax t₁ t₂ → ι → Prop
| _ _ _ (proof.ax i _) j := i = j
| _ _ _ (proof.proj _) _ := false
| _ _ _ (proof.func _ ps) j := ∃ i, proof.occurs (ps i) j
| _ _ _ (proof.eucl p₁ p₂) j := proof.occurs p₁ j ∨ proof.occurs p₂ j

definition proof.use {dom} : Π {cod} {t₁ t₂ : term sig dom cod}, proof ax t₁ t₂ → list ι
| _ _ _ (proof.ax i _) := [i]
| _ _ _ (proof.proj _) := []
| _ _ _ (proof.func _ ps) := list.join $ index.dtup.to_list (λ i, proof.use (ps i))
| _ _ _ (proof.eucl p₁ p₂) := proof.use p₁ ++ proof.use p₂

theorem proof.mem_use_of_occurs {dom} : Π {cod} {t₁ t₂ : term sig dom cod} {p : proof ax t₁ t₂} {i : ι}, proof.occurs p i → i ∈ proof.use p
| _ _ _ (proof.ax i _) j h := eq.rec_on h (or.inl rfl)
| _ _ _ (proof.proj _) _ h := absurd h not_false
| _ _ _ (proof.func _ ps) j h :=
  exists.elim h $ λ i hi,
  let i' : index (index.dtup.to_list (λ i, proof.use (ps i))) := index.map _ (index.dtup.enum_index _ i) in
  have hi' : j ∈ i'.val, by { rw [index.val_map, index.dtup.enum_index_val], exact proof.mem_use_of_occurs hi },
  list.mem_join j i' hi'
| _ _ _ (proof.eucl p₁ p₂) j h :=  or.elim h (λ h, list.mem_append_left _ (proof.mem_use_of_occurs h)) (λ h, list.mem_append_right _ (proof.mem_use_of_occurs h))

definition proof.of_use {dom} : Π {cod} {t₁ t₂ : term sig dom cod} (p : proof ax t₁ t₂), proof (λ (i : index p.use), ax i.val) t₁ t₂
| _ t₁ t₂ p@(proof.ax i sub) := proof.subst sub $ proof.ax_id (index.head i [])
| _ _ _ (proof.proj _) := proof.proj _
| _ _ _ p@(@proof.func _ _ _ _ _ _ f lhs rhs ps) :=
  let m : Π (i : sig.index f) (j : index (ps i).use), index p.use :=
  λ i j, index.join_map _ (index.dtup.to_list_index _ i) $ eq.rec_on (index.dtup.to_list_index_val (λ i, (ps i).use) i).symm j in
  let ps : Π (i : sig.index f), proof (λ (i : index p.use), ax i.val) (lhs i) (rhs i) :=
  λ i, proof.transfer (proof.transfer_of_map (m i) (by {intro, simp})) (proof.of_use (ps i)) in
  proof.func f ps
| _ t₁ t₂ p@(@proof.eucl _ _ _ _ _ _ _ t _ _ p₁ p₂) :=
  let p₁ : proof (λ (i : index p.use), ax i.val) t t₁ :=
  proof.transfer (proof.transfer_of_map (index.append_left _ _) (by {intro, rw [index.append_left_val]})) (proof.of_use p₁) in
  let p₂ : proof (λ (i : index p.use), ax i.val) t t₂ :=
  proof.transfer (proof.transfer_of_map (index.append_right _ _) (by {intro, rw [index.append_right_val]})) (proof.of_use p₂) in
  proof.eucl p₁ p₂

theorem compactness (e : identity sig) : models ax e → ∃ (as : list ι), models (λ (i : index as), ax i.val) e :=
begin
intros hm,
cases completeness ax e hm with hp,
existsi hp.use,
apply soundness,
constructor,
exact proof.of_use hp,
end

end universal
