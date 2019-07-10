-- Copyright © 2019 François G. Dorais. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.

import .basic
import .identity
import .congruence
import .model

namespace universal
universe u
variables {τ : Type} {σ : Type u} {sig : signature τ σ} {ι : Type} (ax : ι → identity sig)

inductive proof {ι : Type} (ax : ι → identity sig) {dom : list τ} : Π {cod : τ}, term sig dom cod → term sig dom cod → Type u
| ax (i : ι) (sub : substitution sig (ax i).dom dom) : proof (sub.apply (ax i).lhs) (sub.apply (ax i).rhs)
| proj {} (i : index dom) : proof (term.proj i) (term.proj i)
| func (f : σ) {lhs rhs : Π (i : sig.index f), term sig dom i.val} : (Π i, proof (lhs i) (rhs i)) → proof (term.func f lhs) (term.func f rhs)
| eucl {cod : τ} {{t u v : term sig dom cod}} : proof t u → proof t v → proof u v

namespace proof
variables {ax} {dom : list τ}

definition refl : Π {cod} (t : term sig dom cod), proof ax t t
| _ (term.proj i) := proof.proj i
| _ (term.func f ts) := proof.func f (λ i, refl (ts i))

definition rfl {cod} {t : term sig dom cod} : proof ax t t := proof.refl t

definition symm {cod} {{t u : term sig dom cod}} : proof ax t u → proof ax u t :=
λ h, proof.eucl h $ proof.refl t

definition trans {cod} {{t u v : term sig dom cod}} :
proof ax t u → proof ax u v → proof ax t v :=
λ h₁ h₂, proof.eucl h₁.symm h₂

definition subst {dom₁ dom₂ : list τ} (sub : substitution sig dom₁ dom₂) :
Π {cod : τ} {t u : term sig dom₁ cod}, proof ax t u → proof ax (sub.apply t) (sub.apply u)
| _ _ _ (proof.ax i isub) :=
  eq.rec_on (substitution.comp_apply sub isub (ax i).lhs) $
  eq.rec_on (substitution.comp_apply sub isub (ax i).rhs) $
  proof.ax i (substitution.comp sub isub)
| _ _ _ (proof.proj i) := proof.rfl
| _ _ _ (proof.func f hs) := proof.func f (λ i, subst (hs i))
| _ _ _ (proof.eucl h₁ h₂) := proof.eucl (subst h₁) (subst h₂)

variables (sig dom ax)

definition to_congruence : congruence (term_algebra sig dom) :=
{ r := λ _ t u, nonempty (proof ax t u)
, refl := λ _ _, ⟨proof.rfl⟩
, eucl := λ _ _ _ _ ⟨h₁⟩ ⟨h₂⟩, ⟨proof.eucl h₁ h₂⟩
, func := λ f _ _ h, nonempty.elim (index.choice h) (λ h, ⟨proof.func f h⟩)
}

end proof

theorem proof.sound {dom} : ∀ {cod} {t u : term sig dom cod}, proof ax t u → valid ax t u
| _ _ _ (proof.ax i sub) := valid.ax i sub
| _ _ _ (proof.proj i) := valid.refl (term.proj i)
| _ _ _ (proof.func f hs) := valid.app f (λ i, proof.sound (hs i))
| _ _ _ (proof.eucl h₁ h₂) := valid.eucl (proof.sound h₁) (proof.sound h₂)

definition proves (e : identity sig) : Prop := nonempty (proof ax e.lhs e.rhs)

theorem soundness (e : identity sig) : proves ax e → models ax e := λ ⟨h⟩, proof.sound ax h

abbreviation init_algebra (dom : list τ) : algebra sig := quotient (term_algebra sig dom) (proof.to_congruence sig ax dom)

namespace init_algebra

theorem satisfies_exact (e : identity sig) : 
(init_algebra ax e.dom).satisfies e → proves ax e :=
begin
rw ← quotient.satisfies,
intro H,
cases H substitution.id with H,
rw ← substitution.apply_def substitution.id at H,
rw ← substitution.apply_def substitution.id at H,
rw substitution.id_apply at H,
rw substitution.id_apply at H,
exact ⟨H⟩,
end

theorem satisfies_axiom (dom) (i) : algebra.satisfies (init_algebra ax dom) (ax i) :=
begin
rw ← quotient.satisfies (proof.to_congruence sig ax dom) (ax i),
intro sub,
apply nonempty.intro,
exact proof.ax i sub,
end

end init_algebra

theorem completeness (e : identity sig) : models ax e → proves ax e :=
begin
intro H,
apply init_algebra.satisfies_exact,
apply H,
apply init_algebra.satisfies_axiom,
end

end universal
