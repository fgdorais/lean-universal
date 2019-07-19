-- Copyright © 2019 François G. Dorais. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.

import .basic

namespace universal
variables {τ : Type} {σ : Type*} (sig : signature τ σ)

abbreviation substitution (dom₁ dom₂ : list τ) := Π (i : index dom₁), term sig dom₂ i.val

namespace substitution
variables {sig} {dom₁ dom₂ dom₃ : list τ} (sub : substitution sig dom₁ dom₂)

abbreviation to_valuation : algebra.valuation (term_algebra sig dom₂) dom₁ := sub

abbreviation apply {cod} (t : term sig dom₁ cod) : term sig dom₂ cod :=
algebra.eval (term_algebra sig dom₂) t sub

theorem apply_def {cod} (t : term sig dom₁ cod) : sub.apply t = (term_algebra sig dom₂).eval t sub := rfl

theorem apply_proj {i : index dom₁} : sub.apply (term.proj i) = sub i := rfl

theorem apply_func {f} (ts : Π (i : sig.index f), term sig dom₁ i.val) :
sub.apply (term.func f ts) = term.func f (λ i, sub.apply (ts i)) := rfl

theorem eval (alg : algebra sig) : ∀ {cod} (t : term sig dom₁ cod) (val : Π (i : index dom₂), alg.sort i.val),
alg.eval (sub.apply t) val = alg.eval t (λ i, alg.eval (sub i) val)
| _ (term.proj i) val := rfl
| _ (term.func f ts) val :=
  have IH : (λ i, alg.eval (sub.apply (ts i)) val) = (λ i, alg.eval (ts i) (λ i, alg.eval (sub i) val)),
  from funext $ λ i, eval (ts i) val,
  calc alg.eval (sub.apply (term.func f ts)) val
  = alg.func f (λ i, alg.eval (sub.apply (ts i)) val) : rfl ...
  = alg.func f (λ i, alg.eval (ts i) (λ i, alg.eval (sub i) val)) : by rw IH ...
  = alg.eval (term.func f ts) (λ (i : index dom₁), alg.eval (sub i) val) : by reflexivity

abbreviation id {dom : list τ} : substitution sig dom dom := term.proj

@[simp] theorem id_apply {dom : list τ} : ∀ {cod} (t : term sig dom cod), substitution.id.apply t = t
| _ (term.proj _) := rfl
| _ (term.func f ts) := 
  have (λ i, apply id (ts i)) = ts,
  from funext $ λ i, id_apply (ts i),
  calc apply id (term.func f ts)
  = term.func f (λ i, apply id (ts i)) : rfl ...
  = term.func f ts : by rw this

abbreviation comp : substitution sig dom₂ dom₃ → substitution sig dom₁ dom₂ → substitution sig dom₁ dom₃ :=
λ sub₂₃ sub₁₂ i, sub₂₃.apply (sub₁₂ i)

@[simp] theorem comp_apply (sub₂₃ : substitution sig dom₂ dom₃) (sub₁₂ : substitution sig dom₁ dom₂) :
∀ {cod} (t : term sig dom₁ cod), (comp sub₂₃ sub₁₂).apply t = sub₂₃.apply (sub₁₂.apply t)
| _ (term.proj _) := rfl
| _ (term.func f ts) :=
  have (λ i, (comp sub₂₃ sub₁₂).apply (ts i)) = (λ i, sub₂₃.apply (sub₁₂.apply (ts i))),
  from funext $ λ i, comp_apply (ts i),
  calc (comp sub₂₃ sub₁₂).apply (term.func f ts)
  = term.func f (λ i, (comp sub₂₃ sub₁₂).apply (ts i)) : rfl ...
  = term.func f (λ i, sub₂₃.apply (sub₁₂.apply (ts i))) : by rw this ...
  = sub₂₃.apply (term.func f (λ i, sub₁₂.apply (ts i))) : by rw apply_func sub₂₃ ...
  = sub₂₃.apply (apply sub₁₂ (term.func f ts)) : by rw apply_func sub₁₂

end substitution

section subst 
variables {sig} {dom₁ dom₂ : list τ} (sub : substitution sig dom₁ dom₂)

abbreviation term.subst {{cod}} : term sig dom₁ cod → term sig dom₂ cod := sub.apply

abbreviation equation.subst {{cod}} : equation sig dom₁ cod → equation sig dom₂ cod :=
λ e, ⟨sub.apply e.lhs, sub.apply e.rhs⟩

theorem equation.subst_lhs {cod} (e : equation sig dom₁ cod) : (e.subst sub).lhs = e.lhs.subst sub := rfl

theorem equation.subst_rhs {cod} (e : equation sig dom₁ cod) : (e.subst sub).rhs = e.rhs.subst sub := rfl

theorem subst_subst {dom₁ dom₂ dom₃ : list τ} (sub₂₃ : substitution sig dom₂ dom₃) (sub₁₂ : substitution sig dom₁ dom₂) {cod} (t : term sig dom₁ cod) :
t.subst (λ i, (sub₁₂ i).subst sub₂₃) = (t.subst sub₁₂).subst sub₂₃ := substitution.comp_apply sub₂₃ sub₁₂ t

@[simp] theorem subst_proj {dom} {cod} (t : term sig dom cod) : t.subst term.proj = t := substitution.id_apply t

end subst



end universal
