-- Copyright © 2019 François G. Dorais. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.

import .basic
import .homomorphism
import .identity

namespace universal
variables {τ : Type} {σ : Type*} (sig : signature τ σ)

namespace algebra

section pi
variables {sig} {ι : Type*} (alg : ι → algebra sig)

definition pi : algebra sig :=
{ sort := λ t, Π j, (alg j).sort t
, func := λ f xs j, (alg j).func f (λ i, xs i j)
}

@[simp] theorem pi_func (f) (xs) (j) : (pi alg).func f xs j = (alg j).func f (λ i, xs i j) := rfl

definition pi_proj (j) : homomorphism (pi alg) (alg j) :=
{ map := λ _ x, x j
, func := λ _ _, rfl
}

theorem pi_eval {dom} : ∀ {cod} (t : term sig dom cod) (xs) (j),
(pi alg).eval t xs j = (alg j).eval t (λ i, xs i j)
| _ (term.proj _) _ _ := rfl
| _ (term.func f ts) xs j :=
  have (λ i, (pi alg).eval (ts i) xs j) = (λ i, (alg j).eval (ts i) (λ i, xs i j)), 
  from funext $ λ i, pi_eval (ts i) xs j,
  calc _ 
  = (alg j).func f (λ i, (pi alg).eval (ts i) xs j) : rfl ...
  = (alg j).func f (λ i, (alg j).eval (ts i) (λ i, xs i j)) : by rw this ...
  = (alg j).eval (term.func f ts) (λ i, xs i j) : by reflexivity

theorem pi_satisfies (e : identity sig) : (∀ i, (alg i).satisfies e) → (pi alg).satisfies e :=
begin
intros H val,
funext,
rw pi_eval,
rw pi_eval,
apply H,
end

section universal_property
variables {alg} {alg₀ : algebra sig} (h : Π j, homomorphism alg₀ (alg j))

definition pi_hom : homomorphism alg₀ (pi alg) :=
{ map := λ t x j, (h j).map t x
, func := λ _ _, funext $ λ j, by simp [(h j).func]
}

@[simp] theorem pi_hom_proj (j) : (pi_proj alg j).comp (pi_hom h) = h j := homomorphism.ext $ λ _ _, rfl

theorem pi_univ (h₀ : homomorphism alg₀ (pi alg)) :
(∀ j, (pi_proj alg j).comp h₀ = h j) → h₀ = pi_hom h :=
λ H, homomorphism.ext $ λ t x, funext $ λ j,
begin
transitivity ((pi_proj alg j).comp h₀).map t x,
reflexivity,
rw H,
reflexivity,
end

end universal_property

end pi

section prod
variables {sig} (alg₁ : algebra sig) (alg₂ : algebra sig)

definition prod : algebra sig :=
{ sort := λ t, alg₁.sort t × alg₂.sort t
, func := λ f xs, (alg₁.func f (λ i, (xs i).fst), alg₂.func f (λ i, (xs i).snd))
}

@[simp] theorem prod_func (f) (xs) : (prod alg₁ alg₂).func f xs = (alg₁.func f (λ i, (xs i).fst), alg₂.func f (λ i, (xs i).snd)) := rfl

definition prod_fst : homomorphism (prod alg₁ alg₂) alg₁ :=
{ map := λ _, prod.fst
, func := λ _ _, rfl
}

definition prod_snd : homomorphism (prod alg₁ alg₂) alg₂ :=
{ map := λ _, prod.snd
, func := λ _ _, rfl
}

theorem prod_eval {dom} : ∀ {cod} (t : term sig dom cod) (xs),
(prod alg₁ alg₂).eval t xs = (alg₁.eval t (λ i, (xs i).fst), alg₂.eval t (λ i, (xs i).snd))
| _ (term.proj _) _ := prod.eq rfl rfl
| _ (term.func f ts) xs :=
  have (λ i, (prod alg₁ alg₂).eval (ts i) xs) = (λ i, 
    (alg₁.eval (ts i) (λ i, (xs i).fst), 
      alg₂.eval (ts i) (λ i, (xs i).snd))),
  from funext $ λ i, prod_eval (ts i) xs,
  calc (prod alg₁ alg₂).eval (term.func f ts) xs
  = (prod alg₁ alg₂).func f (λ i, (prod alg₁ alg₂).eval (ts i) xs) : rfl ...
  = (prod alg₁ alg₂).func f (λ i, (alg₁.eval (ts i) (λ i, (xs i).fst), alg₂.eval (ts i) (λ i, (xs i).snd))) : by rw this ... 
  = (alg₁.eval (term.func f ts) (λ i, (xs i).fst), alg₂.eval (term.func f ts) (λ i, (xs i).snd)) : by reflexivity

theorem prod_eval_fst {dom} {cod} (t : term sig dom cod) (xs) :
((prod alg₁ alg₂).eval t xs).fst = alg₁.eval t (λ i, (xs i).fst) := by rw prod_eval

theorem prod_eval_snd {dom} {cod} (t : term sig dom cod) (xs) :
((prod alg₁ alg₂).eval t xs).snd = alg₂.eval t (λ i, (xs i).snd) := by rw prod_eval

theorem prod_satisfies (e : identity sig) : alg₁.satisfies e → alg₂.satisfies e → (prod alg₁ alg₂).satisfies e :=
begin
intros H₁ H₂ val,
rw prod_eval,
rw prod_eval,
apply prod.eq,
apply H₁,
apply H₂,
end

section universal_property
variables {alg₁ alg₂} {alg : algebra sig} (h₁ : homomorphism alg alg₁) (h₂ : homomorphism alg alg₂)
include h₁ h₂

definition prod_hom : homomorphism alg (prod alg₁ alg₂) :=
{ map := λ t x, (h₁.map t x, h₂.map t x)
, func := λ f xs, prod.eq (by simp [h₁.func f]) (by simp [h₂.func f])
}

@[simp] theorem prod_hom_fst : (prod_fst alg₁ alg₂).comp (prod_hom h₁ h₂) = h₁ := homomorphism.ext $ λ _ _, rfl

@[simp] theorem prod_hom_snd : (prod_snd alg₁ alg₂).comp (prod_hom h₁ h₂) = h₂ := homomorphism.ext $ λ _ _, rfl

theorem prod_univ (h : homomorphism alg (prod alg₁ alg₂)) :
(prod_fst alg₁ alg₂).comp h = h₁ → (prod_snd alg₁ alg₂).comp h = h₂ → h = prod_hom h₁ h₂ :=
λ H₁ H₂, homomorphism.ext $ λ t x, prod.eq 
(begin
transitivity ((prod_fst alg₁ alg₂).comp h).map t x,
reflexivity,
rw H₁,
reflexivity,
end)
(begin
transitivity ((prod_snd alg₁ alg₂).comp h).map t x,
reflexivity,
rw H₂,
reflexivity,
end)

end universal_property

end prod

end algebra

end universal
