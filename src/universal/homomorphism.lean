-- Copyright © 2019 François G. Dorais. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.

import .basic
import .substitution

namespace universal
variables {τ : Type} {σ : Type*} {sig : signature τ σ}

structure homomorphism (alg₁ : algebra sig) (alg₂ : algebra sig) :=
(map {} (t) : alg₁.sort t → alg₂.sort t)
(func (f : σ) : ∀ (xs : Π (i : sig.index f), alg₁.sort i.val), alg₂.func f (λ i, map _ (xs i)) = map _ (alg₁.func f xs))

instance (alg₁ : algebra sig) (alg₂ : algebra sig) : has_coe_to_fun (homomorphism alg₁ alg₂) :=
{ F := λ _, Π {t}, alg₁.sort t → alg₂.sort t
, coe := λ h, h.map
}

namespace homomorphism
variables {alg₁ : algebra sig} {alg₂ : algebra sig} {alg₃ : algebra sig}

theorem eq : Π {{h₁ h₂ : homomorphism alg₁ alg₂}}, h₁.map = h₂.map → h₁ = h₂
| ⟨_,_⟩ ⟨_,_⟩ rfl := rfl

theorem ext {{h₁ h₂ : homomorphism alg₁ alg₂}} : (∀ {t} (x : alg₁.sort t), h₁.map t x = h₂.map t x) → h₁ = h₂ :=
λ H, eq $ funext $ λ _, funext $ λ x, H x

definition id (alg : algebra sig) : homomorphism alg alg :=
{ map := λ _, id
, func := λ _ _, rfl
}

definition comp (h₂₃ : homomorphism alg₂ alg₃) (h₁₂ : homomorphism alg₁ alg₂) : homomorphism alg₁ alg₃ :=
{ map := λ t x, h₂₃.map t (h₁₂.map t x)
, func := λ f xs, eq.subst (h₁₂.func f xs) (h₂₃.func f _)
}

class injective (h : homomorphism alg₁ alg₂) : Prop := intro ::
(elim (t) : function.injective (h.map t))

class surjective (h : homomorphism alg₁ alg₂) : Prop := intro ::
(elim (t) : function.surjective (h.map t))

instance comp.inj (h₂₃ : homomorphism alg₂ alg₃) (h₁₂ : homomorphism alg₁ alg₂)
[injective h₂₃] [injective h₁₂] : injective (comp h₂₃ h₁₂) :=
⟨λ t, function.injective_comp (injective.elim h₂₃ t) (injective.elim h₁₂ t)⟩

instance comp.surj (h₂₃ : homomorphism alg₂ alg₃) (h₁₂ : homomorphism alg₁ alg₂)
[surjective h₂₃] [surjective h₁₂] : surjective (comp h₂₃ h₁₂) :=
⟨λ t, function.surjective_comp (surjective.elim h₂₃ t) (surjective.elim h₁₂ t)⟩

@[priority 0]
instance id.inj (alg : algebra sig) : injective (id alg) := ⟨λ _, function.injective_id⟩

@[priority 0]
instance id.surj (alg : algebra sig) : surjective (id alg) := ⟨λ _, function.surjective_id⟩

theorem eval (h : homomorphism alg₁ alg₂) {dom} :
∀ {cod} (t : term sig dom cod) (val : Π (i : index dom), alg₁.sort i.val),
h.map _ (alg₁.eval t val) = alg₂.eval t (λ i, h.map _ (val i))
| _ (term.proj i) val := rfl
| _ (term.func f ts) val :=
  have IH : (λ i, h.map _ (alg₁.eval (ts i) val)) = (λ i, alg₂.eval (ts i) (λ i, h.map _ (val i))),
  from funext $ λ i, eval (ts i) val,
  calc h.map _ (alg₁.eval (term.func f ts) val)
  = h.map _ (alg₁.func f (λ i, alg₁.eval (ts i) val)) : rfl ...
  = alg₂.func f (λ i, h.map _ (alg₁.eval (ts i) val)) : by rw h.func ...
  = alg₂.func f (λ i, alg₂.eval (ts i) (λ i, h.map _ (val i))) : by rw IH ...
  = alg₂.eval (term.func f ts) (λ i, h.map _ (val i)) : by reflexivity

end homomorphism

namespace algebra.valuation
variables {alg₁ : algebra sig} {alg₂ : algebra sig} (h : homomorphism alg₁ alg₂)

definition map {dom} (val : algebra.valuation alg₁ dom) : algebra.valuation alg₂ dom := λ i, h (val i)

theorem map_eval {dom} (val : algebra.valuation alg₁ dom) :
∀ {cod} (x : term sig dom cod), alg₂.eval x (val.map h) = h.map cod (alg₁.eval x val)
| _ (term.proj _) := rfl
| _ (term.func f xs) :=
  have (λ i, alg₂.eval (xs i) (val.map h)) = (λ i, h.map _ (alg₁.eval (xs i) val)),
  from funext $ λ i, map_eval (xs i),
  calc _
  = alg₂.func f (λ i, alg₂.eval (xs i) (val.map h)) : rfl ...
  = alg₂.func f (λ i, h.map _ (alg₁.eval (xs i) val)) : by rw this ...
  = h.map _ (alg₁.func f (λ i, alg₁.eval (xs i) val)) : by rw h.func f ...
  = h.map _ (alg₁.eval (term.func f xs) val) : by rw alg₁.eval_func

end algebra.valuation

definition algebra.eval_hom (alg : algebra sig) {dom : list τ} (val : Π (i : index dom), alg.sort i.val) :
homomorphism (term_algebra sig dom) alg :=
{ map := λ (cod) (t : term sig dom cod), alg.eval t val
, func := λ _ _, rfl
}

definition term.subst_hom {dom₁ dom₂ : list τ} (sub : substitution sig dom₁ dom₂) :
homomorphism (term_algebra sig dom₁) (term_algebra sig dom₂) :=
{ map := term.subst sub
, func := λ _ _, rfl
}

end universal
