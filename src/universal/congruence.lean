-- Copyright © 2019 François G. Dorais. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.

import .basic
import .homomorphism
import .identity

namespace universal
variables {τ : Type} {σ : Type} {sig : signature τ σ} (alg : algebra sig)

structure congruence :=
(r (t) : alg.sort t → alg.sort t → Prop)
(refl {t} (x : alg.sort t) : r t x x)
(eucl {t} {{x y z : alg.sort t}} : r t x y → r t x z → r t y z)
(func (f) {xs ys : Π (i : sig.index f), alg.sort i.val} : (∀ i, r _ (xs i) (ys i)) → r _ (alg.func f xs) (alg.func f ys))

namespace congruence
variables {alg} (con : congruence alg)

theorem rfl {t} {x : alg.sort t} : con.r t x x := con.refl x

theorem symm {t} {{x y : alg.sort t}} : con.r t x y → con.r t y x :=
λ h, con.eucl h con.rfl

theorem trans {t} {{x y z : alg.sort t}} : con.r t x y → con.r t y z → con.r t x z :=
λ hxy hyz, con.eucl (con.symm hxy) hyz

definition to_reflexive (t) : reflexive (con.r t) := λ x, con.refl x

definition to_symmetric (t) : symmetric (con.r t) := λ _ _ hxy, con.symm hxy

definition to_transitive (t) : transitive (con.r t) := λ _ _ _ hxy hyz, con.trans hxy hyz

definition to_euclidean (t) : euclidean (con.r t) := λ _ _ _ hxy hxz, con.eucl hxy hxz

definition to_equivalence (t) : equivalence (con.r t) :=
equivalence.mk _ (con.to_reflexive t) (con.to_euclidean t)

definition to_setoid (t) : setoid (alg.sort t) :=
{ r := con.r t
, iseqv := con.to_equivalence t
}

end congruence

definition quotient (con : congruence alg) : algebra sig :=
have hr : ∀ t, reflexive (con.r t), from λ t, con.to_reflexive t,
{ sort := λ t, quot (con.r t)
, func := λ f xs, 
  have hr : ∀ i : sig.index  f, reflexive (con.r i.val), from λ i, con.to_reflexive i.val,
  let fn := λ (xs : Π i : sig.index f, alg.sort i.val), quot.mk (con.r (sig.cod f)) (alg.func f xs) in
  quot.lift_on (quot.index_inv hr xs) fn $
  begin
  intros xs ys h,
  apply quot.sound,
  apply con.func,
  exact h,
  end
}

variables {alg} (con : congruence alg)

abbreviation quotient.mk {{t}} : alg.sort t → (quotient alg con).sort t := quot.mk (con.r t)

theorem quotient.func_beta (f : σ) (xs : Π (i : sig.index f), alg.sort i.val) :
algebra.func (quotient alg con) f (λ i, quotient.mk con (xs i)) = quotient.mk con (alg.func f xs) :=
quot.index_lift_beta _ _

theorem quotient.mk_exact {t} {x y : alg.sort t} : quotient.mk con x = quotient.mk con y → con.r t x y :=
λ h, ec.elim_self (con.to_equivalence t) (quot.ec_exact h)

theorem quotient.mk_sound {t} {x y : alg.sort t} : con.r t x y → quotient.mk con x = quotient.mk con y := quot.sound

definition quotient_hom : homomorphism alg (quotient alg con) :=
{ map := quotient.mk con
, func := quotient.func_beta con
}

instance quotient_hom.surj : homomorphism.surjective (quotient_hom con) := ⟨λ _ x, quot.induction_on x (λ x, ⟨x, rfl⟩)⟩

theorem quotient.exact {t} {x y : alg.sort t} : (quotient_hom con).map _ x = (quotient_hom con).map _ y → con.r t x y :=
λ h, ec.elim_self (con.to_equivalence t) (quot.ec_exact h)

theorem quotient.sound {t} {x y : alg.sort t} : con.r t x y → (quotient_hom con).map _ x = (quotient_hom con).map _ y := quot.sound

definition quotient.lift {alg'} (h : homomorphism alg alg') (H : ∀ t x y, con.r t x y → h x = h y) :
homomorphism (quotient alg con) alg' :=
{ map := λ t x, quot.lift (h.map t) (H t) x
, func := λ f xs, quot.index_induction_on (λ i, con.to_reflexive i.val) xs $ λ xs,
  calc alg'.func f (λ i, quot.lift (h.map i.val) (H i.val) (quotient.mk con (xs i)))
  = h.map (sig.cod f) (alg.func f xs) : by rw h.func f xs ...
  = quot.lift (h.map (sig.cod f)) (H (sig.cod f)) ((quotient alg con).func f (λ i, quotient.mk con (xs i))) : by rw quotient.func_beta con f xs
}

theorem quotient.lift_beta {alg'} (h : homomorphism alg alg') {H : ∀ t x y, con.r t x y → h.map t x = h.map t y} {t} (x : alg.sort t) :
(quotient.lift con h H).map t (quotient.mk con x) = h.map t x := rfl

namespace homomorphism
variables {alg₁ : algebra sig} {alg₂ : algebra sig} (h : homomorphism alg₁ alg₂)

definition kernel (h : homomorphism alg₁ alg₂) : congruence alg₁ :=
{ r := λ t x y, h.map t x = h.map t y
, refl := λ _ _, rfl
, eucl := λ _ _ _ _ e₁ e₂, eq.subst e₁ e₂  
, func := λ f xs ys es, 
  eq.subst (h.func f xs) $
  eq.subst (h.func f ys) $
  congr_arg _ $ funext es
}

definition image : algebra sig := quotient alg₁ (kernel h)

definition image_map : homomorphism alg₁ (image h) := quotient_hom (kernel h)

definition image_inc : homomorphism (image h) alg₂ := quotient.lift (kernel h) h (λ _ _ _ a, a)

instance image_inc.inj : injective (image_inc h) :=
⟨λ t x₁ x₂, quot.induction_on x₁ $ λ x₁, quot.induction_on x₂ $ λ x₂ hx, quot.sound hx⟩

theorem image_factorization : comp (image_inc h) (image_map h) = h := homomorphism.ext $ λ _ _, rfl

end homomorphism

abbreviation congruence.satisfies (ax : identity sig) : Prop :=
∀ (val : Π (i : index ax.dom), alg.sort i.val), con.r _ (alg.eval ax.lhs val) (alg.eval ax.rhs val)

namespace quotient
variables {con}

theorem satisfies_sound (ax : identity sig) : 
con.satisfies ax → (quotient alg con).satisfies ax :=
λ H val, quot.index_induction_on (λ i, con.to_reflexive i.val) val $
λ ts, calc (quotient alg con).eval (identity.lhs ax) (λ i, (quotient_hom con).map _ (ts i))
= (quotient_hom con).map _ (alg.eval (identity.lhs ax) ts) : by rw homomorphism.eval ...
= (quotient_hom con).map _ (alg.eval (identity.rhs ax) ts) : by rw quotient.sound con (H ts) ...
= (quotient alg con).eval (identity.rhs ax) (λ i, (quotient_hom con).map _ (ts i)) : by rw homomorphism.eval

theorem satisfies_exact (ax : identity sig) : 
(quotient alg con).satisfies ax → con.satisfies ax :=
λ H val, quotient.exact con $
calc (quotient_hom con).map _ (alg.eval ax.lhs val)
= (quotient alg con).eval ax.lhs (λ i, (quotient_hom con).map _ (val i)) : by rw homomorphism.eval ...
= (quotient alg con).eval ax.rhs (λ i, (quotient_hom con).map _ (val i)) : by rw H ...
= (quotient_hom con).map _ (alg.eval ax.rhs val) : by rw homomorphism.eval

end quotient

theorem quotient.satisfies (ax : identity sig) :
con.satisfies ax ↔ (quotient alg con).satisfies ax :=
⟨quotient.satisfies_sound ax, quotient.satisfies_exact ax⟩ 

end universal
