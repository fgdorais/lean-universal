-- Copyright © 2019 François G. Dorais. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.

import .basic
import .identity
import .congruence

namespace universal
variables {τ : Type} {σ : Type} {sig : signature τ σ}

definition valid {ι : Type} (ax : ι → identity sig) {dom : list τ} {{cod}} : term sig dom cod → term sig dom cod → Prop :=
λ t₁ t₂, ∀ (alg : algebra.{0} sig), (∀ i, alg.satisfies (ax i)) → (∀ (val : Π (i : index dom), alg.sort i.val), alg.eval t₁ val = alg.eval t₂ val)

namespace valid
variables {ι : Type} {ax : ι → identity sig} {dom : list τ}

theorem refl {{cod}} (t : term sig dom cod) : valid ax t t := λ _ _ _, rfl

theorem rfl {cod} {t : term sig dom cod} : valid ax t t := refl t

theorem ax (i) (sub : substitution sig (ax i).dom dom) :
valid ax (sub.apply (ax i).lhs) (sub.apply (ax i).rhs) :=
begin
intros alg h val,
rw sub.eval,
rw sub.eval,
apply h,
end

theorem app (f : σ) {ts us : Π (i : sig.index f), term sig dom i.val} :
(∀ (i : sig.index f), valid ax (ts i) (us i)) → valid ax (term.func f ts) (term.func f us) :=
begin
intros hs alg h val,
rw alg.eval_func,
rw alg.eval_func,
congr,
funext i,
apply hs i alg,
exact h,
end

theorem symm {{cod}} {{x y : term sig dom cod}} : valid ax x y → valid ax y x :=
λ hxy alg h val, eq.symm $ hxy alg h val

theorem trans {{cod}} {{x y z : term sig dom cod}} : valid ax x y → valid ax y z → valid ax x z :=
λ hxy hyz alg h val, eq.trans (hxy alg h val) (hyz alg h val)

theorem eucl {{cod}} {{x y z : term sig dom cod}} : valid ax x y → valid ax x z → valid ax y z :=
λ hxy hxz, trans hxy.symm hxz

variables (sig dom ax)

definition to_congruence : congruence (term_algebra sig dom) :=
{ r := valid ax
, refl := valid.refl
, eucl := valid.eucl
, func := valid.app
}

end valid

definition models {ι : Type} (ax : ι → identity sig) (e : identity sig) : Prop := valid ax e.lhs e.rhs

theorem models.elim {ι : Type} {ax : ι → identity sig} {e : identity sig} : 
models ax e → ∀ (alg : algebra sig), (∀ i, alg.satisfies (ax i)) → alg.satisfies e :=
λ Hm alg Ha val,
let h := alg.eval_hom val in
let img := homomorphism.image h in
let ival : Π (i : index e.dom), img.sort i.val := λ i, quotient.mk h.kernel (term.proj i) in
have hival : h.image_map = img.eval_hom ival,
begin
apply homomorphism.ext,
introv,
induction x with _ f ts IH,
reflexivity,
have : term.func f ts = (term_algebra sig e.dom).func f ts, from rfl,
rw this,
rw ← homomorphism.func,
rw ← homomorphism.func,
congr,
funext,
exact IH i,
end,
have Ia : ∀ i, img.satisfies (ax i),
begin
intro i,
apply algebra.satisfies_of_injective_hom (homomorphism.image_inc (alg.eval_hom val)),
exact Ha i,
end,
calc h.map e.cod e.lhs
= (homomorphism.comp h.image_inc h.image_map).map e.cod e.lhs : by rw h.image_factorization ...
= h.image_inc.map e.cod (h.image_map.map e.cod e.lhs) : rfl ...
= h.image_inc.map e.cod ((img.eval_hom ival).map e.cod e.lhs) : by rw hival ...
= h.image_inc.map e.cod (algebra.eval _ e.lhs ival) : rfl ...
= h.image_inc.map e.cod (algebra.eval _ e.rhs ival) : by rw Hm img Ia ival ...
= h.image_inc.map e.cod ((img.eval_hom ival).map e.cod e.rhs) : rfl ...
= h.image_inc.map e.cod (h.image_map.map e.cod e.rhs) : by rw hival ...
= (homomorphism.comp h.image_inc h.image_map).map e.cod e.rhs : rfl ...
= h.map e.cod e.rhs : by rw h.image_factorization

end universal
