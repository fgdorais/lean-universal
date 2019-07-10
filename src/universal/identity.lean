-- Copyright © 2019 François G. Dorais. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.

import .basic
import .substitution
import .homomorphism

namespace universal
variables {τ : Type} {σ : Type} (sig : signature τ σ)

structure identity :=
(cod : τ)
(dom : list τ)
(eqn : equation sig dom cod)

variable {sig}

definition equation.to_identity {dom} {{cod}} : equation sig dom cod → identity sig :=
λ e, ⟨_, _, e⟩

definition term.to_identity {dom} {{cod}} : term sig dom cod → term sig dom cod → identity sig :=
λ x₁ x₂, ⟨_, _, ⟨x₁, x₂⟩⟩

namespace identity
variables {sig} (ax : identity sig)

abbreviation lhs : term sig ax.dom ax.cod := ax.eqn.lhs

abbreviation rhs : term sig ax.dom ax.cod := ax.eqn.rhs

abbreviation subst {dom : list τ} (sub : substitution sig ax.dom dom) : identity sig :=
{ cod := ax.cod
, dom := dom
, eqn := ax.eqn.subst sub
}

theorem subst_lhs {dom : list τ} (sub : substitution sig ax.dom dom) :
(ax.subst sub).lhs = ax.lhs.subst sub := rfl

theorem subst_rhs {dom : list τ} (sub : substitution sig ax.dom dom) :
(ax.subst sub).rhs = ax.rhs.subst sub := rfl

end identity

namespace algebra
variables (alg : algebra sig) {alg₁ : algebra sig} {alg₂ : algebra sig} (h : homomorphism alg₁ alg₂)

definition satisfies (ax : identity sig) : Prop :=
∀ (val : Π (i : index ax.dom), alg.sort i.val), alg.eval ax.lhs val = alg.eval ax.rhs val

theorem satisfies_of_injective_hom [homomorphism.injective h] (ax : identity sig) : 
alg₂.satisfies ax → alg₁.satisfies ax :=
begin
intros H₂ val₁,
apply homomorphism.injective.elim h,
rw h.eval,
rw h.eval,
apply H₂,
end 

theorem satisfies_of_surjective_hom [homomorphism.surjective h] (ax : identity sig) : 
alg₁.satisfies ax → alg₂.satisfies ax :=
begin
intros H₁ val₂,
have : nonempty (Π (i : index ax.dom), { x : alg₁.sort i.val // h.map i.val x = val₂ i}),
begin
apply index.choice,
intro i,
cases homomorphism.surjective.elim h i.val (val₂ i) with x hx,
exact nonempty.intro ⟨x, hx⟩,
end,
cases this with pval₁,
let val₁ := λ i, (pval₁ i).val,
have : val₂ = (λ i, h.map _ (val₁ i)), from funext (λ i, eq.symm (pval₁ i).property),
rw this,
rw ← h.eval,
rw ← h.eval,
apply congr_arg,
apply H₁,
end

end algebra

end universal
