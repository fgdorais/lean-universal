-- Copyright © 2019 François G. Dorais. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.

import util

namespace universal

@[derive decidable_eq]
structure arity (τ : Type) := (cod : τ) (dom : list τ)

namespace arity
variables {τ : Type} (a b : arity τ)

protected theorem eq : ∀ {a b : arity τ}, a.cod = b.cod → a.dom = b.dom → a = b
| ⟨_,_⟩ ⟨_,_⟩ rfl rfl := rfl

theorem eq_iff : a.cod = b.cod ∧ a.dom = b.dom ↔ a = b :=
⟨λ ⟨hc, hd⟩, arity.eq hc hd, λ h, eq.subst h ⟨rfl, rfl⟩⟩

abbreviation index := index a.dom

abbreviation func (sort : τ → Type*) := (Π (i : a.index), sort i.val) → sort a.cod

end arity

definition signature (τ : Type) (σ : Type*) := σ → arity τ

universe u
variables {τ : Type} {σ : Type u} (sig : signature τ σ)

abbreviation signature.cod (f : σ) : τ := arity.cod (sig f)

abbreviation signature.dom (f : σ) : list τ := arity.dom (sig f)

abbreviation signature.index (f : σ) := arity.index (sig f)

inductive term (dom : list τ) : τ → Type u
| proj {} (i : index dom) : term i.val
| func (f : σ) : (Π (i : sig.index f), term i.val) → term (sig.cod f)

namespace term
variables {sig} {dom : list τ} {cod : τ} (t : term sig dom cod) 
include t

abbreviation arity : arity τ := ⟨cod, dom⟩

abbreviation dom : list τ := dom

abbreviation cod : τ := cod

abbreviation index : Type := index dom

end term

structure algebra :=
(sort : τ → Type*)
(func (f : σ) : arity.func (sig f) sort)

definition term_algebra (dom : list τ) : algebra sig :=
{ sort := term sig dom
, func := term.func
}

definition const_algebra : algebra sig := term_algebra sig []

namespace algebra
variables {sig} (alg : algebra sig) 

abbreviation valuation (dom : list τ) := Π (i : index dom), alg.sort i.val

definition eval {dom : list τ} : Π {cod : τ} (t : term sig dom cod), (Π (i : index dom), alg.sort i.val) → alg.sort cod
| _ (term.proj i) val := val i
| _ (term.func f ts) val := alg.func f (λ i, eval (ts i) val)

theorem eval_proj {dom : list τ} (i) (val : Π i : index dom, alg.sort i.val) : eval alg (term.proj i) val = val i := rfl

theorem eval_func {dom : list τ} (f) (ts) (val : Π i : index dom, alg.sort i.val) : eval alg (term.func f ts) val = alg.func f (λ i, eval alg (ts i) val) := rfl

end algebra

structure equation (dom : list τ) (cod : τ) := (lhs rhs : term sig dom cod)

namespace equation
variables {sig} {dom : list τ} {cod : τ}

abbreviation func (f) (es : Π (i : sig.index f), equation sig dom i.val) : equation sig dom (sig.cod f) :=
⟨term.func f (λ i, (es i).lhs), term.func f (λ i, (es i).rhs)⟩ 

end equation

definition equation_algebra (dom : list τ) : algebra sig :=
{ sort := equation sig dom
, func := equation.func
}

end universal
