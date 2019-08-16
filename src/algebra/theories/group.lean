-- Copyright © 2019 François G. Dorais. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.

import .basic
import .monoid
import .loop

set_option default_priority 0

namespace algebra

signature group (α : Type*) :=
(op : α → α → α)
(inv : α → α)
(id : α)

namespace group_sig
variables {α : Type*} (s : group_sig α)

abbreviation ldiv (x y : α) := s.op (s.inv x) y -- (λ x y, x⁻¹ ∙ y)

abbreviation rdiv (x y : α) := s.op x (s.inv y) -- (λ x y, x ∙ y⁻¹)

@[signature_instance]
definition to_monoid : monoid_sig α :=
{ op := s.op
, id := s.id
}

@[signature_instance]
definition to_loop : loop_sig α :=
{ op := s.op
, ldiv := s.ldiv
, rdiv := s.rdiv
, id := s.id
}

end group_sig

variables {α : Type*} (s : group_sig α)
local infix ∙ := s.op
local postfix ⁻¹ := s.inv
local notation `e` := s.id

@[theory]
class group : Prop := intro ::
(associative : identity.op_associative s.op)
(right_identity : identity.op_right_identity s.op s.id)
(right_inverse : identity.op_right_inverse s.op s.inv s.id)

namespace group
variable [i : group s]
include i

@[identity_instance]
theorem right_cancellative : identity.op_right_cancellative s.op :=
λ x y z,
assume h : x ∙ y = z ∙ y,
show x = z,
from calc x
= x ∙ e : by rw op_right_identity s.op ...
= x ∙ (y ∙ y⁻¹) : by rw op_right_inverse s.op s.inv ...
= (x ∙ y) ∙ y⁻¹ : by rw op_associative s.op ...
= (z ∙ y) ∙ y⁻¹ : by rw h ...
= z ∙ (y ∙ y⁻¹) : by rw op_associative s.op ...
= z ∙ e : by rw op_right_inverse s.op s.inv ...
= z : by rw op_right_identity s.op

@[identity_instance]
theorem left_identity : identity.op_left_identity s.op s.id :=
λ x, 
have (e ∙ x) ∙ x⁻¹ = x ∙ x⁻¹, 
from calc (e ∙ x) ∙ x⁻¹ 
= e ∙ (x ∙ x⁻¹) : by rw op_associative s.op ...
= e ∙ e : by rw op_right_inverse s.op ...
= e : by rw op_right_identity s.op ...
= x ∙ x⁻¹ : by rw op_right_inverse s.op,
op_right_cancellative s.op this

@[identity_instance]
theorem left_inverse : identity.op_left_inverse s.op s.inv s.id :=
λ x,
have (x⁻¹ ∙ x) ∙ x⁻¹ = e ∙ x⁻¹, 
from calc (x⁻¹ ∙ x) ∙ x⁻¹ 
= x⁻¹ ∙ (x ∙ x⁻¹) : by rw op_associative s.op ...
= x⁻¹ ∙ e : by rw op_right_inverse s.op s.inv ...
= x⁻¹ : by rw op_right_identity s.op ...
= e ∙ x⁻¹ : by rw op_left_identity s.op,
op_right_cancellative s.op this

@[identity_instance]
theorem left_cancellative : identity.op_left_cancellative s.op :=
λ x y z,
assume h : x ∙ y = x ∙ z,
show y = z, 
from calc y
= e ∙ y : by rw op_left_identity s.op ...
= (x⁻¹ ∙ x) ∙ y : by rw op_left_inverse s.op ...
= x⁻¹ ∙ (x ∙ y) : by rw op_associative s.op ...
= x⁻¹ ∙ (x ∙ z) : by rw h ...
= (x⁻¹ ∙ x) ∙ z : by rw op_associative s.op ...
= e ∙ z : by rw op_left_inverse s.op ...
= z : by rw op_left_identity s.op

@[identity_instance]
theorem inv_fixpoint : identity.fn_fixpoint s.inv s.id :=
show e⁻¹ = e, 
from calc e⁻¹
= e⁻¹ ∙ e : by rw op_right_identity s.op ...
= e : by rw op_left_inverse s.op

@[identity_instance]
theorem inv_involutive : identity.fn_involutive s.inv :=
λ x, 
have x⁻¹⁻¹ ∙ x⁻¹ = x ∙ x⁻¹,
from calc x⁻¹⁻¹ ∙ x⁻¹
= e : by rw op_left_inverse s.op ...
= x ∙ x⁻¹ : by rw op_right_inverse s.op,
op_right_cancellative s.op this

@[identity_instance]
theorem inv_antimorphism : identity.fn_op_antimorphism s.inv s.op s.op :=
λ x y, 
have (x ∙ y)⁻¹ ∙ (x ∙ y) = (y⁻¹ ∙ x⁻¹) ∙ (x ∙ y), 
from calc (x ∙ y)⁻¹ ∙ (x ∙ y) 
= e : by rw op_left_inverse s.op ...
= y⁻¹ ∙ y : by rw op_left_inverse s.op ...
= (y⁻¹ ∙ e) ∙ y : by rw op_right_identity s.op s.id ...
= (y⁻¹ ∙ (x⁻¹ ∙ x)) ∙ y : by rw op_left_inverse s.op ...
= ((y⁻¹ ∙ x⁻¹) ∙ x) ∙ y : by rw op_associative s.op y⁻¹ x⁻¹ x ...
= (y⁻¹ ∙ x⁻¹) ∙ (x ∙ y) : by rw op_associative s.op,
op_right_cancellative s.op this

@[identity_instance]
theorem left_division : identity.op_left_division s.op s.ldiv :=
λ x y,
show x ∙ (x⁻¹ ∙ y) = y,
from calc x ∙ (x⁻¹ ∙ y)
= (x ∙ x⁻¹) ∙ y : by rw op_associative s.op ...
= e ∙ y : by rw op_right_inverse s.op ...
= y : by rw op_left_identity s.op

@[identity_instance]
theorem right_division : identity.op_right_division s.op s.rdiv :=
λ x y, 
show (y ∙ x⁻¹) ∙ x = y,
from calc (y ∙ x⁻¹) ∙ x
= y ∙ (x⁻¹ ∙ x) : by rw op_associative s.op ...
= y ∙ e : by rw op_left_inverse s.op ...
= y : by rw op_right_identity s.op

instance to_monoid : monoid s.to_monoid := monoid.infer _
instance to_loop : loop s.to_loop := loop.infer _

end group

@[theory]
class comm_group : Prop := intro ::
(associative : identity.op_associative s.op)
(commutative : identity.op_commutative s.op)
(right_identity : identity.op_right_identity s.op s.id)
(right_inverse : identity.op_right_inverse s.op s.inv s.id)

namespace comm_group
variable [i : comm_group s]
include i

instance to_group : group s := group.infer _

@[identity_instance]
theorem inv_homomorphism : identity.fn_op_homomorphism s.inv s.op s.op :=
λ x y, show (x ∙ y)⁻¹ = x⁻¹ ∙ y⁻¹,
from calc (x ∙ y)⁻¹
= (y ∙ x)⁻¹ : by rw op_commutative s.op ...
= x⁻¹ ∙ y⁻¹ : by rw fn_op_antimorphism s.inv s.op s.op

instance to_comm_monoid : comm_monoid s.to_monoid := comm_monoid.infer _

end comm_group

end algebra
