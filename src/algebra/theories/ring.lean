-- Copyright © 2019 François G. Dorais. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.

import .basic
import .group 
import .monoid
import .semiring

set_option default_priority 0

namespace algebra

signature ring (α : Type*) := 
(mul : α → α → α)
(one : α)
(add : α → α → α)
(neg : α → α)
(zero : α)

namespace ring_sig
variables {α : Type*} (s : ring_sig α)

@[signature_instance]
def to_add_group : group_sig α :=
{ op := s.add
, inv := s.neg
, id := s.zero
}

@[signature_instance]
def to_mul_monoid : monoid_sig α :=
{ op := s.mul
, id := s.one
}

@[unify] 
definition to_mul_monoid_to_semigroup_op_hint (t : semigroup_sig α) : unification_hint :=
{ pattern := t.op =?= s.mul
, constraints := [t =?= s.to_mul_monoid.to_semigroup]
}

@[signature_instance]
definition to_semiring : semiring_sig α :=
{ add := s.add
, zero := s.zero
, mul := s.mul
, one := s.one
}

end ring_sig

variables {α : Type*} (s : ring_sig α)
local notation `𝟘` := s.zero
local notation `𝟙` := s.one
local prefix - := s.neg
local infix + := s.add
local infix ∙ := s.mul

@[theory]
class ring : Prop := intro ::
(add_associative : identity.op_associative s.add)
(add_right_identity : identity.op_right_identity s.add s.zero)
(add_right_inverse : identity.op_right_inverse s.add s.neg s.zero)
(mul_associative : identity.op_associative s.mul)
(mul_left_identity : identity.op_left_identity s.mul s.one)
(mul_right_identity : identity.op_right_identity s.mul s.one)
(mul_left_distributive : identity.op_left_distributive s.mul s.add)
(mul_right_distributive : identity.op_right_distributive s.mul s.add)

namespace ring
variable [i : ring s]
include i

instance to_add_group : group s.to_add_group := group.infer _

@[identity_instance]
theorem add_commutative : identity.op_commutative s.add :=
λ x y,
have (x + x) + (y + y) = (x + y) + (x + y),
from calc (x + x) + (y + y)
= (𝟙 ∙ x + 𝟙 ∙ x) + (y + y) : by rw op_left_identity s.mul s.one x ...
= (𝟙 ∙ x + 𝟙 ∙ x) + (𝟙 ∙ y + 𝟙 ∙ y) : by rw op_left_identity s.mul s.one y ...
= (𝟙 + 𝟙) ∙ x + (𝟙 ∙ y + 𝟙 ∙ y) : by rw op_left_distributive s.mul s.add _ _ x ... 
= (𝟙 + 𝟙) ∙ x + (𝟙 + 𝟙) ∙ y : by rw op_left_distributive s.mul s.add _ _ y ...
= (𝟙 + 𝟙) ∙ (x + y) : by rw op_right_distributive s.mul ...
= 𝟙 ∙ (x + y) + 𝟙 ∙ (x + y) : by rw op_left_distributive s.mul ...
= (x + y) + (x + y) : by rw op_left_identity s.mul s.one,
have x + ((x + y) + y) = x + ((y + x) + y),
from calc x + ((x + y) + y)
= x + (x + (y + y)) : by rw op_associative s.add ...
= (x + x) + (y + y) : by rw op_associative s.add ...
= (x + y) + (x + y) : by rw this ...
= x + (y + (x + y)) : by rw op_associative s.add ...
= x + ((y + x) + y) : by rw op_associative s.add,
have (x + y) + y = (y + x) + y,
from op_left_cancellative s.add this,
show x + y = y + x,
from op_right_cancellative s.add this

instance to_add_comm_group : comm_group s.to_add_group := comm_group.infer _

@[identity_instance]
theorem mul_left_null : identity.op_left_fixpoint s.mul s.zero :=
λ x, 
have x + 𝟘 ∙ x = x + 𝟘,
from calc x + 𝟘 ∙ x 
= 𝟙 ∙ x + 𝟘 ∙ x : by rw op_left_identity s.mul s.one ...
= (𝟙 + 𝟘) ∙ x : by rw op_left_distributive s.mul ...
= 𝟙 ∙ x : by rw op_right_identity s.add s.zero ...
= x : by rw op_left_identity s.mul s.one ...
= x + 𝟘 : by rw op_right_identity s.add s.zero,
show 𝟘 ∙ x = 𝟘, 
from op_left_cancellative s.add this

@[identity_instance]
theorem mul_right_null : identity.op_right_fixpoint s.mul s.zero :=
λ x, 
have x + x ∙ 𝟘 = x + 𝟘,
from calc x + x ∙ 𝟘 
= x ∙ 𝟙 + x ∙ 𝟘 : by rw op_right_identity s.mul s.one ...
= x ∙ (𝟙 + 𝟘) : by rw op_right_distributive s.mul ...
= x ∙ 𝟙 : by rw op_right_identity s.add s.zero ...
= x : by rw op_right_identity s.mul s.one ...
= x + 𝟘 : by rw op_right_identity s.add s.zero,
show x ∙ 𝟘 = 𝟘, 
from op_left_cancellative s.add this

instance to_semiring : semiring s.to_semiring := semiring.infer _

@[identity_instance]
theorem mul_neg_left_homomorphism : identity.op_left_fn_homomorphism s.mul s.neg s.neg :=
λ x y, 
have -x ∙ y + x ∙ y = -(x ∙ y) + x ∙ y,
from calc -x ∙ y + x ∙ y 
= (-x + x) ∙ y : by rw op_left_distributive s.mul ...
= 𝟘 ∙ y : by rw op_left_inverse s.add s.neg s.zero ...
= 𝟘 : by rw op_left_fixpoint s.mul ...
= -(x ∙ y) + x ∙ y : by rw op_left_inverse s.add s.neg s.zero,
show -x ∙ y = -(x ∙ y), 
from op_right_cancellative s.add this

@[identity_instance]
theorem mul_neg_right_homomorphism : identity.op_right_fn_homomorphism s.mul s.neg s.neg :=
λ x y, 
have x ∙ -y + x ∙ y = -(x ∙ y) + x ∙ y,
from calc x ∙ -y + x ∙ y 
= x ∙ (-y + y) : by rw op_right_distributive s.mul ...
= x ∙ 𝟘 : by rw op_left_inverse s.add s.neg s.zero ...
= 𝟘 : by rw op_right_fixpoint s.mul ...
= -(x ∙ y) + x ∙ y : by rw op_left_inverse s.add s.neg s.zero,
show x ∙ -y = -(x ∙ y), 
from op_right_cancellative s.add this

end ring

@[theory]
class comm_ring : Prop := intro ::
(add_associative : identity.op_associative s.add)
(add_right_identity : identity.op_right_identity s.add s.zero)
(add_right_inverse : identity.op_right_inverse s.add s.neg s.zero)
(mul_associative : identity.op_associative s.mul)
(mul_commutative : identity.op_commutative s.mul)
(mul_right_identity : identity.op_right_identity s.mul s.one)
(mul_right_distributive : identity.op_right_distributive s.mul s.add)

namespace comm_ring
variables [i : comm_ring s]
include i

@[identity_instance]
theorem mul_left_distributive : identity.op_left_distributive s.mul s.add :=
λ x y z,
show (x + y) ∙ z = x ∙ z + y ∙ z, 
from calc (x + y) ∙ z 
= z ∙ (x + y) : by rw op_commutative s.mul ...
= z ∙ x + z ∙ y : by rw op_right_distributive s.mul ...
= x ∙ z + z ∙ y : by rw op_commutative s.mul x ...
= x ∙ z + y ∙ z : by rw op_commutative s.mul y

instance to_mul_comm_monoid : comm_monoid s.to_mul_monoid := comm_monoid.infer _

instance to_ring : ring s := ring.infer _

instance to_comm_semiring : comm_semiring s.to_semiring := comm_semiring.infer _

end comm_ring

end algebra
