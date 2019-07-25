import .basic
import .group 
import .monoid

set_option default_priority 0

namespace algebra

signature semiring (α : Type*) := 
(mul : α → α → α)
(one : α)
(add : α → α → α)
(zero : α)

namespace semiring_sig
variables {α : Type*} (s : semiring_sig α)

def to_add_monoid : monoid_sig α :=
{ op := s.add
, id := s.zero
}

@[unify] definition to_add_monoid_op_hint (t : monoid_sig α) : unification_hint :=
{ pattern := t.op =?= s.add
, constraints := [t =?= s.to_add_monoid]
}

@[unify] definition to_add_monoid_id_hint (t : monoid_sig α) : unification_hint :=
{ pattern := t.id =?= s.zero
, constraints := [t =?= s.to_add_monoid]
}

def to_mul_monoid : monoid_sig α :=
{ op := s.mul
, id := s.one
}

@[unify] definition to_mul_monoid_op_hint (t : monoid_sig α) : unification_hint :=
{ pattern := t.op =?= s.mul
, constraints := [t =?= s.to_mul_monoid]
}

@[unify] definition to_mul_monoid_id_hint (t : monoid_sig α) : unification_hint :=
{ pattern := t.id =?= s.one
, constraints := [t =?= s.to_mul_monoid]
}

end semiring_sig

variables {α : Type*} (s : semiring_sig α)
local notation `𝟘` := s.zero
local notation `𝟙` := s.one
local infix + := s.add
local infix ∙ := s.mul

@[theory]
class semiring : Prop := intro ::
(add_associative : identity.op_associative s.add)
(add_commutative : identity.op_commutative s.add)
(add_right_identity : identity.op_right_identity s.add s.zero)
(mul_associative : identity.op_associative s.mul)
(mul_left_identity : identity.op_left_identity s.mul s.one)
(mul_right_identity : identity.op_right_identity s.mul s.one)
(mul_left_distributive : identity.op_left_distributive s.mul s.add)
(mul_right_distributive : identity.op_right_distributive s.mul s.add)
(mul_left_null : identity.op_left_fixpoint s.mul s.zero)
(mul_right_null : identity.op_right_fixpoint s.mul s.zero)

namespace semiring
variable [i : semiring s]
include i

instance add_comm_monoid : comm_monoid s.to_add_monoid := comm_monoid.infer _

instance mul_monoid : monoid s.to_mul_monoid := monoid.infer _

end semiring

@[theory]
class comm_semiring : Prop := intro ::
(add_associative : identity.op_associative s.add)
(add_commutative : identity.op_commutative s.add)
(add_right_identity : identity.op_right_identity s.add s.zero)
(mul_associative : identity.op_associative s.mul)
(mul_commutative : identity.op_commutative s.mul)
(mul_right_identity : identity.op_right_identity s.mul s.one)
(mul_right_null : identity.op_right_fixpoint s.mul s.zero)
(mul_right_distributive : identity.op_right_distributive s.mul s.add)

namespace comm_semiring
variable [i : comm_semiring s]
include i

@[identity_instance]
theorem mul_left_identity : identity.op_left_identity s.mul s.one :=
λ x, calc 𝟙 ∙ x
= x ∙ 𝟙 : by rw op_commutative s.mul ...
= x : by rw op_right_identity s.mul

@[identity_instance]
theorem mul_left_null : identity.op_left_fixpoint s.mul s.zero :=
λ x, calc 𝟘 ∙ x
= x ∙ 𝟘 : by rw op_commutative s.mul ...
= 𝟘 : by rw op_right_fixpoint s.mul

@[identity_instance]
theorem mul_left_distributive : identity.op_left_distributive s.mul s.add :=
λ x y z, calc (x + y) ∙ z
= z ∙ (x + y) : by rw op_commutative s.mul ...
= z ∙ x + z ∙ y : by rw op_right_distributive s.mul s.add ...
= x ∙ z + z ∙ y : by rw op_commutative s.mul x ...
= x ∙ z + y ∙ z : by rw op_commutative s.mul y

instance to_semiring : semiring s := semiring.infer _

instance to_mul_monoid : comm_monoid s.to_mul_monoid := comm_monoid.infer _

end comm_semiring

end algebra