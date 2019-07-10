import .basic
import .semigroup
import .unital

set_option default_priority 0

namespace algebra

signature monoid (α : Type*) :=
(op : α → α → α)
(id : α)

namespace monoid_sig
variables {α : Type*} (s : monoid_sig α)

definition to_semigroup : semigroup_sig α :=
{ op := s.op
}

@[unify] definition to_semigroup_op_hint (t : semigroup_sig α) : unification_hint :=
{ pattern := t.op =?= s.op
, constraints := [t =?= s.to_semigroup]
}

definition to_unital : unital_sig α :=
{ op := s.op
, id := s.id
}

@[unify] definition to_unital_op_hint (t : unital_sig α) : unification_hint :=
{ pattern := t.op =?= s.op
, constraints := [t =?= s.to_unital]
}

@[unify] definition to_unital_id_hint (t : unital_sig α) : unification_hint :=
{ pattern := t.id =?= s.id
, constraints := [t =?= s.to_unital]
}

end monoid_sig

variables {α : Type*} (s : monoid_sig α)

local infix ∙ := s.op
local notation `e` := s.id

@[theory]
class monoid : Prop := intro ::
(associative : identity.op_associative s.op)
(left_identity : identity.op_left_identity s.op s.id)
(right_identity : identity.op_right_identity s.op s.id)

namespace monoid
variable [i : monoid s]
include i

instance to_semigroup : semigroup s.to_semigroup := semigroup.infer _

end monoid

@[theory]
class comm_monoid : Prop := intro ::
(associative : identity.op_associative s.op)
(commutative : identity.op_commutative s.op)
(right_identity : identity.op_right_identity s.op s.id)

namespace comm_monoid
variables [i : comm_monoid s]
include i

@[identity_instance]
theorem left_identity : identity.op_left_identity s.op s.id :=
λ x, show e ∙ x = x, from calc _
= x ∙ e : by rw op_commutative s.op ...
= x : by rw op_right_identity s.op

instance to_monoid : monoid s := monoid.infer _

instance to_comm_semigroup : comm_semigroup s.to_semigroup := comm_semigroup.infer _

instance to_comm_unital : comm_unital s.to_unital := comm_unital.infer _

end comm_monoid

end algebra
