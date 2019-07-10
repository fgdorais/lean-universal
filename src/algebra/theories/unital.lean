import .basic
import .magma

namespace algebra

signature unital (α : Type*) :=
(op : α → α → α)
(id : α)

namespace unital_sig
variables {α : Type*} (s : unital_sig α)

definition to_magma : magma_sig α :=
{ op := s.op
}

@[unify] definition to_magma_op_hint (t : magma_sig α) : unification_hint :=
{ pattern := t.op =?= s.op
, constraints := [t =?= s.to_magma]
}

end unital_sig

variables {α : Type*} (s : unital_sig α)
local infix ∙ := s.op
local notation `e` := s.id

@[theory]
class unital : Prop := intro ::
(left_identity : identity.op_left_identity s.op s.id)
(right_identity : identity.op_right_identity s.op s.id)

namespace unital
variable [i : unital s]
include i

instance to_magma : magma s.to_magma := magma.infer _

end unital

@[theory]
class comm_unital : Prop := intro ::
(commutative : identity.op_commutative s.op)
(right_identity : identity.op_right_identity s.op s.id)

namespace comm_unital
variable [i : comm_unital s]
include i

@[identity_instance]
theorem left_identity : identity.op_left_identity s.op s.id :=
λ x, show e ∙ x = x, from calc _
= x ∙ e : by rw op_commutative s.op ...
= x : by rw op_right_identity s.op

instance to_unital : unital s := unital.infer _

instance to_comm_magma : comm_magma s.to_magma := comm_magma.infer _

end comm_unital

end algebra
