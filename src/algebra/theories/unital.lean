-- Copyright © 2019 François G. Dorais. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.

import .basic
import .magma

namespace algebra

signature unital (α : Type*) :=
(op : α → α → α)
(id : α)

namespace unital_sig
variables {α : Type*} (s : unital_sig α)

@[signature_instance]
definition to_magma : magma_sig α :=
{ op := s.op
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
class cancel_unital : Prop := intro ::
(left_cancellative : identity.op_left_cancellative s.op)
(right_cancellative : identity.op_right_cancellative s.op)
(left_identity : identity.op_left_identity s.op s.id)
(right_identity : identity.op_right_identity s.op s.id)

namespace cancel_unital
variable [i : cancel_unital s]
include i

instance to_cancel_magma : cancel_magma s.to_magma := cancel_magma.infer _

end cancel_unital

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

@[theory]
class cancel_comm_unital : Prop := intro ::
(commutative : identity.op_commutative s.op)
(right_identity : identity.op_right_identity s.op s.id)
(right_cancellative : identity.op_right_cancellative s.op)

namespace cancel_comm_unital
variables [i : cancel_comm_unital s]
include i

instance to_comm_unital : comm_unital s := comm_unital.infer _

instance to_cancel_comm_magma : cancel_comm_magma s.to_magma := cancel_comm_magma.infer _

instance to_cancel_unital : cancel_unital s := cancel_unital.infer _

end cancel_comm_unital

end algebra
