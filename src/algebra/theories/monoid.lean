-- Copyright © 2019 François G. Dorais. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.

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

@[signature_instance]
definition to_semigroup : semigroup_sig α :=
{ op := s.op
}

@[signature_instance]
definition to_unital : unital_sig α :=
{ op := s.op
, id := s.id
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

instance to_unital : unital s.to_unital := unital.infer _

end monoid

@[theory]
class cancel_monoid : Prop := intro ::
(associative : identity.op_associative s.op)
(left_identity : identity.op_left_identity s.op s.id)
(right_identity : identity.op_right_identity s.op s.id)
(left_cancellative : identity.op_left_cancellative s.op)
(right_cancellative : identity.op_right_cancellative s.op)

namespace cancel_monoid
variable [i : cancel_monoid s]
include i

instance to_monoid : monoid s := monoid.infer _

instance to_cancel_semigroup : cancel_semigroup s.to_semigroup := cancel_semigroup.infer _

instance to_cancel_unital : cancel_unital s.to_unital := cancel_unital.infer _

end cancel_monoid

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

@[theory]
class cancel_comm_monoid : Prop := intro ::
(associative : identity.op_associative s.op)
(commutative : identity.op_commutative s.op)
(right_identity : identity.op_right_identity s.op s.id)
(right_cancellative : identity.op_right_cancellative s.op)

namespace cancel_comm_monoid
variable [i : cancel_comm_monoid s]
include i

instance to_comm_monoid : comm_monoid s := comm_monoid.infer _

instance to_cancel_comm_semigroup : cancel_comm_semigroup s.to_semigroup := cancel_comm_semigroup.infer _

instance to_cancel_monoid : cancel_monoid s := cancel_monoid.infer _

instance to_cancel_comm_unital : cancel_comm_unital s.to_unital := cancel_comm_unital.infer _

end cancel_comm_monoid

@[theory]
class left_monoid_action {β : Type*} (t : left_action_sig α β) : Prop := intro ::
(left_compatible : identity.op_left_compatible t.act s.op)
(left_identity : identity.op_left_identity t.act s.id)

@[theory]
class right_monoid_action {β : Type*} (t : right_action_sig α β) : Prop := intro ::
(right_compatible : identity.op_right_compatible t.act s.op)
(right_identity : identity.op_right_identity t.act s.id)

end algebra
