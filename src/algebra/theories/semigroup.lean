-- Copyright © 2019 François G. Dorais. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.

import .basic
import .magma

set_option default_priority 0

namespace algebra

signature semigroup (α : Type*) :=
(op : α → α → α)

namespace semigroup_sig

@[signature_instance]
definition to_magma {α} (s : semigroup_sig α) : magma_sig α :=
{ op := s.op
}

end semigroup_sig

variables {α : Type*} (s : semigroup_sig α)
local infix ∙ := s.op

@[theory]
class semigroup : Prop := intro ::
(associative : identity.op_associative s.op)

namespace semigroup
variable [i : semigroup s]
include i

instance to_magma : magma s.to_magma := magma.infer _

end semigroup

@[theory]
class comm_semigroup : Prop := intro ::
(associative : identity.op_associative s.op)
(commutative : identity.op_commutative s.op)

namespace comm_semigroup
variable [i : comm_semigroup s]
include i

instance to_semigroup : semigroup s := semigroup.infer _

instance to_comm_magma : comm_magma s.to_magma := comm_magma.infer _

@[identity_instance]
theorem left_commutative : identity.op_left_commutative s.op :=
λ x y z,
show x ∙ (y ∙ z) = y ∙ (x ∙ z),
from calc x ∙ (y ∙ z)
= (x ∙ y) ∙ z : by rw op_associative s.op ...
= (y ∙ x) ∙ z : by rw op_commutative s.op x y ...
= y ∙ (x ∙ z) : by rw op_associative s.op

@[identity_instance]
theorem right_commutative : identity.op_right_commutative s.op :=
λ x y z,
show (x ∙ y) ∙ z = (x ∙ z) ∙ y,
from calc (x ∙ y) ∙ z
= x ∙ (y ∙ z) : by rw op_associative s.op ...
= x ∙ (z ∙ y) : by rw op_commutative s.op y z ...
= (x ∙ z) ∙ y : by rw op_associative s.op

end comm_semigroup

@[theory]
class cancel_semigroup : Prop := intro ::
(associative : identity.op_associative s.op)
(left_cancellative : identity.op_left_cancellative s.op)
(right_cancellative : identity.op_right_cancellative s.op)

namespace cancel_semigroup
variable [i : cancel_semigroup s]
include i

instance to_semigroup : semigroup s := semigroup.infer _

instance to_cancel_magma : cancel_magma s.to_magma := cancel_magma.infer _

end cancel_semigroup

@[theory]
class cancel_comm_semigroup : Prop := intro ::
(associative : identity.op_associative s.op)
(commutative : identity.op_commutative s.op)
(right_cancellative : identity.op_right_cancellative s.op)

namespace cancel_comm_semigroup
variable [i : cancel_comm_semigroup s]
include i

instance to_comm_semigroup : comm_semigroup s := comm_semigroup.infer _

instance to_cancel_comm_magma : cancel_comm_magma s.to_magma := cancel_comm_magma.infer _

instance to_cancel_semigroup : cancel_semigroup s := cancel_semigroup.infer _

end cancel_comm_semigroup

end algebra
