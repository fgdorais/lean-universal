-- Copyright © 2019 François G. Dorais. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.

import .basic
import .action

namespace algebra

signature magma (α : Type*) :=
(op : α → α → α)

namespace magma_sig
variables {α : Type*} (s : magma_sig α)

@[signature_instance]
definition to_left_action : left_action_sig α α :=
{ act := s.op
}

@[signature_instance]
definition to_right_action : right_action_sig α α :=
{ act := s.op
}

end magma_sig

class magma {α} (s : magma_sig α) : Prop := intro ::

abbreviation magma.infer {α} (s : magma_sig α) : magma s := magma.intro _

@[theory]
class cancel_magma {α} (s : magma_sig α) : Prop := intro ::
(left_cancellative : identity.op_left_cancellative s.op)
(right_cancellative : identity.op_right_cancellative s.op)

instance cancel_magma.to_magma {α} (s : magma_sig α) [i : cancel_magma s] : magma s := magma.infer _ 

@[theory]
class comm_magma {α} (s : magma_sig α) : Prop := intro ::
(commutative : identity.op_commutative s.op)

instance comm_magma.to_magma {α} (s : magma_sig α) [i : comm_magma s] : magma s := magma.infer _ 

@[theory]
class cancel_comm_magma {α} (s : magma_sig α) : Prop := intro ::
(commutative : identity.op_commutative s.op)
(right_cancellative : identity.op_right_cancellative s.op)

instance cancel_comm_magma.to_comm_magma {α} (s : magma_sig α) [i : cancel_comm_magma s] : comm_magma s := comm_magma.infer _

@[identity_instance]
theorem cancel_comm_magma.left_cancellative {α} (s : magma_sig α) [i : cancel_comm_magma s] :
identity.op_left_cancellative s.op :=
λ x y z h, have s.op y x = s.op z x, 
from calc s.op y x
= s.op x y : by rw op_commutative s.op ...
= s.op x z : by rw h ...
= s.op z x : by rw op_commutative s.op,
op_right_cancellative s.op this

instance cancel_comm_magma.to_cancel_magma {α} (s : magma_sig α) [i : cancel_comm_magma s] : cancel_magma s := cancel_magma.infer _

end algebra
