-- Copyright © 2019 François G. Dorais. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.

import .basic
import .magma

set_option default_priority 0

namespace algebra

signature quasigroup (α : Type*) := 
(op : α → α → α)
(ldiv : α → α → α)
(rdiv : α → α → α)

namespace quasigroup_sig 
variables {α : Type*} (s : quasigroup_sig α)

@[signature_instance]
definition to_magma : magma_sig α :=
{ op := s.op
}

end quasigroup_sig

variables {α : Type*} (s : quasigroup_sig α)
local infix ∙ := s.op
local infix \ := s.ldiv
local infix / := s.rdiv

@[theory]
class quasigroup : Prop := intro ::
(left_cancel : identity.op_left_cancellative s.op)
(right_cancel : identity.op_right_cancellative s.op)
(left_division : identity.op_left_division s.op s.ldiv)
(right_division : identity.op_right_division s.op s.rdiv)

namespace quasigroup
variable [i : quasigroup s]
include i

instance to_cancel_magma : cancel_magma s.to_magma := cancel_magma.infer _

theorem unique_left_division (x y z : α) : x ∙ y = z ↔ y = x \ z :=
⟨ assume h : x ∙ y = z,
  have x ∙ y = x ∙ (x \ z), from calc
  x ∙ y
  = z : by rw h ...
  = x ∙ (x \ z) : by rw op_left_division s.op,
  op_left_cancellative s.op this
, assume h : y = x \ z,
  eq.substr h $ op_left_division s.op s.ldiv x z
⟩

theorem unique_right_division (x y z : α) : x ∙ y = z ↔ x = z / y :=
⟨ assume h : x ∙ y = z,
  have x ∙ y = (z / y) ∙ y, from calc
  x ∙ y
  = z : by rw h ...
  = (z / y) ∙ y : by rw op_right_division s.op,
  op_right_cancellative s.op this
, assume h : x = z / y,
  eq.substr h $ op_right_division s.op s.rdiv y z
⟩

end quasigroup

end algebra
