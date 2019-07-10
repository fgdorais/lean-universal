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

definition to_magma : magma_sig α :=
{ op := s.op
}

@[unify] definition to_magma_op_hint (t : magma_sig α) : unification_hint :=
{ pattern := t.op =?= s.op
, constraints := [t =?= s.to_magma]
}

end quasigroup_sig

variables {α : Type*} (s : quasigroup_sig α)
local infix ∙ := s.op
local infix \ := s.ldiv
local infix / := s.rdiv

@[theory]
class quasigroup : Prop := intro ::
(left_cancel : identity.op_left_cancellative s.op)
(left_division : identity.op_left_division s.op s.ldiv)
(right_cancel : identity.op_right_cancellative s.op)
(right_division : identity.op_right_division s.op s.rdiv)

namespace quasigroup
variable [i : quasigroup s]
include i

theorem unique_left_division (x y z : α) : x ∙ y = z ↔ y = x \ z :=
iff.intro
( assume h : x ∙ y = z,
  have x ∙ y = x ∙ (x \ z), from calc
  x ∙ y
  = z : by rw h ...
  = x ∙ (x \ z) : by rw op_left_division s.op,
  op_left_cancellative s.op this
)
( assume h : y = x \ z,
  eq.substr h $ op_left_division s.op s.ldiv x z
)

theorem unique_right_division (x y z : α) : x ∙ y = z ↔ x = z / y :=
iff.intro
( assume h : x ∙ y = z,
  have x ∙ y = (z / y) ∙ y, from calc
  x ∙ y
  = z : by rw h ...
  = (z / y) ∙ y : by rw op_right_division s.op,
  op_right_cancellative s.op this
)
( assume h : x = z / y,
  eq.substr h $ op_right_division s.op s.rdiv y z
)

end quasigroup

end algebra
