import .basic
import .quasigroup

set_option default_priority 0

namespace algebra

signature loop (α : Type*) :=
(op : α → α → α)
(ldiv : α → α → α)
(rdiv : α → α → α)
(id : α)

namespace loop_sig
variables {α : Type*} (s : loop_sig α)

abbreviation linv (x : α) : α := s.rdiv s.id x -- (λ x, e / x)

abbreviation rinv (x : α) : α := s.ldiv x s.id -- (λ x, x \ e)

definition to_quasigroup : quasigroup_sig α :=
{ op := s.op
, ldiv := s.ldiv
, rdiv := s.rdiv
}

@[unify] definition to_quasigroup_op_hint (t : quasigroup_sig α) : unification_hint :=
{ pattern := t.op =?= s.op
, constraints := [t =?= s.to_quasigroup]
}

@[unify] definition to_quasigroup_ldiv_hint (t : quasigroup_sig α) : unification_hint :=
{ pattern := t.ldiv =?= s.ldiv
, constraints := [t =?= s.to_quasigroup]
}

@[unify] definition to_quasigroup_rdiv_hint (t : quasigroup_sig α) : unification_hint :=
{ pattern := t.rdiv =?= s.rdiv
, constraints := [t =?= s.to_quasigroup]
}

end loop_sig

variables {α : Type*} (s : loop_sig α)
local infix ∙ := s.op
local infix \ := s.ldiv
local infix / := s.rdiv
local notation `e` := s.id

@[theory]
class loop : Prop := intro ::
(left_identity : identity.op_left_identity s.op s.id)
(right_identity : identity.op_right_identity s.op s.id)
(left_cancel : identity.op_left_cancellative s.op)
(right_cancel : identity.op_right_cancellative s.op)
(left_division : identity.op_left_division s.op s.ldiv)
(right_division : identity.op_right_division s.op s.rdiv)

namespace loop
variable [i : loop s]
include i

@[identity_instance]
theorem left_inverse : identity.op_left_inverse s.op s.linv s.id :=
λ x, op_right_division s.op s.rdiv x e

@[identity_instance]
theorem right_inverse : identity.op_right_inverse s.op s.rinv s.id :=
λ x, op_left_division s.op s.ldiv x e

instance to_quasigroup : quasigroup s.to_quasigroup := quasigroup.infer _

end loop

end algebra
