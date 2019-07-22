import .basic
import .action

namespace algebra

signature magma (α : Type*) :=
(op : α → α → α)

namespace magma_sig
variables {α : Type*} (s : magma_sig α)

definition to_left_action : left_action_sig α α :=
{ act := s.op
}

@[unify] definition to_left_action_hint (t : left_action_sig α α) : unification_hint :=
{ pattern := t.act =?= s.op
, constraints := [t =?= s.to_left_action]
}

definition to_right_action : right_action_sig α α :=
{ act := s.op
}

@[unify] definition to_right_action_hint (t : right_action_sig α α) : unification_hint :=
{ pattern := t.act =?= s.op
, constraints := [t =?= s.to_right_action]
}

end magma_sig

class magma {α} (s : magma_sig α) : Prop := intro ::

abbreviation magma.infer {α} (s : magma_sig α) : magma s := magma.intro _

@[theory]
class comm_magma {α} (s : magma_sig α) : Prop := intro ::
(commutative : identity.op_commutative s.op)

instance comm_magma.to_magma {α} (s : magma_sig α) [i : comm_magma s] : magma s := magma.infer _ 

end algebra
