import .basic
import .group

namespace algebra

signature action (α : Type*) (β : Type*) := 
(act : α → β → β)

class action {α : Type*} {β : Type*} (s : action_sig α β) : Prop := intro ::

abbreviation action.infer {α : Type*} {β : Type*} (s : action_sig α β) : action s := action.intro s

set_option old_structure_cmd true

@[theory]
class semigroup_action {α : Type*} {β : Type*} (act : action_sig α β) (s : semigroup_sig α) extends semigroup s : Prop := intro ::
(act_compat : identity.op_left_compatible act.act s.op)

@[theory]
class monoid_action {α : Type*} {β : Type*} (act : action_sig α β) (s : monoid_sig α) extends monoid s : Prop := intro ::
(act_compat : identity.op_left_compatible act.act s.op)
(act_left_identity : identity.op_left_identity act.act s.id)

@[theory]
class group_action {α : Type*} {β : Type*} (act : action_sig α β) (s : group_sig α) extends group s : Prop := intro ::
(act_compat : identity.op_left_compatible act.act s.op)
(act_left_identity : identity.op_left_identity act.act s.id)

end algebra