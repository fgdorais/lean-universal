-- Copyright © 2019 François G. Dorais. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.

import .basic
import .monoid
import .group
import .action

namespace algebra

/- 
signature command cannot handle operation parameters, 
so we define category_sig manually; category_hom is missing.
-/
structure category_sig {α : Type*} (β : α → α → Type*) :=
(op (a b c : α) : β a b → β b c → β a c)
(id (a : α) : β a a)

namespace category_sig
variables {α : Type*} {β : α → α → Type*} (s : category_sig β)

@[signature_instance]
definition to_monoid (a : α) : monoid_sig (β a a) :=
{ op := s.op a a a
, id := s.id a
}

@[signature_instance]
definition to_left_action (a b : α) : left_action_sig (β a a) (β a b) :=
{ act := s.op a a b
}

@[signature_instance]
definition to_right_action (a b : α) : right_action_sig (β a a) (β b a) :=
{ act := s.op b a a
}

end category_sig

/- TODO: fix theory attribute to handle parameters correctly -/
class category {α : Type*} {β : α → α → Type*} (s : category_sig β) : Prop := intro ::
(assoc (a b c d) : identity.op_compatibility (s.op a c d) (s.op a b c) (s.op a b d) (s.op b c d))
(left_identity (a b) : identity.op_left_identity (s.op a a b) (s.id a))
(right_identity (a b) : identity.op_right_identity (s.op a b b) (s.id b))

attribute [identity_instance] category.assoc
attribute [identity_instance] category.left_identity
attribute [identity_instance] category.right_identity

namespace category
variables {α : Type*} {β : α → α → Type*} (s : category_sig β) [i : category s]

definition infer 
[Π (a b c d), class.op_compatibility (s.op a c d) (s.op a b c) (s.op a b d) (s.op b c d)]
[Π (a b), class.op_left_identity (s.op a a b) (s.id a)]
[Π (a b), class.op_right_identity (s.op a b b) (s.id b)] : category s :=
category.intro
(λ _ _ _ _, op_compatibility _ _ _ _)
(λ _ _, op_left_identity _ _)
(λ _ _, op_right_identity _ _)

include i

instance to_monoid (a : α) : monoid (s.to_monoid a) := monoid.infer _

instance to_left_monoid_action (a b : α) : left_monoid_action (s.to_monoid a) (s.to_left_action a b) := left_monoid_action.infer _ _

instance to_right_monoid_action (a b : α) : right_monoid_action (s.to_monoid a) (s.to_right_action a b) := right_monoid_action.infer _ _

end category

end algebra

/- move to monoid when ready -/
namespace algebra

namespace monoid_sig
variables {α : Type*} (s : monoid_sig α)

@[signature_instance]
definition to_category : category_sig (λ (_ _ : unit), α) :=
{ op := λ _ _ _, s.op
, id := λ _, s.id
}

end monoid_sig

namespace monoid
variables {α : Type*} (s : monoid_sig α) [monoid s]

@[identity_instance]
theorem to_category_compatibility (a b c d : unit) : identity.op_compatibility (s.to_category.op a c d) (s.to_category.op a b c) (s.to_category.op a b d) (s.to_category.op b c d) :=
show identity.op_compatibility s.op s.op s.op s.op, from op_associative s.op

@[identity_instance]
theorem to_category_left_identity (a b : unit) : identity.op_left_identity (s.to_category.op a a b) (s.to_category.id a) :=
show identity.op_left_identity s.op s.id, from op_left_identity s.op s.id

@[identity_instance]
theorem to_category_right_identity (a b : unit) : identity.op_right_identity (s.to_category.op a b b) (s.to_category.id b) :=
show identity.op_right_identity s.op s.id, from op_right_identity s.op s.id

instance to_category : category s.to_category := category.infer _

end monoid

end algebra