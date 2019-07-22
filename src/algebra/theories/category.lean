import .basic
import .monoid
import .group

namespace algebra

/- 
signature command cannot handle operation parameters yet, 
so we define category_sig manually; category_hom is missing.
-/
structure category_sig {α : Type*} (β : α → α → Type*) :=
(op (a b c : α) : β a b → β b c → β a c)
(id (a : α) : β a a)

namespace category_sig
variables {α : Type*} {β : α → α → Type*} (s : category_sig β)

@[reducible]
definition to_monoid (a : α) : monoid_sig (β a a) :=
{ op := s.op a a a
, id := s.id a
}

@[unify] definition to_monoid_op_hint (a : α) (t : monoid_sig (β a a)) : unification_hint :=
{ pattern := t.op =?= s.op a a a
, constraints := [t =?= s.to_monoid a]
}

@[unify] definition to_monoid_id_hint (a : α) (t : monoid_sig (β a a)) : unification_hint :=
{ pattern := t.id =?= s.id a
, constraints := [t =?= s.to_monoid a]
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

/- monoid.infer can't infer op_associative from op_compatibility -/
@[identity_instance]
theorem to_monoid_assoc (a : α) : identity.op_associative (s.to_monoid a).op :=
op_compatibility _ _ _ _

instance to_monoid (a : α) : monoid (s.to_monoid a) := monoid.infer _

end category

end algebra

/- move to monoid when ready -/
namespace algebra

namespace monoid_sig
variables {α : Type*} (s : monoid_sig α)

definition to_category : category_sig (λ (_ _ : unit), α) :=
{ op := λ _ _ _, s.op
, id := λ _, s.id
}

@[unify] definition to_category_op_hint (t : category_sig (λ (_ _ : unit), α)) (a b c : unit) : unification_hint :=
{ pattern := t.op a b c =?= s.op
, constraints := [t =?= s.to_category]
}

@[unify] definition to_category_id_hint (t : category_sig (λ (_ _ : unit), α)) (a : unit) : unification_hint :=
{ pattern := t.id a =?= s.id
, constraints := [t =?= s.to_category]
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