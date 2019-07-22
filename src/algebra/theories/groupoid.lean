import .basic
import .category
import .group

namespace algebra

/- 
signature command cannot handle operation parameters yet, 
so we define groupoid_sig manually; groupoid_hom is missing.
-/
structure groupoid_sig {α : Type*} (β : α → α → Type*) :=
(op (a b c : α) : β a b → β b c → β a c)
(id (a : α) : β a a)
(inv (a b : α) : β a b → β b a)

namespace groupoid_sig
variables {α : Type*} {β : α → α → Type*} (s : groupoid_sig β)

definition to_category : category_sig β :=
{ op := s.op
, id := s.id
}

@[unify] definition to_category_op_hint (t : category_sig β) (a b c : α) : unification_hint :=
{ pattern := t.op a b c =?= s.op a b c
, constraints := [t =?= s.to_category]
}

@[unify] definition to_category_id_hint (t : category_sig β) (a) : unification_hint :=
{ pattern := t.id a =?= s.id a
, constraints := [t =?= s.to_category]
}

definition to_group (a : α) : group_sig (β a a) :=
{ op := s.op a a a
, inv := s.inv a a
, id := s.id a
}

@[unify] definition to_group_op_hint (a : α) (t : group_sig (β a a)) : unification_hint :=
{ pattern := t.op =?= s.op a a a
, constraints := [t =?= s.to_group a]
}

@[unify] definition to_group_inv_hint (a : α) (t : group_sig (β a a)) : unification_hint :=
{ pattern := t.inv =?= s.inv a a
, constraints := [t =?= s.to_group a]
}

@[unify] definition to_group_id_hint (a : α) (t : group_sig (β a a)) : unification_hint :=
{ pattern := t.id =?= s.id a
, constraints := [t =?= s.to_group a]
}

end groupoid_sig

class groupoid {α : Type*} {β : α → α → Type*} (s : groupoid_sig β) : Prop := intro ::
(assoc (a b c d) : identity.op_compatibility (s.op a c d) (s.op a b c) (s.op a b d) (s.op b c d))
(right_identity (a b) : identity.op_right_identity (s.op a b b) (s.id b))
(right_inverse (a b) : identity.op_right_inverse (s.op a b a) (s.inv a b) (s.id a))

attribute [identity_instance] groupoid.assoc
attribute [identity_instance] groupoid.right_identity
attribute [identity_instance] groupoid.right_inverse

namespace groupoid
variables {α : Type*} {β : α → α → Type*} (s : groupoid_sig β) [i : groupoid s]

definition infer
[Π (a b c d), class.op_compatibility (s.op a c d) (s.op a b c) (s.op a b d) (s.op b c d)]
[Π (a b), class.op_right_identity (s.op a b b) (s.id b)]
[Π (a b), class.op_right_inverse (s.op a b a) (s.inv a b) (s.id a)]
: groupoid s :=
groupoid.intro 
  (λ _ _ _ _, op_compatibility _ _ _ _) 
  (λ _ _, op_right_identity _ _) 
  (λ _ _, op_right_inverse _ _ _)

include i
local infix ∙ := s.op _ _ _
local postfix ⁻¹ := s.inv _ _
local notation `e` := s.id _

@[identity_instance]
theorem right_cancellative (a b c) : identity.op_right_cancellative (s.op a b c) :=
λ x y z,
assume h : x ∙ y = z ∙ y,
show x = z,
from calc x
= x ∙ e : by rw op_right_identity (s.op _ _ _) ...
= x ∙ (y ∙ y⁻¹) : by rw op_right_inverse (s.op _ _ _) (s.inv _ _) ...
= (x ∙ y) ∙ y⁻¹ : by rw op_compatibility (s.op a c b) (s.op a b c) (s.op a b b) (s.op b c b) ...
= (z ∙ y) ∙ y⁻¹ : by rw h ...
= z ∙ (y ∙ y⁻¹) : by rw op_compatibility (s.op a c b) (s.op a b c) (s.op a b b) (s.op b c b) ...
= z ∙ e : by rw op_right_inverse (s.op _ _ _) (s.inv _ _) ...
= z : by rw op_right_identity (s.op _ _ _)

@[identity_instance]
theorem left_identity (a b) : identity.op_left_identity (s.op a a b) (s.id a) :=
λ x, 
have (e ∙ x) ∙ x⁻¹ = x ∙ x⁻¹, 
from calc (e ∙ x) ∙ x⁻¹ 
= e ∙ (x ∙ x⁻¹) : by rw op_compatibility (s.op a b a) (s.op a a b) (s.op a a a) (s.op a b a) ...
= e ∙ e : by rw op_right_inverse (s.op _ _ _) ...
= e : by rw op_right_identity (s.op _ _ _) ...
= x ∙ x⁻¹ : by rw op_right_inverse (s.op _ _ _),
op_right_cancellative (s.op _ _ _) this

@[identity_instance]
theorem left_inverse (a b) : identity.op_left_inverse (s.op a b a) (s.inv b a) (s.id a) :=
λ x,
have (x⁻¹ ∙ x) ∙ x⁻¹ = e ∙ x⁻¹, 
from calc (x⁻¹ ∙ x) ∙ x⁻¹
= x⁻¹ ∙ (x ∙ x⁻¹) : by rw op_compatibility (s.op a a b) (s.op a b a) (s.op a b b) (s.op b a b) ...
= x⁻¹ ∙ e : by rw op_right_inverse (s.op _ _ _) (s.inv _ _) ...
= x⁻¹ : by rw op_right_identity (s.op _ _ _) ...
= e ∙ x⁻¹ : by rw op_left_identity (s.op _ _ _),
op_right_cancellative (s.op _ _ _) this

@[identity_instance]
theorem left_cancellative (a b c) : identity.op_left_cancellative (s.op a b c) :=
λ x y z,
assume h : x ∙ y = x ∙ z,
show y = z, 
from calc y
= e ∙ y : by rw op_left_identity (s.op _ _ _) ...
= (x⁻¹ ∙ x) ∙ y : by rw op_left_inverse (s.op _ _ _) ...
= x⁻¹ ∙ (x ∙ y) : by rw op_compatibility (s.op b b c) (s.op b a b) (s.op b a c) (s.op a b c) ...
= x⁻¹ ∙ (x ∙ z) : by rw h ...
= (x⁻¹ ∙ x) ∙ z : by rw op_compatibility (s.op b b c) (s.op b a b) (s.op b a c) (s.op a b c) ...
= e ∙ z : by rw op_left_inverse (s.op _ _ _) ...
= z : by rw op_left_identity (s.op _ _ _)

/- group.infer can't infer op_associative from op_compatibility -/
@[identity_instance]
theorem to_group_assoc (a : α) : identity.op_associative (s.to_group a).op :=
show identity.op_compatibility (s.op a a a) (s.op a a a) (s.op a a a) (s.op a a a),
from op_compatibility _ _ _ _

instance to_category : category s.to_category := category.infer _

instance to_group (a : α) : group (s.to_group a) := group.infer _

end groupoid

end algebra

/- move to group when ready -/
namespace algebra

namespace group_sig
variables {α : Type*} (s : group_sig α)

definition to_groupoid : groupoid_sig (λ (_ _ : unit), α) :=
{ op := λ _ _ _, s.op
, inv := λ _ _, s.inv
, id := λ _, s.id
}

@[unify] definition to_groupoid_op_hint (t : groupoid_sig (λ (_ _ : unit), α)) (a b c : unit) : unification_hint :=
{ pattern := t.op a b c =?= s.op
, constraints := [t =?= s.to_groupoid]
}

@[unify] definition to_groupoid_inv_hint (t : groupoid_sig (λ (_ _ : unit), α)) (a b : unit) : unification_hint :=
{ pattern := t.inv a b =?= s.inv
, constraints := [t =?= s.to_groupoid]
}

@[unify] definition to_groupoid_id_hint (t : groupoid_sig (λ (_ _ : unit), α)) (a : unit) : unification_hint :=
{ pattern := t.id a =?= s.id
, constraints := [t =?= s.to_groupoid]
}

end group_sig

namespace group
variables {α : Type*} (s : group_sig α) [group s]

@[identity_instance]
theorem to_groupoid_compatibility (a b c d : unit) : identity.op_compatibility (s.to_groupoid.op a c d) (s.to_groupoid.op a b c) (s.to_groupoid.op a b d) (s.to_groupoid.op b c d) :=
show identity.op_compatibility s.op s.op s.op s.op, from op_associative s.op

@[identity_instance]
theorem to_groupoid_right_identity (a b : unit) : identity.op_right_identity (s.to_groupoid.op a b b) (s.to_groupoid.id b) :=
show identity.op_right_identity s.op s.id, from op_right_identity s.op s.id

@[identity_instance]
theorem to_groupoid_right_inverse (a b : unit) : identity.op_right_inverse (s.to_groupoid.op a b a) (s.to_groupoid.inv a b) (s.to_groupoid.id b) :=
show identity.op_right_inverse s.op s.inv s.id, from op_right_inverse s.op s.inv s.id

instance to_groupoid : groupoid s.to_groupoid := groupoid.infer _

end group

end algebra