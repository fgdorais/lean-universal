import .basic
import .magma

set_option default_priority 0

namespace algebra

signature semigroup (α : Type*) :=
(op : α → α → α)

namespace semigroup_sig

definition to_magma {α} (s : semigroup_sig α) : magma_sig α :=
{ op := s.op
}

@[unify] definition to_magma_op_hint {α} (s : semigroup_sig α) (t : magma_sig α) : unification_hint :=
{ pattern := t.op =?= s.op
, constraints := [t =?= s.to_magma]
}

definition pi {ι : Type*} {α : ι → Type*} (s : Π i, semigroup_sig (α i)) : semigroup_sig (Π i, α i) :=
{ op := λ x y i, (s i).op (x i) (y i)
}

definition prod {α₁ : Type*} {α₂ : Type*} (s₁ : semigroup_sig α₁) (s₂ : semigroup_sig α₂) : semigroup_sig (α₁ × α₂) :=
{ op := λ ⟨x₁, x₂⟩ ⟨y₁, y₂⟩, ⟨s₁.op x₁ y₁, s₂.op x₂ y₂⟩
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

instance to_semigroup : semigroup s := semigroup.infer s

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

instance to_semigroup : semigroup s := semigroup.infer s

end cancel_semigroup

@[theory]
class cancel_comm_semigroup : Prop := intro ::
(associative : identity.op_associative s.op)
(commutative : identity.op_commutative s.op)
(right_cancellative : identity.op_right_cancellative s.op)

namespace cancel_comm_semigroup
variable [i : cancel_comm_semigroup s]
include i

instance to_comm_semigroup : comm_semigroup s := comm_semigroup.infer s

@[identity_instance]
theorem left_cancellative : identity.op_left_cancellative s.op :=
begin
intros x y z h,
rw [op_commutative s.op x] at h,
rw [op_commutative s.op x] at h,
exact op_right_cancellative s.op h,
end

instance to_cancel_semigroup : cancel_semigroup s := cancel_semigroup.infer s

end cancel_comm_semigroup

section pi
open semigroup_sig
variables {β : α → Type*} (si : Π i, semigroup_sig (β i))

@[identity_instance]
theorem pi_associative [Π i, semigroup (si i)] : identity.op_associative (semigroup_sig.pi si).op :=
λ x y z, funext $ λ i, op_associative (si i).op _ _ _

@[identity_instance]
theorem pi_commutative [Π i, comm_semigroup (si i)] : identity.op_commutative (semigroup_sig.pi si).op :=
λ x y, funext $ λ i, op_commutative (si i).op _ _

@[identity_instance]
theorem pi_left_cancelative [Π i, cancel_semigroup (si i)] : identity.op_left_cancellative (semigroup_sig.pi si).op :=
λ x y z h, funext $ λ i, op_left_cancellative (si i).op $
show (pi si).op x y i = (pi si).op x z i, from congr_fun h i

@[identity_instance]
theorem pi_right_cancelative [Π i, cancel_semigroup (si i)] : identity.op_right_cancellative (semigroup_sig.pi si).op :=
λ x y z h, funext $ λ i, op_right_cancellative (si i).op $
show (pi si).op x y i = (pi si).op z y i, from congr_fun h i

instance pi_semigroup [Π i, semigroup (si i)] : semigroup (pi si) := semigroup.infer _

instance pi_comm_semigroup [Π i, comm_semigroup (si i)] : comm_semigroup (pi si) := comm_semigroup.infer _

instance pi_cancel_semigroup [Π i, cancel_semigroup (si i)] : cancel_semigroup (pi si) := cancel_semigroup.infer _

instance pi_cancel_comm_semigroup [Π i, cancel_comm_semigroup (si i)] : cancel_comm_semigroup (pi si) := cancel_comm_semigroup.infer _

end pi

section prod
open semigroup_sig
variables {β : Type*} (t : semigroup_sig β)

@[identity_instance]
theorem prod_associative [semigroup s] [semigroup t] : identity.op_associative (semigroup_sig.prod s t).op :=
λ ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩, prod.eq (op_associative s.op _ _ _) (op_associative t.op _ _ _)

@[identity_instance]
theorem prod_commutative [comm_semigroup s] [comm_semigroup t] : identity.op_commutative (semigroup_sig.prod s t).op :=
λ ⟨_, _⟩ ⟨_, _⟩, prod.eq (op_commutative s.op _ _) (op_commutative t.op _ _)

@[identity_instance]
theorem prod_left_cancellative [cancel_semigroup s] [cancel_semigroup t] : identity.op_left_cancellative (semigroup_sig.prod s t).op :=
λ ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ ⟨z₁, z₂⟩ h, prod.eq 
(op_left_cancellative s.op (show ((prod s t).op (x₁, x₂) (y₁, y₂)).fst = ((prod s t).op (x₁, x₂) (z₁, z₂)).fst, by rw h))
(op_left_cancellative t.op (show ((prod s t).op (x₁, x₂) (y₁, y₂)).snd = ((prod s t).op (x₁, x₂) (z₁, z₂)).snd, by rw h))

@[identity_instance]
theorem prod_right_cancellative [cancel_semigroup s] [cancel_semigroup t] : identity.op_right_cancellative (semigroup_sig.prod s t).op :=
λ ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ ⟨z₁, z₂⟩ h, prod.eq 
(op_right_cancellative s.op (show ((prod s t).op (x₁, x₂) (y₁, y₂)).fst = ((prod s t).op (z₁, z₂) (y₁, y₂)).fst, by rw h))
(op_right_cancellative t.op (show ((prod s t).op (x₁, x₂) (y₁, y₂)).snd = ((prod s t).op (z₁, z₂) (y₁, y₂)).snd, by rw h))

instance prod_semigroup [semigroup s] [semigroup t] : semigroup (prod s t) := semigroup.infer _

instance prod_comm_semigroup [comm_semigroup s] [comm_semigroup t] : comm_semigroup (prod s t) := comm_semigroup.infer _

instance prod_cancel_semigroup [cancel_semigroup s] [cancel_semigroup t] : cancel_semigroup (prod s t) := cancel_semigroup.infer _

instance prod_cancel_comm_semigroup [cancel_comm_semigroup s] [cancel_comm_semigroup t] : cancel_comm_semigroup (prod s t) := cancel_comm_semigroup.infer _

end prod

end algebra
