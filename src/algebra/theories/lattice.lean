-- Copyright © 2019 François G. Dorais. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.

import .basic
import .semilattice

namespace algebra

signature lattice (α : Type*) :=
(join : α → α → α)
(meet : α → α → α)

namespace lattice_sig
variables {α : Type*} (s : lattice_sig α)

@[signature_instance]
definition to_join_semilattice : semilattice_sig α :=
{ op := s.join
}

@[signature_instance]
definition to_meet_semilattice : semilattice_sig α :=
{ op := s.meet
}

end lattice_sig

variables {α : Type*} (s : lattice_sig α)
local infix ∪ := s.join
local infix ∩ := s.meet

@[theory]
class lattice : Prop := intro ::
(join_associative : identity.op_associative s.join)
(join_commutative : identity.op_commutative s.join)
(join_right_absorptive : identity.op_right_absorptive s.join s.meet)
(meet_associative : identity.op_associative s.meet)
(meet_commutative : identity.op_commutative s.meet)
(meet_right_absorptive : identity.op_right_absorptive s.meet s.join)

namespace lattice
variable [i : lattice s]
include i

@[identity_instance]
theorem join_left_absorptive : identity.op_left_absorptive s.join s.meet :=
λ x y, calc (x ∩ y) ∪ y
= y ∪ (x ∩ y) : by rw op_commutative s.join ...
= y ∪ (y ∩ x) : by rw op_commutative s.meet ...
= y : by rw op_right_absorptive s.join

@[identity_instance]
theorem meet_left_absorptive : identity.op_left_absorptive s.meet s.join :=
λ x y, calc (x ∪ y) ∩ y
= y ∩ (x ∪ y) : by rw op_commutative s.meet ...
= y ∩ (y ∪ x) : by rw op_commutative s.join ...
= y : by rw op_right_absorptive s.meet

@[identity_instance]
theorem join_idempotent : identity.op_idempotent s.join :=
λ x, calc x ∪ x
= x ∪ (x ∩ (x ∪ x)) : by rw op_right_absorptive s.meet ...
= x : by rw op_right_absorptive s.join

@[identity_instance]
theorem meet_idempotent : identity.op_idempotent s.meet :=
λ x, calc x ∩ x
= x ∩ (x ∪ (x ∩ x)) : by rw op_right_absorptive s.join ...
= x : by rw op_right_absorptive s.meet

instance to_join_semilattice : semilattice s.to_join_semilattice := semilattice.infer _

instance to_meet_semilattice : semilattice s.to_meet_semilattice := semilattice.infer _

end lattice

@[theory]
class distributive_lattice : Prop := intro ::
(join_associative : identity.op_associative s.join)
(join_commutative : identity.op_commutative s.join)
(join_right_absorptive : identity.op_right_absorptive s.join s.meet)
(meet_associative : identity.op_associative s.meet)
(meet_commutative : identity.op_commutative s.meet)
(meet_right_absorptive : identity.op_right_absorptive s.meet s.join)
(meet_join_right_distributive : identity.op_right_distributive s.meet s.join)

namespace distributive_lattice
variable [i : distributive_lattice s]
include i

instance to_lattice : lattice s := lattice.infer _

@[identity_instance]
theorem meet_join_left_distributive : identity.op_left_distributive s.meet s.join :=
λ x y z, calc (x ∪ y) ∩ z
= z ∩ (x ∪ y) : by rw op_commutative s.meet ...
= (z ∩ x) ∪ (z ∩ y) : by rw op_right_distributive s.meet s.join ...
= (x ∩ z) ∪ (z ∩ y) : by rw op_commutative s.meet x z ...
= (x ∩ z) ∪ (y ∩ z) : by rw op_commutative s.meet y z

@[identity_instance]
theorem join_meet_left_distributive : identity.op_left_distributive s.join s.meet :=
λ x y z, calc (x ∩ y) ∪ z
= (x ∩ y) ∪ ((y ∩ z) ∪ z) : by rw op_left_absorptive s.join s.meet ...
= (x ∩ y) ∪ ((z ∩ y) ∪ z) : by rw op_commutative s.meet y z ...
= ((x ∩ y) ∪ (z ∩ y)) ∪ z : by rw op_associative s.join ...
= ((x ∪ z) ∩ y) ∪ z : by rw op_left_distributive s.meet s.join ...
= ((x ∪ z) ∩ y) ∪ ((x ∪ z) ∩ z) : by rw op_left_absorptive s.meet s.join ...
= (x ∪ z) ∩ (y ∪ z) : by rw op_right_distributive s.meet s.join

@[identity_instance]
theorem join_meet_right_distributive : identity.op_right_distributive s.join s.meet :=
λ x y z, calc x ∪ (y ∩ z)
= (y ∩ z) ∪ x : by rw op_commutative s.join ...
= (y ∪ x) ∩ (z ∪ x) : by rw op_left_distributive s.join s.meet ...
= (x ∪ y) ∩ (z ∪ x) : by rw op_commutative s.join x y ...
= (x ∪ y) ∩ (x ∪ z) : by rw op_commutative s.join x z

@[identity_instance]
theorem join_meet_cancel_left : identity.op_op_left_cancellative s.join s.meet :=
λ x y z hjoin hmeet, 
calc y
= (x ∪ y) ∩ y : by rw op_left_absorptive s.meet ...
= (x ∪ z) ∩ y : by rw hjoin ...
= (x ∩ y) ∪ (z ∩ y) : by rw op_left_distributive s.meet s.join ...
= (x ∩ z) ∪ (z ∩ y) : by rw hmeet ...
= (x ∩ z) ∪ (y ∩ z) : by rw op_commutative s.meet y z ...
= (x ∪ y) ∩ z : by rw op_left_distributive s.meet s.join ...
= (x ∪ z) ∩ z : by rw hjoin ...
= z : by rw op_left_absorptive s.meet s.join

@[identity_instance]
theorem join_meet_cancel_right : identity.op_op_right_cancellative s.join s.meet :=
λ x z y hjoin hmeet,
have hjoin' : z ∪ x = z ∪ y, 
from calc z ∪ x 
= x ∪ z : by rw op_commutative s.join ...
= y ∪ z : by rw hjoin ...
= z ∪ y : by rw op_commutative s.join,
have hmeet' : z ∩ x = z ∩ y, 
from calc z ∩ x 
= x ∩ z : by rw op_commutative s.meet ...
= y ∩ z : by rw hmeet ...
= z ∩ y : by rw op_commutative s.meet,
join_meet_cancel_left s hjoin' hmeet'

end distributive_lattice

end algebra
