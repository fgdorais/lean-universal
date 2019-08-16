-- Copyright © 2019 François G. Dorais. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.

import .basic
import .lattice
import .semiring

namespace algebra

signature bounded_lattice (α : Type*) :=
(join : α → α → α)
(meet : α → α → α)
(bot : α)
(top : α)

namespace bounded_lattice_sig
variables {α : Type*} (s : bounded_lattice_sig α)

@[signature_instance]
definition to_lattice : lattice_sig α :=
{ join := s.join
, meet := s.meet
}

@[signature_instance]
definition to_bounded_join_semilattice : bounded_semilattice_sig α :=
{ op := s.join
, id := s.bot
}

@[signature_instance]
definition to_bounded_meet_semilattice : bounded_semilattice_sig α :=
{ op := s.meet
, id := s.top
}

@[signature_instance]
definition to_join_meet_semiring : semiring_sig α :=
{ add := s.join
, zero := s.bot
, mul := s.meet
, one := s.top
}

@[signature_instance]
definition to_meet_join_semiring : semiring_sig α :=
{ add := s.meet
, zero := s.top
, mul := s.join
, one := s.bot
}

end bounded_lattice_sig

variables {α : Type*} (s : bounded_lattice_sig α)
local infix ∪ := s.join
local infix ∩ := s.meet
local notation `𝟙` := s.top
local notation `𝟘` := s.bot

@[theory]
class bounded_lattice : Prop := intro ::
(join_associative : identity.op_associative s.join)
(join_commutative : identity.op_commutative s.join)
(join_right_absorptive : identity.op_right_absorptive s.join s.meet)
(join_right_identity : identity.op_right_identity s.join s.bot)
(meet_associative : identity.op_associative s.meet)
(meet_commutative : identity.op_commutative s.meet)
(meet_right_absorptive : identity.op_right_absorptive s.meet s.join)
(meet_right_identity : identity.op_right_identity s.meet s.top)

namespace bounded_lattice
variable [i : bounded_lattice s]
include i

instance to_lattice : lattice s.to_lattice := lattice.infer _

@[identity_instance]
theorem join_idempotent : identity.op_idempotent s.join :=
λ x, op_idempotent s.join x

@[identity_instance]
theorem meet_idempotent : identity.op_idempotent s.meet :=
λ x, op_idempotent s.meet x

instance to_bounded_join_semilattice : bounded_semilattice s.to_bounded_join_semilattice := bounded_semilattice.infer _

instance to_bounded_meet_semilattice : bounded_semilattice s.to_bounded_meet_semilattice := bounded_semilattice.infer _

@[identity_instance]
theorem join_right_null : identity.op_right_fixpoint s.join s.top :=
λ x, calc x ∪ 𝟙
= (x ∩ 𝟙) ∪ 𝟙 : by rw op_right_identity s.meet ...
= 𝟙 : by rw op_left_absorptive s.join

@[identity_instance]
theorem meet_right_null : identity.op_right_fixpoint s.meet s.bot :=
λ x, calc x ∩ 𝟘
= (x ∪ 𝟘) ∩ 𝟘 : by rw op_right_identity s.join ...
= 𝟘 : by rw op_left_absorptive s.meet

end bounded_lattice

@[theory]
class bounded_distributive_lattice : Prop := intro ::
(join_associative : identity.op_associative s.join)
(join_commutative : identity.op_commutative s.join)
(join_right_absorptive : identity.op_right_absorptive s.join s.meet)
(join_right_identity : identity.op_right_identity s.join s.bot)
(meet_associative : identity.op_associative s.meet)
(meet_commutative : identity.op_commutative s.meet)
(meet_right_absorptive : identity.op_right_absorptive s.meet s.join)
(meet_right_identity : identity.op_right_identity s.meet s.top)
(meet_join_right_distributive : identity.op_right_distributive s.meet s.join)

namespace bounded_distributive_lattice
variable [i : bounded_distributive_lattice s]
include i

instance to_bounded_lattice : bounded_lattice s := bounded_lattice.infer _

instance to_distributive_lattice : distributive_lattice s.to_lattice := distributive_lattice.infer _

instance to_join_meet_semiring : comm_semiring s.to_join_meet_semiring := comm_semiring.infer _

/- help to_meet_join_semiring inference -/
@[identity_instance]
theorem join_meet_right_distributive : identity.op_right_distributive s.join s.meet :=
op_right_distributive _ _

instance to_meet_join_semiring : comm_semiring s.to_meet_join_semiring := comm_semiring.infer _

end bounded_distributive_lattice

end algebra
