-- Copyright © 2019 François G. Dorais. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.

import .basic
import .semigroup
import .monoid

namespace algebra

signature semilattice (α : Type*) :=
(op : α → α → α)

namespace semilattice_sig
variables {α : Type*} (s : semilattice_sig α)

@[signature_instance]
definition to_semigroup : semigroup_sig α :=
{ op := s.op
}

end semilattice_sig

variables {α : Type*} (s : semilattice_sig α)

@[theory]
class semilattice : Prop := intro ::
(associative : identity.op_associative s.op)
(commutative : identity.op_commutative s.op)
(idempotent : identity.op_idempotent s.op)

namespace semilattice
variable [i : semilattice s]
include i

instance to_comm_semigroup : comm_semigroup s.to_semigroup := comm_semigroup.infer _

end semilattice

end algebra

namespace algebra

signature bounded_semilattice (α : Type*) :=
(op : α → α → α)
(id : α)

namespace bounded_semilattice_sig
variables {α : Type*} (s : bounded_semilattice_sig α)

definition to_semilattice : semilattice_sig α :=
{ op := s.op
}

@[unify] definition to_semilattice_op_hint (t : semilattice_sig α) : unification_hint :=
{ pattern := t.op =?= s.op
, constraints := [t =?= s.to_semilattice]
}

definition to_monoid : monoid_sig α :=
{ op := s.op
, id := s.id
}

@[unify] definition to_monoid_op_hint (t : monoid_sig α) : unification_hint :=
{ pattern := t.op =?= s.op
, constraints := [t =?= s.to_monoid]
}

@[unify] definition to_monoid_id_hint (t : monoid_sig α) : unification_hint :=
{ pattern := t.id =?= s.id
, constraints := [t =?= s.to_monoid]
}

end bounded_semilattice_sig

variables {α : Type*} (s : bounded_semilattice_sig α)

@[theory]
class bounded_semilattice : Prop := intro ::
(associative : identity.op_associative s.op)
(commutative : identity.op_commutative s.op)
(idempotent : identity.op_idempotent s.op)
(right_identity : identity.op_right_identity s.op s.id)

namespace bounded_semilattice
variable [i : bounded_semilattice s]
include i

instance to_semilattice : semilattice s.to_semilattice := semilattice.infer _

instance to_comm_monoid : comm_monoid s.to_monoid := comm_monoid.infer _

end bounded_semilattice

end algebra