import .basic

namespace algebra

signature magma (α : Type*) :=
(op : α → α → α)

class magma {α} (s : magma_sig α) : Prop := intro ::

abbreviation magma.infer {α} (s : magma_sig α) : magma s := magma.intro _

@[theory]
class comm_magma {α} (s : magma_sig α) : Prop := intro ::
(commutative : identity.op_commutative s.op)

instance comm_magma.to_magma {α} (s : magma_sig α) [i : comm_magma s] : magma s := magma.infer _ 

end algebra
