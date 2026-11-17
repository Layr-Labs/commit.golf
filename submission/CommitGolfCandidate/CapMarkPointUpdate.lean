import CommitGolfCandidate.CapMarkInvariant

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

theorem cap_mark_point_update (reference before after : MachineState)
    (group node : Nat) (groupBound : group < 512) (nodeBound : node < 512)
    (memory : after.mem = (before.setMem (capMarkAddress group) 1).mem)
    (unchanged : before.getMem (capMarkAddress node) =
      reference.getMem (capMarkAddress node)) :
    after.getMem (capMarkAddress node) =
      if node = group then 1 else reference.getMem (capMarkAddress node) := by
  have lookup : after.getMem (capMarkAddress node) =
      (before.setMem (capMarkAddress group) 1).getMem (capMarkAddress node) :=
    congrArg (fun mem => mem (capMarkAddress node)) memory
  rw [lookup]
  by_cases same : node = group
  · subst node
    rw [MachineState.getMem_setMem_eq, if_pos rfl]
  · have distinct : capMarkAddress node ≠ capMarkAddress group := by
      intro equal
      exact same (cap_mark_address_injective 256 (by decide) node group
        nodeBound groupBound equal)
    rw [MachineState.getMem_setMem_ne distinct, if_neg same]
    exact unchanged

theorem cap_mark_lookup_address (reference before : MachineState) (node : Nat)
    (same : before.getMem (BitVec.ofNat 64 (28672+8*node)) =
      reference.getMem (BitVec.ofNat 64 (28672+8*node))) :
    before.getMem (capMarkAddress node) = reference.getMem (capMarkAddress node) :=
  same

end CommitGolfCandidate
