import CommitGolfCandidate.TwoPermutationHybridModel
import CommitGolfCandidate.TwoPermutationPackedCapSuffix
import CommitGolfCandidate.TwoPermutationPackedCapDecode

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.Sampling

theorem execute_cap_suffix (oracle : Oracle) (groups : List Nat) (before : MachineState)
    (pointer claim fuel : Nat) (ready : CapSuffixReady groups before pointer claim)
    (fuelBound : 25056 ≤ fuel) : CapFinished oracle groups before pointer claim fuel :=
  execute_cap_suffix_with actualFrontier oracle groups before pointer claim fuel ready fuelBound

theorem canonical_cap_heap (oracle : Oracle) (leaves : DigestTape) :
    CapHeapCorrect oracle (Hybrid.heap oracle.compression leaves) := by
  intro node positive below
  have room : 256 ≤ LENGTH/2 := by decide
  rw [Hybrid.heap_parent oracle.compression leaves node ⟨positive,by omega⟩,Hybrid.normalize,ite_eq_left (by omega)]
  rw [if_pos (by omega)] <;> rfl

end TwoPermutationPrototype.Packed.Checker
