import CommitGolfCandidate.TwoPermutationPackedCapSuffix
import CommitGolfCandidate.TwoPermutationPackedCapDecode

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.Sampling

theorem execute_cap_suffix (oracle : Oracle) (groups : List Nat) (before : MachineState)
    (pointer claim fuel : Nat) (ready : CapSuffixReady groups before pointer claim)
    (fuelBound : 80000 ≤ fuel) : CapFinished oracle groups before pointer claim fuel :=
  execute_cap_suffix_with actualFrontier oracle groups before pointer claim fuel ready fuelBound

end TwoPermutationPrototype.Packed.Checker
