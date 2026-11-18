import CommitGolfCandidate.TwoPermutationPackedCapSuffix
import CommitGolfCandidate.TwoPermutationPackedCapDecode
import CommitGolfCandidate.TwoPermutationMixedTranscript

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.Sampling

theorem execute_cap_suffix (oracle : Oracle) (groups : List Nat) (before : MachineState)
    (pointer claim fuel : Nat) (ready : CapSuffixReady groups before pointer claim)
    (fuelBound : 25056 ≤ fuel) : CapFinished oracle groups before pointer claim fuel :=
  execute_cap_suffix_with actualFrontier oracle groups before pointer claim fuel ready fuelBound

theorem canonical_cap_heap (oracle : Oracle) (leaves : DigestTape) :
    CapHeapCorrect oracle (mixedTranscriptHeap oracle.compression leaves) := by
  intro node positive below
  have room : 256 ≤ LENGTH := by decide
  let answer : BitVec 256 := oracle.compression
    (mixedTranscriptHeap oracle.compression leaves (2*node+1) ++
      mixedTranscriptHeap oracle.compression leaves (2*node))
  have parent : mixedTranscriptHeap oracle.compression leaves node = projectMixed node answer :=
    mixed_heap_parent oracle.compression leaves node positive (by omega)
  have projected : projectMixed node answer = CommitGolfCandidate.ShortTree.padLow answer :=
    projectMixed_projected node answer (by omega)
  exact parent.trans projected

end TwoPermutationPrototype.Packed.Checker
