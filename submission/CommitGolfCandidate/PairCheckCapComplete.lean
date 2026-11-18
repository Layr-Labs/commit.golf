-- Pair-heads copy of TwoPermutationPackedCapComplete (stack/check/work/mkcopy.py); edits below are marked PAIR.
import CommitGolfCandidate.PairCheckCapSuffix
import CommitGolfCandidate.PairCheckNamespaces
import CommitGolfCandidate.PairCheckCapDecode

namespace TwoPermutationPrototype.PairCk.Packed.Checker
open  TwoPermutationPrototype.Packed TwoPermutationPrototype.Packed.Checker TwoPermutationPrototype.PairCk.Packed.Checker
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.Sampling

theorem execute_cap_suffix (oracle : Oracle) (groups : List Nat) (before : MachineState)
    (pointer claim fuel : Nat) (ready : CapSuffixReady groups before pointer claim)
    (fuelBound : 25056 ≤ fuel) : CapFinished oracle groups before pointer claim fuel :=
  execute_cap_suffix_with actualFrontier oracle groups before pointer claim fuel ready fuelBound

theorem canonical_cap_heap (oracle : Oracle) (leaves : DigestTape) :
    CapHeapCorrect oracle (transcriptHeap true oracle.compression leaves) := by
  intro node positive below
  have room : 256 ≤ LENGTH := by decide
  rw [transcript_heap_parent true oracle.compression leaves node positive (by omega)]
  rfl

end TwoPermutationPrototype.PairCk.Packed.Checker
