import CommitGolfCandidate.GroupOpenCapMoves
import CommitGolfCandidate.TwoPermutationOpeningCapWrites
import CommitGolfCandidate.GroupOpenCapCopy

/-! Each cap emit copies the first 28 digest bytes and keeps every register but x7, x21 and x28..x31. Word 697 tests the countdown. A plain emit writes the last halfword and advances by 30 bytes. Every eighth emit folds its high bits into the previous seven slots and advances by 28 bytes. -/
namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open Opening (capDigestAddress proofBase)

/-- The halfword at byte `address` (little endian). -/
def halfAt (state : MachineState) (address : Nat) : BitVec 16 :=
  state.getByte (BitVec.ofNat 64 (address+1)) ++ state.getByte (BitVec.ofNat 64 address)

/-- Bytes the emit block writes: its slot `[dest, dest+width)` and, for the 8th node, halfword 14 of the previous
seven slots. -/
def EmitTouched (dest count a : Nat) : Prop :=
  (dest ≤ a ∧ a < dest+(if count=0 then 28 else 30)) ∨
    (count=0 ∧ ∃ k<7, a=dest-182+30*k ∨ a=dest-181+30*k)

def EmitCap238 : Prop :=
  ∀ (groups : List Nat) (state : MachineState) (node dest count : Nat),
    node < 512 → CapPosition groups state node dest → state.getReg .x30=BitVec.ofNat 64 count → count ≤ 7 →
    state.pc=0x1a70 → proofBase+(if count=0 then 210 else 0) ≤ dest → dest%2=0 → dest+30 ≤ MEMORY_BYTES →
    ∃ after, RunsOpeningBlock state after (if count=0 then CapCopy.cycles dest+41 else CapCopy.cycles dest+7) ∧ after.pc=0x1af4 ∧
      CapPosition groups after node (dest+(if count=0 then 28 else 30)) ∧
      after.getReg .x30=BitVec.ofNat 64 (if count=0 then 7 else count-1) ∧
      (∀ b<(if count=0 then 28 else 30),
        after.getByte (BitVec.ofNat 64 (dest+b))=state.getByte (BitVec.ofNat 64 (capDigestAddress node+b))) ∧
      (count=0 → ∀ k<7, halfAt after (dest-182+30*k)=
        (halfAt state (dest-182+30*k) ||| ((halfAt state (capDigestAddress node+28) >>> (2*k)) <<< 14))) ∧
      (∀ a<2^64, ¬EmitTouched dest count a → after.getByte (BitVec.ofNat 64 a)=state.getByte (BitVec.ofNat 64 a)) ∧
      (∀ r, r ≠ .x7 → r ≠ .x21 → r ≠ .x28 → r ≠ .x29 → r ≠ .x30 → r ≠ .x31 → after.getReg r = state.getReg r)

end TwoPermutationPrototype.GroupedOpening
