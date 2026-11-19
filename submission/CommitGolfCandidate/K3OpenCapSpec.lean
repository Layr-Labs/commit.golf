import CommitGolfCandidate.GroupOpenCapMoves
import CommitGolfCandidate.TwoPermutationOpeningCapWrites

/-! T238 cap frontier, one emitted node (opener rows 668..700 with the appended blocks WK 855 and WS 859).
The emit block copies the node's first 28 bytes (14 `lhu/sh` pairs), loads its halfword 14 (`lhu x31,28(x7)`) and
jumps to WK. With the countdown `x30 = count`:
- `count ≠ 0`: `addi x30,x30,-1; sh x31,28(x21)` (a plain 30-byte slot), then `addi x21,x21,30`; 37 cycles;
- `count = 0` (8th node of a group): WS sets `x30 := 7` and ORs bits `2k, 2k+1` of the halfword into bits 14, 15 of
  halfword 14 of each of the previous 7 slots (`x21-182+30k`), `addi x21,x21,-2`, then `addi x21,x21,30`; 71 cycles.
`EmitCap238` is the frozen interface between the emit block (GroupOpenCapEmit) and the cursor (GroupOpenCapSubtree). -/
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
    ∃ after, RunsOpeningBlock state after (if count=0 then 71 else 37) ∧ after.pc=0x1af4 ∧
      CapPosition groups after node (dest+(if count=0 then 28 else 30)) ∧
      after.getReg .x30=BitVec.ofNat 64 (if count=0 then 7 else count-1) ∧
      (∀ b<(if count=0 then 28 else 30),
        after.getByte (BitVec.ofNat 64 (dest+b))=state.getByte (BitVec.ofNat 64 (capDigestAddress node+b))) ∧
      (count=0 → ∀ k<7, halfAt after (dest-182+30*k)=
        (halfAt state (dest-182+30*k) ||| ((halfAt state (capDigestAddress node+28) >>> (2*k)) <<< 14))) ∧
      (∀ a<2^64, ¬EmitTouched dest count a → after.getByte (BitVec.ofNat 64 a)=state.getByte (BitVec.ofNat 64 a))

end TwoPermutationPrototype.GroupedOpening
