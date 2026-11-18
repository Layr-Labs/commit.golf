import CommitGolfCandidate.TwoPermutationPackedOpeningFields
import CommitGolfCandidate.TwoPermutationOpeningCapImage
import CommitGolfCandidate.TwoPermutationPackedOpeningPack

namespace TwoPermutationPrototype.PackedOpening
set_option maxRecDepth 4096
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp

/-- The `count` unpacked proof bytes of a state, read from `proofBase`. -/
def proofBytes (state : MachineState) (count : Nat) : List Byte :=
  List.ofFn fun i : Fin count => state.getByte (BitVec.ofNat 64 (Opening.proofBase + i.val))

theorem proof_bytes_length (state : MachineState) (count : Nat) :
    (proofBytes state count).length = count := by
  simp [proofBytes]

theorem proof_bytes_getD (state : MachineState) (count i : Nat) (inside : i < count) :
    (proofBytes state count).getD i 0 = state.getByte (BitVec.ofNat 64 (Opening.proofBase + i)) := by
  simp [proofBytes, List.getD_eq_getElem?_getD, inside]

theorem proof_bytes_congr {left right : MachineState} (memory : left.mem = right.mem) (count : Nat) :
    proofBytes left count = proofBytes right count := by
  simp only [proofBytes, MachineState.getByte, MachineState.getMem, memory]

/-- The common return block at `0x1a5c` sets the exit registers and jumps to the pack postpass,
which rewrites the unpacked proof of `k` records and `b` footer digests (`498k + 30b` bytes at
`proofBase`) in place into `ProofCodec.pack`, returns its length in `x11`, and halts with success.
Nothing outside `[proofBase, proofBase + 2^34)` changes. -/
theorem execute_exit (state : MachineState) (pc : state.pc = 0x1a5c) (k b : Nat)
    (count : state.getReg .x16 = BitVec.ofNat 64 k)
    (start : state.getReg .x20 = BitVec.ofNat 64 Opening.proofBase)
    (length : state.getReg .x21 - state.getReg .x20 = BitVec.ofNat 64 (498*k + 30*b))
    (fits : 498*k + 30*b ≤ Pack.capacityBytes) :
    ∃ final : MachineState,
      (∀ fuel allowCoins, execute openingImage (Pack.exitSteps k b + fuel) state allowCoins =
        pure ⟨.success, final, Pack.exitCycles k b, 0⟩) ∧
      (final.getReg .x11).toNat = ProofCodec.packedLength k (15*k + b) ∧
      (∀ p < ProofCodec.packedLength k (15*k + b),
        final.getByte (BitVec.ofNat 64 (Opening.proofBase + p)) =
          (ProofCodec.pack k (proofBytes state (498*k + 30*b))).getD p 0) ∧
      (∀ a : Word, a.toNat < Opening.proofBase ∨ Opening.proofBase + 2^34 ≤ a.toNat →
        final.getByte a = state.getByte a) := by
  have room : Opening.proofBase + 2^34 ≤ 2^36 := by decide
  have base : Opening.proofBase < 2^36 := by decide
  have fits' := fits
  unfold Pack.capacityBytes at fits'
  have src : Pack.Source k b Opening.proofBase (proofBytes state (498*k + 30*b)) state := by
    intro a lo hi
    rw [proof_bytes_getD _ _ _ (by omega), Nat.add_sub_cancel' lo, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain ⟨final, ran, ret, bytes⟩ :=
    Pack.execute_pack k b Opening.proofBase _ state pc count start length fits room src
  have small : ProofCodec.packedLength k (15*k + b) < 2^33 := by
    unfold ProofCodec.packedLength ProofCodec.bodyLength; omega
  refine ⟨final, ran, ?_, ?_, ?_⟩
  · rw [ret, Pack.toNat_w _ (by unfold Pack.count; omega)]
    rfl
  · intro p inside
    have fit : Opening.proofBase + p < 2^64 := by omega
    rw [bytes, Pack.toNat_w _ fit, if_pos (by unfold Pack.count; omega), Nat.add_sub_cancel_left]
    exact Pack.packed_bytes k b _ (proof_bytes_length _ _) p inside
  · intro a outside
    rw [bytes, if_neg (by unfold Pack.count; omega), if_neg (by
      unfold Pack.scratch Pack.rounded Pack.count; omega)]

end TwoPermutationPrototype.PackedOpening
