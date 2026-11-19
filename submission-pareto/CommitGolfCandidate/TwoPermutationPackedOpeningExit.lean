import CommitGolfCandidate.TwoPermutationPackedOpeningFields
import CommitGolfCandidate.TwoPermutationOpeningCapImage
import CommitGolfCandidate.HeadStreamPack

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
`proofBase`) in place into `ProofCodec.HeadStreamFive.pack`, returns its length in `x11`, and halts with success.
Nothing outside `[proofBase, proofBase + 2^34)` changes. -/
theorem execute_exit (state : MachineState) (pc : state.pc = 0x1a5c) (k b : Nat)
    (count : state.getReg .x16 = BitVec.ofNat 64 k)
    (start : state.getReg .x20 = BitVec.ofNat 64 Opening.proofBase)
    (length : state.getReg .x21 - state.getReg .x20 = BitVec.ofNat 64 (498*k + 30*b))
    (fits : 498*k + 30*b ≤ Pack.capacityBytes) :
    ∃ final : MachineState,
      (∀ fuel allowCoins, execute openingImage (HeadStream.exitSteps k b + fuel) state allowCoins =
        pure ⟨.success, final, HeadStream.exitCycles k b, 0⟩) ∧
      (final.getReg .x11).toNat = ProofCodec.HeadStreamFive.packedLength k (15*k + b) ∧
      (∀ p < ProofCodec.HeadStreamFive.packedLength k (15*k + b),
        final.getByte (BitVec.ofNat 64 (Opening.proofBase + p)) =
          (ProofCodec.HeadStreamFive.pack k (proofBytes state (498*k + 30*b))).getD p 0) ∧
      (∀ a : Word, a.toNat < Opening.proofBase ∨ Opening.proofBase + 2^34 ≤ a.toNat →
        final.getByte a = state.getByte a) := by
  have room : Opening.proofBase + 2^34 ≤ 2^36 := by decide
  have base : Opening.proofBase < 2^36 := by decide
  have fits' := fits
  unfold Pack.capacityBytes at fits'
  have src : Pack.Source k b Opening.proofBase (proofBytes state (498*k + 30*b)) state := by
    intro a lo hi
    rw [proof_bytes_getD _ _ _ (by omega), Nat.add_sub_cancel' lo, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  let P := proofBytes state (498*k+30*b)
  let Q := ProofCodec.pack k P
  let L := ProofCodec.packedLength k (15*k+b)
  let H := Pack.scratch Opening.proofBase+Pack.rounded k b
  obtain ⟨prepared,ran,ready,ret,regs,bytes⟩ :=
    Pack.prepare_pack k b Opening.proofBase _ state pc count start length fits room src
  have small : L+7≤2^33 := by
    dsimp [L]
    unfold ProofCodec.packedLength ProofCodec.bodyLength; omega
  have records : 481*k≤L := by
    dsimp [L]
    unfold ProofCodec.packedLength ProofCodec.bodyLength
    omega
  have qlen : Q.length=L := by
    simp [Q,P,L,ProofCodec.pack_length,proof_bytes_length,ProofCodec.unpackedCount]
    congr 1
    omega
  have source : ∀ p<L, prepared.getByte (BitVec.ofNat 64 (Opening.proofBase+p))=Q.getD p 0 := by
    intro p inside
    have fit : Opening.proofBase+p<2^64 := by omega
    rw [bytes, Pack.toNat_w _ fit, if_pos (by unfold Pack.count; omega), Nat.add_sub_cancel_left]
    exact Pack.packed_bytes k b _ (proof_bytes_length _ _) p inside
  have qhead (r : Nat) (hr : r<k) : Q.getD (481*r+45) 0=ProofCodec.headByte P r := by
    rw [← Pack.packed_bytes k b P (proof_bytes_length _ _) _ (by
      unfold ProofCodec.packedLength ProofCodec.bodyLength Pack.count;omega)]
    rw [ProofCodec.packedByte,if_pos (by unfold ProofCodec.bodyLength Pack.count;omega),
      if_pos (by omega),show (481*r+45)/481=r by omega]
  have gap : Opening.proofBase+2^33≤H := Nat.le_add_right _ _
  have hroom : H+k+8≤Opening.proofBase+2^34 := by
    dsimp [H]
    unfold Pack.scratch Pack.rounded Pack.count
    omega
  have headers : ∀ r<k, (prepared.getByte (BitVec.ofNat 64 (H+r))).toNat%32=
      ProofCodec.HeadStreamFive.head k Q r := by
    intro r hr
    rw [bytes,Pack.toNat_w _ (by omega),if_neg (by unfold Pack.count;omega),if_pos (by dsimp [H];omega)]
    rw [show H+r-Pack.scratch Opening.proofBase=Pack.rounded k b+r by dsimp [H];omega]
    rw [Pack.stashed,if_neg (by omega),show Pack.rounded k b+r-Pack.rounded k b=r by omega]
    rw [ProofCodec.HeadStreamFive.head,if_pos hr,qhead r hr]
  obtain ⟨final,converted,ret',serialized,frame⟩ := HeadStream.convert_run k L Opening.proofBase H Q prepared
    ready regs.x5 regs.x10 ret regs.x16 regs.x20 regs.x27 qlen records small room gap hroom source headers
  refine ⟨final,?_,?_,serialized,?_⟩
  · intro fuel coins
    have h := ran (HeadStream.extraSteps k L+fuel) coins
    rw [converted] at h
    simpa [HeadStream.exitSteps,HeadStream.exitCycles,L,Nat.add_assoc,Execution.charge] using h
  · rw [ret',Pack.toNat_w _ (by omega)]
    rfl
  · intro a outside
    rw [frame a (by omega)]
    rw [bytes, if_neg (by unfold Pack.count; omega), if_neg (by
      unfold Pack.scratch Pack.rounded Pack.count; omega)]

end TwoPermutationPrototype.PackedOpening
