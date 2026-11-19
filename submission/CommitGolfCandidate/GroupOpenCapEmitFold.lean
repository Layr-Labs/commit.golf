import CommitGolfCandidate.GroupOpenCapEmitPrefix
import CommitGolfCandidate.GroupOpenFoldRun
import CommitGolfCandidate.K3OpenPack238

/-! # T238 cap emit: the eighth node of a group (`count = 0`)

After the shared alignment-dispatched prefix (the node's first 28 bytes and its halfword 14 in `x31`, then the jump
to WK), word 855 `beq x30,x0` sends `x30 = 0` to WS: 859 `addi x30,x0,7`, the seven folds 860..893 (halfword 14 of
slot `k` of the group OR'd with bits `2k, 2k+1` of `x31` in bits 14, 15), 894 `addi x21,x21,-2`, 895 `jal` to 700,
700 `addi x21,x21,30`: `CapCopy.cycles dest+43` cycles, the cursor 28 bytes on, the countdown back at 7. -/
namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open Opening (capDigestAddress)

set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

private theorem fold_pc859 : BitVec.ofNat 64 (4096+4*855) + signExtend13 16 = BitVec.ofNat 64 (4096+4*859) := by
  decide
private theorem fold_pc700 : BitVec.ofNat 64 (4096+4*895) + signExtend21 0x1ffcf4 = BitVec.ofNat 64 (4096+4*700) := by
  decide
private theorem fold_seven : (0 : Word) + signExtend12 7 = BitVec.ofNat 64 7 := by decide
private theorem fold_back : (signExtend12 0xffe : Word) + signExtend12 30 = BitVec.ofNat 64 28 := by decide

private theorem fold_byte_of_mem {s t : MachineState} (same : s.mem = t.mem) (q : Word) : s.getByte q = t.getByte q := by
  unfold MachineState.getByte MachineState.getMem
  rw [same]

private theorem fold_half_of_mem {s t : MachineState} (same : s.mem = t.mem) (a : Nat) : halfAt s a = halfAt t a := by
  unfold halfAt
  rw [fold_byte_of_mem same, fold_byte_of_mem same]

private theorem fold_addi_reg (s : MachineState) (rd rs : Reg) (imm : BitVec 12) (r : Reg) (other : r ≠ rd) :
    (execInstrBr s (.ADDI rd rs imm)).getReg r = s.getReg r := by
  show ((s.setReg rd (s.getReg rs + signExtend12 imm)).setPC (s.pc + 4)).getReg r = _
  rw [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm other)]

private theorem fold_addi_reg_self (s : MachineState) (rd rs : Reg) (imm : BitVec 12) (nonzero : rd ≠ .x0) :
    (execInstrBr s (.ADDI rd rs imm)).getReg rd = s.getReg rs + signExtend12 imm := by
  show ((s.setReg rd (s.getReg rs + signExtend12 imm)).setPC (s.pc + 4)).getReg rd = _
  rw [MachineState.getReg_setPC, MachineState.getReg_setReg_eq nonzero]

private theorem fold_jal_reg (s : MachineState) (offset : BitVec 21) (r : Reg) :
    (execInstrBr s (.JAL .x0 offset)).getReg r = s.getReg r := by
  show ((s.setReg .x0 (s.pc + 4)).setPC (s.pc + signExtend21 offset)).getReg r = _
  rw [MachineState.getReg_setPC]
  rfl

theorem emit_cap238_fold (groups : List Nat) (state : MachineState) (node dest : Nat)
    (bounded : node < 512) (position : CapPosition groups state node dest)
    (counter : state.getReg .x30 = BitVec.ofNat 64 0) (pc : state.pc = 0x1a70)
    (separate : Opening.proofBase+210 ≤ dest) (aligned : dest%2=0) (fits : dest+30 ≤ MEMORY_BYTES) :
    ∃ after, RunsOpeningBlock state after (CapCopy.cycles dest+43) ∧ after.pc = 0x1af4 ∧
      CapPosition groups after node (dest+28) ∧
      after.getReg .x30 = BitVec.ofNat 64 7 ∧
      (∀ b<28, after.getByte (BitVec.ofNat 64 (dest+b)) = state.getByte (BitVec.ofNat 64 (capDigestAddress node+b))) ∧
      (∀ k<7, halfAt after (dest-182+30*k) =
        (halfAt state (dest-182+30*k) ||| ((halfAt state (capDigestAddress node+28) >>> (2*k)) <<< 14))) ∧
      (∀ a<2^64, ¬EmitTouched dest 0 a → after.getByte (BitVec.ofNat 64 a) = state.getByte (BitVec.ofNat 64 a)) := by
  have ram : MEMORY_BYTES < 2^64 := by decide
  have small : MEMORY_BYTES = 2^36 := rfl
  have low : 182 ≤ dest := by omega
  obtain ⟨mid, run0, pc0, x21m, x31m, regsm, bytesm, framem, lowm⟩ :=
    cap_emit_prefix groups state node dest bounded position pc (by omega) aligned fits
  let x := halfAt state (capDigestAddress node+28)
  -- 855 `beq x30,x0,+16`: taken
  have x30m : mid.getReg .x30 = BitVec.ofNat 64 0 := (regsm .x30 (by decide) (by decide)).trans counter
  let m1 := execInstrBr mid (.BEQ .x30 .x0 16)
  have run1 : RunsOpeningBlock mid m1 1 := beq_step mid 855 .x30 .x0 16 (by decide) pc0 rfl
  have shape1 : m1 = mid.setPC (BitVec.ofNat 64 (4096+4*859)) := by
    show (if mid.getReg .x30 == mid.getReg .x0 then mid.setPC (mid.pc + signExtend13 16)
      else mid.setPC (mid.pc + 4)) = _
    rw [x30m, show mid.getReg .x0 = 0 from rfl, if_pos (by decide), pc0, fold_pc859]
  have m1reg (r : Reg) : m1.getReg r = mid.getReg r := by rw [shape1, MachineState.getReg_setPC]
  have m1mem : m1.mem = mid.mem := by rw [shape1]; rfl
  -- 859 `addi x30,x0,7`
  let m2 := execInstrBr m1 (.ADDI .x30 .x0 7)
  have step2 := row_step m1 859 (.ADDI .x30 .x0 7) (by decide) (by rw [shape1]; rfl) rfl rfl rfl
  have m2reg (r : Reg) (other : r ≠ .x30) : m2.getReg r = mid.getReg r := (fold_addi_reg m1 .x30 .x0 7 r other).trans (m1reg r)
  have m2x30 : m2.getReg .x30 = BitVec.ofNat 64 7 := by
    rw [fold_addi_reg_self m1 .x30 .x0 7 (by decide), show m1.getReg .x0 = 0 from rfl, fold_seven]
  have m2mem : m2.mem = mid.mem := by
    have : m2.mem = m1.mem := rfl
    exact this.trans m1mem
  -- 860..893: the seven folds
  have pc2 : m2.pc = BitVec.ofNat 64 (4096+4*(wsStart+1)) := step2.2
  have pointer2 : m2.getReg .x21 = BitVec.ofNat 64 dest := (m2reg .x21 (by decide)).trans x21m
  have top2 : m2.getReg .x31 = x.zeroExtend 64 := (m2reg .x31 (by decide)).trans x31m
  have codes : ∀ j < 7, RowsCode (foldIterRows (wsStart+1) j) := fun j inside => (fold_iter_code ⟨j, inside⟩).2
  obtain ⟨run3, pc3, x21f, -, keepf, framef, -⟩ :=
    fold_up_to (wsStart+1) codes m2 dest x low (by omega) aligned pc2 pointer2 top2 7 (by omega)
  let m3 := foldUpTo (wsStart+1) 7 m2
  have pc3' : m3.pc = BitVec.ofNat 64 (4096+4*894) := pc3
  -- 894 `addi x21,x21,-2`; 895 `jal` to 700; 700 `addi x21,x21,30`
  let m4 := execInstrBr m3 (.ADDI .x21 .x21 0xffe)
  have step4 := row_step m3 894 (.ADDI .x21 .x21 0xffe) (by decide) pc3' rfl rfl rfl
  let m5 := execInstrBr m4 (.JAL .x0 0x1ffcf4)
  have step5 := row_step m4 895 (.JAL .x0 0x1ffcf4) (by decide) step4.2 rfl rfl rfl
  have pc5 : m5.pc = BitVec.ofNat 64 (4096+4*700) := step5.2.trans fold_pc700
  let after := execInstrBr m5 (.ADDI .x21 .x21 30)
  have step6 := row_step m5 700 (.ADDI .x21 .x21 30) (by decide) pc5 rfl rfl rfl
  have afterMem : after.mem = m3.mem := rfl
  have reg3 (r : Reg) (a : r ≠ .x28) (b : r ≠ .x29) (c : r ≠ .x31) : m3.getReg r = m2.getReg r := keepf r a b c
  have regAfter (r : Reg) (other : r ≠ .x21) : after.getReg r = m3.getReg r :=
    (fold_addi_reg m5 .x21 .x21 30 r other).trans ((fold_jal_reg m4 0x1ffcf4 r).trans (fold_addi_reg m3 .x21 .x21 0xffe r other))
  -- the bytes the folds leave alone
  have byteFold (q : Nat) (qfit : q+8 ≤ 2^64) (away : ∀ j < 7, q ≠ foldAddress dest j ∧ q ≠ foldAddress dest j+1) :
      m3.getByte (BitVec.ofNat 64 q) = m2.getByte (BitVec.ofNat 64 q) :=
    fold_frame_bytes (wsStart+1) codes m2 dest x low (by omega) aligned pc2 pointer2 top2 q qfit away
  refine ⟨after, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have chain := ((((((run0.next run1).next step2.1).next run3).next step4.1).next step5.1).next step6.1)
    exact chain
  · exact step6.2
  · apply cap_position_kept position
    · intro r a b c d e f
      rw [regAfter r b, reg3 r c d f, m2reg r e]
      exact regsm r a f
    · intro a inside
      change after.mem (BitVec.ofNat 64 a) = state.mem (BitVec.ofNat 64 a)
      rw [afterMem]
      have far : ∀ j < 7, BitVec.ofNat 64 a ≠ alignToDword (BitVec.ofNat 64 (foldAddress dest j)) := by
        intro j hj same
        have v := congrArg BitVec.toNat same
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show a < 2^64 by omega),
          align_any _ (by unfold foldAddress; omega)] at v
        unfold foldAddress at v
        omega
      have m3m := framef (BitVec.ofNat 64 a) far
      change m3.getMem (BitVec.ofNat 64 a) = m2.getMem (BitVec.ofNat 64 a) at m3m
      have m2m : m2.getMem (BitVec.ofNat 64 a) = mid.getMem (BitVec.ofNat 64 a) := by
        unfold MachineState.getMem; rw [m2mem]
      exact m3m.trans (m2m.trans (lowm a inside))
    · rw [fold_addi_reg_self m5 .x21 .x21 30 (by decide), fold_jal_reg m4 0x1ffcf4 .x21,
        fold_addi_reg_self m3 .x21 .x21 0xffe (by decide), x21f, BitVec.add_assoc, fold_back, ← BitVec.ofNat_add]
  · rw [regAfter .x30 (by decide), reg3 .x30 (by decide) (by decide) (by decide)]
    exact m2x30
  · intro b inside
    rw [fold_byte_of_mem afterMem, byteFold (dest+b) (by omega) (fun j hj => by unfold foldAddress; omega),
      fold_byte_of_mem m2mem]
    exact bytesm b inside
  · intro k inside
    rw [fold_half_of_mem afterMem]
    have even : (dest-182+30*k) % 2 = 0 := by omega
    have fit : dest-182+30*k+8 ≤ 2^64 := by omega
    have b0 := fold_slot_bytes (wsStart+1) codes m2 dest x low (by omega) aligned pc2 pointer2 top2 k 0 inside (by decide)
    have b1 := fold_slot_bytes (wsStart+1) codes m2 dest x low (by omega) aligned pc2 pointer2 top2 k 1 inside (by decide)
    simp only [Nat.add_zero, Nat.mul_zero, Nat.mul_one] at b0 b1
    change m3.getByte _ = _ at b0 b1
    unfold foldAddress at b0 b1
    unfold halfAt
    rw [b1, b0, half_split]
    unfold foldValue
    rw [fold_half_bytes]
    have h2 : m2.getHalfword (BitVec.ofNat 64 (dest-182+30*k)) = halfAt state (dest-182+30*k) := by
      rw [← half_at_eq m2 _ even fit, fold_half_of_mem m2mem]
      unfold halfAt
      rw [framem _ (by omega) (Or.inl (by omega)), framem _ (by omega) (Or.inl (by omega))]
    rw [h2]
    rfl
  · intro a inside untouched
    have untouched' : ¬ ((dest ≤ a ∧ a < dest + 28) ∨ (∃ k < 7, a = dest-182+30*k ∨ a = dest-181+30*k)) := by
      intro h
      apply untouched
      unfold EmitTouched
      simpa using h
    have outside : a < dest ∨ dest+28 ≤ a := by
      by_contra h
      exact untouched' (Or.inl ⟨by omega, by omega⟩)
    have away : ∀ j < 7, a ≠ foldAddress dest j ∧ a ≠ foldAddress dest j+1 := by
      intro j hj
      unfold foldAddress
      refine ⟨fun e => untouched' (Or.inr ⟨j, hj, Or.inl e⟩), fun e => untouched' (Or.inr ⟨j, hj, Or.inr ?_⟩)⟩
      omega
    rw [fold_byte_of_mem afterMem]
    have toMid : m2.getByte (BitVec.ofNat 64 a) = mid.getByte (BitVec.ofNat 64 a) := fold_byte_of_mem m2mem _
    by_cases room : a+8 ≤ 2^64
    · rw [byteFold a room away, toMid]
      exact framem a inside outside
    · have dword : m3.getMem (alignToDword (BitVec.ofNat 64 a)) = m2.getMem (alignToDword (BitVec.ofNat 64 a)) := by
        apply framef
        intro j hj same
        have v := congrArg BitVec.toNat same
        rw [align_any _ inside, align_any _ (by unfold foldAddress; omega)] at v
        unfold foldAddress at v
        omega
      rw [byte_of_dword _ _ _ dword, toMid]
      exact framem a inside outside

end TwoPermutationPrototype.GroupedOpening
