import CommitGolfCandidate.S4Image
import CommitGolfCandidate.S3LoopExec

/-! Execution of the 512-leaf physical block. Each physical half replays the retained
stage-3 group code (still present at PC 1011424) under a pointer displacement, so its
distribution is exactly `s3GroupLeaves`; the reference latch only changes the displacement. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Physical frame: reference state with x18/x23 lowered by the lags and a given PC. -/
def s4Frame (d18 d23 pc : Word) (state : MachineState) : MachineState :=
  (unrollShift d18 d23 0 state).setPC pc

theorem s4_frame_shift (d18 d23 pc : Word) (state : MachineState) :
    s4Frame d18 d23 pc state = unrollShift d18 d23 (pc - state.pc) state := by
  unfold s4Frame unrollShift
  rw [show state.pc + (pc - state.pc) = pc by bv_omega]
  cases state; rfl

theorem s4_frame_pc (d18 d23 pc : Word) (state : MachineState) :
    (s4Frame d18 d23 pc state).pc = pc := by
  cases state; rfl

theorem s4_frame_getReg (d18 d23 pc : Word) (state : MachineState) (reg : Reg)
    (h18 : reg ≠ .x18) (h23 : reg ≠ .x23) :
    (s4Frame d18 d23 pc state).getReg reg = state.getReg reg := by
  unfold s4Frame
  rw [MachineState.getReg_setPC, unroll_shift_getReg _ _ _ _ _ h18 h23]

theorem s4_frame_x23 (d18 d23 pc : Word) (state : MachineState) :
    (s4Frame d18 d23 pc state).getReg .x23 = state.getReg .x23 - d23 := rfl

theorem s4_frame_zero (pc : Word) (state : MachineState) (same : state.pc = pc) :
    s4Frame 0 0 pc state = state := by
  subst same
  cases state
  simp only [s4Frame, unrollShift, MachineState.getReg, MachineState.setReg, MachineState.setPC,
    BitVec.sub_zero, BitVec.add_zero, MachineState.mk.injEq, and_true]
  funext reg
  cases reg <;> simp

def s4Lag18 (h : Nat) : Word := BitVec.ofInt 64 (1536 * (h : Int) - 1536)
def s4Lag23 (h : Nat) : Word := BitVec.ofInt 64 (2048 * (h : Int) - 2048)

/-! ### Immediates -/

theorem s4_sign_extend12_small (n : Nat) (small : n < 2048) :
    signExtend12 (BitVec.ofNat 12 n) = BitVec.ofNat 64 n := by
  unfold signExtend12
  have msb : (BitVec.ofNat 12 n).msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt, BitVec.toNat_ofNat]
    omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false msb]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem s4_sign_extend12_int (value : Int) (low : -2048 ≤ value) (high : value < 2048) :
    signExtend12 (BitVec.ofInt 12 value) = BitVec.ofInt 64 value := by
  unfold signExtend12
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le (by decide), BitVec.toInt_ofInt, BitVec.toInt_ofInt]
  simp only [Int.bmod]
  omega

theorem s4_ofNat_ofInt (n : Nat) (small : n < 2048) :
    BitVec.ofNat 64 n = BitVec.ofInt 64 (n : Int) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  omega

theorem s4_imm (n : Nat) (d X : Int) (small : n < 2048) (hX : X = (n : Int) + d)
    (low : -2048 ≤ X) (high : X < 2048) :
    signExtend12 (BitVec.ofInt 12 X) = signExtend12 (BitVec.ofNat 12 n) + BitVec.ofInt 64 d := by
  rw [s4_sign_extend12_small n small, s4_sign_extend12_int X low high, s4_ofNat_ofInt n small]
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_add, BitVec.toInt_ofInt, BitVec.toInt_ofInt, BitVec.toInt_ofInt]
  simp only [Int.bmod]
  omega

theorem s4_related (h u i : Nat) (hh : h < 2) (hu : u < 64) (hi : i < 14) :
    ShiftRelated (s4Lag18 h) (s4Lag23 h) (((s3LeafCode u)[i]?).getD .EBREAK)
      (((s4LeafCode h u)[i]?).getD .EBREAK) := by
  have load (n : Nat) (hn : 24 * u ≤ n) (hn' : n ≤ 24 * u + 16) (X : Int)
      (hX : X = (n : Int) + (1536 * (h : Int) - 1536)) :
      signExtend12 (BitVec.ofInt 12 X) = signExtend12 (BitVec.ofNat 12 n) + s4Lag18 h :=
    s4_imm n _ X (by omega) hX (by omega) (by omega)
  have heap (X : Int) (hX : X = ((32 * u : Nat) : Int) + (2048 * (h : Int) - 2048)) :
      signExtend12 (BitVec.ofInt 12 X) = signExtend12 (BitVec.ofNat 12 (32 * u)) + s4Lag23 h :=
    s4_imm (32 * u) _ X (by omega) hX (by omega) (by omega)
  interval_cases i <;> simp only [s3LeafCode, s4LeafCode, s3LeafHeadInstructions,
    s3LeafMidInstructions, s4LeafMidInstructions, List.cons_append, List.nil_append,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
  · exact .store _ _ (.inr rfl)
  · exact .store _ _ (.inr rfl)
  · exact .addi _ _ (.inl rfl)
  · exact .ecall
  · exact .load _ _ (load (24 * u) (le_refl _) (by omega) _ (by push_cast; ring))
  · exact .store _ _ (.inl rfl)
  · exact .load _ _ (load (24 * u + 8) (by omega) (by omega) _ (by push_cast; ring))
  · exact .store _ _ (.inl rfl)
  · exact .load _ _ (load (24 * u + 16) (by omega) (by omega) _ (by push_cast; ring))
  · exact .store _ _ (.inl rfl)
  · exact .addi _ _ (.inr rfl)
  · exact .heap _ _ (heap _ (by push_cast; ring))
  · exact .ecall
  · exact .addi _ _ (.inr rfl)

/-- Physical start of half `h` of window `w`. -/
def s4HalfPC (w h : Nat) : Nat := 1015228 + 7184 * w + 3584 * h

theorem s4_shift_code (w h : Nat) (hw : w < 4) (hh : h < 2) :
    ShiftCode (submission.image .commit) (s4Lag18 h) (s4Lag23 h)
      (BitVec.ofNat 64 (s4HalfPC w h) - 1011424) 1011424 896 := by
  intro state k hk pc
  have split : k = 14 * (k / 14) + k % 14 := by omega
  refine ⟨_, _, ?_, ?_, s4_related h (k / 14) (k % 14) hh (by omega) (by omega)⟩
  · apply s3_image_leaf (k / 14) (k % 14) (by omega) (by omega)
    rw [pc]
    bv_omega
  · apply s4_image_window w (896 * h + 14 * (k / 14) + k % 14) hw (by omega) _ _ ?_
      (s4_half_decoded h (k / 14) (k % 14) hh (by omega) (by omega))
    rw [unroll_shift_pc, pc]
    unfold s4HalfPC
    bv_omega

/-- One physical half: 896 instructions, 1792 cycles, 128 queries; distribution of one
reference group's leaves. -/
theorem s4_half_execute (w h : Nat) (hw : w < 4) (hh : h < 2)
    (state : MachineState) (cursor nonce heap : Nat)
    (invariant : S3GroupState state 0 cursor nonce heap)
    (cursorAligned : cursor % 8 = 0) (nonceAligned : nonce % 8 = 0) (heapAligned : heap % 8 = 0)
    (cursorBound : cursor + 16384 + 16 ≤ MEMORY_BYTES) (nonceBound : nonce + 1536 ≤ MEMORY_BYTES)
    (heapBound : heap + 2216 ≤ MEMORY_BYTES) (fuel : Nat) :
    execute (submission.image .commit) (896 + fuel)
        (s4Frame (s4Lag18 h) (s4Lag23 h) (BitVec.ofNat 64 (s4HalfPC w h)) state) true =
      (do let leaves ← s3GroupLeaves state 0 64
          let result ← execute (submission.image .commit) fuel
            (s4Frame (s4Lag18 h) (s4Lag23 h) (BitVec.ofNat 64 (s4HalfPC w h + 3584)) leaves) true
          return result.charge 1792 128) := by
  have reference := s3_group_leaves_execute 64 0 state cursor nonce heap (by decide) invariant
    cursorAligned nonceAligned heapAligned (by omega) nonceBound heapBound 0
  have ref := reference.1
  rw [show 14 * 64 + 0 = 896 by rfl] at ref
  have startPC : state.pc = 1011424 := by rw [invariant.pc]; rfl
  rw [s4_frame_shift, startPC, execute_add,
    unroll_shift_execute _ _ _ _ 1011424 896 (s4_shift_code w h hw hh) true 896 0 state
      (by omega) (by rw [startPC]; rfl), ref]
  simp only [bind_assoc, map_bind, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro leaves reached
  have leavesPC : leaves.pc = 1015008 := by
    rw [(reference.2 leaves reached).1.pc]; rfl
  simp only [execute, map_pure, pure_bind, resume, shiftResult, Execution.charge, ite_true,
    bind_pure_comp]
  rw [s4_frame_shift, leavesPC]
  congr 3
  unfold s4HalfPC
  bv_omega

end CommitGolfCandidate
