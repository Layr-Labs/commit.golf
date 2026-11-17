import CommitGolfCandidate.Execution
import CommitGolfCandidate.CopyRefinement

/-! Relocated code whose salt loads and heap output use immediates offset by
fixed lags of x18 and x23 runs exactly like the reference code. The physical
state is the reference state with x18/x23 lowered by the lags and a relocated
program counter; every query, reply, cost and fault is unchanged. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- Physical copy of a reference state inside an unrolled block. -/
def unrollShift (d18 d23 delta : Word) (state : MachineState) : MachineState :=
  ((state.setReg .x18 (state.getReg .x18 - d18)).setReg .x23
    (state.getReg .x23 - d23)).setPC (state.pc + delta)

def shiftResult (d18 d23 delta : Word) (result : Execution) : Execution :=
  { result with state := unrollShift d18 d23 delta result.state }

/-- Reference/physical instruction pairs. -/
inductive ShiftRelated (d18 d23 : Word) : Instr → Instr → Prop
  | load (refOff physOff : BitVec 12) (shifted : signExtend12 physOff = signExtend12 refOff + d18) :
      ShiftRelated d18 d23 (.LD .x6 .x18 refOff) (.LD .x6 .x18 physOff)
  | heap (refOff physOff : BitVec 12) (shifted : signExtend12 physOff = signExtend12 refOff + d23) :
      ShiftRelated d18 d23 (.ADDI .x12 .x23 refOff) (.ADDI .x12 .x23 physOff)
  | store (source : Reg) (off : BitVec 12) (allowed : source = .x6 ∨ source = .x0) :
      ShiftRelated d18 d23 (.SD .x10 source off) (.SD .x10 source off)
  | addi (target : Reg) (imm : BitVec 12) (allowed : target = .x12 ∨ target = .x10) :
      ShiftRelated d18 d23 (.ADDI target .x10 imm) (.ADDI target .x10 imm)
  | ecall : ShiftRelated d18 d23 .ECALL .ECALL

theorem unroll_shift_getReg (d18 d23 delta : Word) (state : MachineState) (reg : Reg)
    (not18 : reg ≠ .x18) (not23 : reg ≠ .x23) :
    (unrollShift d18 d23 delta state).getReg reg = state.getReg reg := by
  unfold unrollShift
  rw [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not23),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not18)]

theorem unroll_shift_mem (d18 d23 delta : Word) (state : MachineState) :
    (unrollShift d18 d23 delta state).mem = state.mem := rfl

theorem unroll_shift_pc (d18 d23 delta : Word) (state : MachineState) :
    (unrollShift d18 d23 delta state).pc = state.pc + delta := rfl

theorem unroll_shift_setByte (d18 d23 delta : Word) (state : MachineState)
    (address : Word) (byte : BitVec 8) :
    (unrollShift d18 d23 delta state).setByte address byte =
      unrollShift d18 d23 delta (state.setByte address byte) := by
  cases state; rfl

theorem unroll_shift_writeBits {bits : Nat} (d18 d23 delta : Word) (state : MachineState)
    (address : Word) (answer : BitVec bits) :
    writeBits (unrollShift d18 d23 delta state) address answer =
      unrollShift d18 d23 delta (writeBits state address answer) := by
  unfold writeBits
  have folded (indices : List Nat) (current : MachineState) :
      indices.foldl (fun current i => current.setByte (address + BitVec.ofNat 64 i)
        (BitVec.ofNat 8 (answer.toNat / 2 ^ (8 * i)))) (unrollShift d18 d23 delta current) =
      unrollShift d18 d23 delta (indices.foldl (fun current i => current.setByte
        (address + BitVec.ofNat 64 i) (BitVec.ofNat 8 (answer.toNat / 2 ^ (8 * i)))) current) := by
    induction indices generalizing current with
    | nil => rfl
    | cons index indices ih =>
      rw [List.foldl_cons, List.foldl_cons, unroll_shift_setByte, ih]
  rw [folded]
  have pcSame (indices : List Nat) (current : MachineState) :
      (indices.foldl (fun current i => current.setByte (address + BitVec.ofNat 64 i)
        (BitVec.ofNat 8 (answer.toNat / 2 ^ (8 * i)))) current).pc = current.pc := by
    induction indices generalizing current with
    | nil => rfl
    | cons index indices ih => rw [List.foldl_cons, ih]; rfl
  generalize hfold : (List.range ((bits + 7) / 8)).foldl _ state = folded
  have pcFold : folded.pc = state.pc := by rw [← hfold]; exact pcSame _ _
  cases folded
  cases state
  simp only [unrollShift, MachineState.setPC, MachineState.setReg, MachineState.getReg] at pcFold ⊢
  subst pcFold
  congr 1
  simp only [BitVec.add_assoc, BitVec.add_comm delta 4]

theorem unroll_shift_writeOracle (d18 d23 delta : Word) (state : MachineState)
    (address : Word) (query : PublicSpec.Domain) (answer : PublicSpec.Range query) :
    writeOracleAnswer (unrollShift d18 d23 delta state) address query answer =
      unrollShift d18 d23 delta (writeOracleAnswer state address query answer) := by
  cases query with
  | inl _ => exact unroll_shift_writeBits _ _ _ _ _ _
  | inr query => cases query <;> exact unroll_shift_writeBits _ _ _ _ _ _

theorem unroll_shift_readBuffer (d18 d23 delta : Word) (state : MachineState) (address n : Nat) :
    readBuffer (unrollShift d18 d23 delta state) address n = readBuffer state address n :=
  read_buffer_memory_congr _ _ rfl _ _

theorem unroll_shift_oracleInput (d18 d23 delta : Word) (state : MachineState) :
    oracleInput (unrollShift d18 d23 delta state) = oracleInput state := by
  unfold oracleInput
  rw [unroll_shift_getReg d18 d23 delta state .x13 (by decide) (by decide),
    unroll_shift_getReg d18 d23 delta state .x10 (by decide) (by decide),
    unroll_shift_getReg d18 d23 delta state .x11 (by decide) (by decide),
    unroll_shift_getReg d18 d23 delta state .x12 (by decide) (by decide)]
  simp only [unroll_shift_readBuffer]

theorem unroll_shift_random (d18 d23 delta : Word) (state : MachineState) :
    randomArgumentsValid (unrollShift d18 d23 delta state) = randomArgumentsValid state := by
  unfold randomArgumentsValid
  simp only [unroll_shift_getReg d18 d23 delta state .x10 (by decide) (by decide),
    unroll_shift_getReg d18 d23 delta state .x11 (by decide) (by decide)]

theorem unroll_shift_x18 (d18 d23 delta : Word) (state : MachineState) :
    (unrollShift d18 d23 delta state).getReg .x18 = state.getReg .x18 - d18 := rfl

theorem unroll_shift_x23 (d18 d23 delta : Word) (state : MachineState) :
    (unrollShift d18 d23 delta state).getReg .x23 = state.getReg .x23 - d23 := rfl

theorem unroll_shift_setReg (d18 d23 delta : Word) (state : MachineState) (reg : Reg) (value : Word)
    (not18 : reg ≠ .x18) (not23 : reg ≠ .x23) :
    (unrollShift d18 d23 delta state).setReg reg value =
      unrollShift d18 d23 delta (state.setReg reg value) := by
  cases state
  cases reg <;> simp_all [unrollShift, MachineState.setReg, MachineState.getReg, MachineState.setPC] <;>
    funext r <;> cases r <;> simp_all

theorem unroll_shift_setMem (d18 d23 delta : Word) (state : MachineState) (address value : Word) :
    (unrollShift d18 d23 delta state).setMem address value =
      unrollShift d18 d23 delta (state.setMem address value) := by
  cases state; rfl

theorem unroll_shift_setPC (d18 d23 delta : Word) (state : MachineState) (pc : Word) :
    (unrollShift d18 d23 delta state).setPC (pc + delta) =
      unrollShift d18 d23 delta (state.setPC pc) := by
  cases state; rfl

theorem unroll_shift_next_pc (d18 d23 delta : Word) (state : MachineState) :
    (unrollShift d18 d23 delta state).pc + 4 = (state.pc + 4) + delta := by
  rw [unroll_shift_pc, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_comm delta 4]

theorem unroll_shift_cancel (base lag offset : Word) :
    base - lag + (offset + lag) = base + offset := by
  bv_omega

/-- One related ordinary instruction commutes with the shift and advances by four. -/
theorem unroll_shift_ordinary (d18 d23 delta : Word) (I J : Instr)
    (related : ShiftRelated d18 d23 I J) (notCall : I ≠ .ECALL) (state : MachineState) :
    ordinaryStep (unrollShift d18 d23 delta state) (.base J) =
      (ordinaryStep state (.base I)).map (unrollShift d18 d23 delta) ∧
    ∀ next, ordinaryStep state (.base I) = some next → next.pc = state.pc + 4 := by
  cases related with
  | load a b shifted =>
    have address : (unrollShift d18 d23 delta state).getReg .x18 + signExtend12 b =
        state.getReg .x18 + signExtend12 a := by
      rw [unroll_shift_x18, shifted, unroll_shift_cancel]
    have memory : (unrollShift d18 d23 delta state).getMem (state.getReg .x18 + signExtend12 a) =
        state.getMem (state.getReg .x18 + signExtend12 a) := rfl
    by_cases valid : accessValid (state.getReg .x18 + signExtend12 a) 8 = true
    · refine ⟨?_, ?_⟩
      · simp only [ordinaryStep, memoryArgumentsValid, memAccess, address, valid, execInstrBr,
          ite_true, Option.map_some, memory]
        rw [unroll_shift_next_pc, unroll_shift_setReg _ _ _ _ _ _ (by decide) (by decide),
          unroll_shift_setPC]
      · intro next stepped
        simp only [ordinaryStep, memoryArgumentsValid, memAccess, valid, execInstrBr,
          ite_true, Option.some.injEq] at stepped
        rw [← stepped]; rfl
    · refine ⟨?_, ?_⟩
      · simp only [ordinaryStep, memoryArgumentsValid, memAccess, address, valid, execInstrBr,
          Bool.false_eq_true, ite_false, Option.map_none]
      · intro next stepped
        simp [ordinaryStep, memoryArgumentsValid, memAccess, valid] at stepped
  | heap a b shifted =>
    have value : (unrollShift d18 d23 delta state).getReg .x23 + signExtend12 b =
        state.getReg .x23 + signExtend12 a := by
      rw [unroll_shift_x23, shifted, unroll_shift_cancel]
    refine ⟨?_, ?_⟩
    · simp only [ordinaryStep, memoryArgumentsValid, memAccess, value, execInstrBr, ite_true,
        Option.map_some]
      rw [unroll_shift_next_pc, unroll_shift_setReg _ _ _ _ _ _ (by decide) (by decide),
        unroll_shift_setPC]
    · intro next stepped
      simp only [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, ite_true,
        Option.some.injEq] at stepped
      rw [← stepped]; rfl
  | store source a allowed =>
    have base : (unrollShift d18 d23 delta state).getReg .x10 = state.getReg .x10 :=
      unroll_shift_getReg _ _ _ _ _ (by decide) (by decide)
    have src : (unrollShift d18 d23 delta state).getReg source = state.getReg source := by
      rcases allowed with rfl | rfl <;> exact unroll_shift_getReg _ _ _ _ _ (by decide) (by decide)
    by_cases valid : accessValid (state.getReg .x10 + signExtend12 a) 8 = true
    · refine ⟨?_, ?_⟩
      · simp only [ordinaryStep, memoryArgumentsValid, memAccess, base, src, valid, execInstrBr,
          ite_true, Option.map_some]
        rw [unroll_shift_next_pc, unroll_shift_setMem, unroll_shift_setPC]
      · intro next stepped
        simp only [ordinaryStep, memoryArgumentsValid, memAccess, valid, execInstrBr,
          ite_true, Option.some.injEq] at stepped
        rw [← stepped]; rfl
    · refine ⟨?_, ?_⟩
      · simp only [ordinaryStep, memoryArgumentsValid, memAccess, base, valid, execInstrBr,
          Bool.false_eq_true, ite_false, Option.map_none]
      · intro next stepped
        simp [ordinaryStep, memoryArgumentsValid, memAccess, valid] at stepped
  | addi target imm allowed =>
    have base : (unrollShift d18 d23 delta state).getReg .x10 = state.getReg .x10 :=
      unroll_shift_getReg _ _ _ _ _ (by decide) (by decide)
    have t18 : target ≠ .x18 := by rcases allowed with rfl | rfl <;> decide
    have t23 : target ≠ .x23 := by rcases allowed with rfl | rfl <;> decide
    refine ⟨?_, ?_⟩
    · simp only [ordinaryStep, memoryArgumentsValid, memAccess, base, execInstrBr, ite_true,
        Option.map_some]
      rw [unroll_shift_next_pc, unroll_shift_setReg _ _ _ _ _ _ t18 t23, unroll_shift_setPC]
    · intro next stepped
      simp only [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, ite_true,
        Option.some.injEq] at stepped
      rw [← stepped]; rfl
  | ecall => exact absurd rfl notCall


theorem unroll_shift_writeOracle_pc (state : MachineState) (address : Word)
    (query : PublicSpec.Domain) (answer : PublicSpec.Range query) :
    (writeOracleAnswer state address query answer).pc = state.pc + 4 := by
  cases query with
  | inl _ => rfl
  | inr query => cases query <;> rfl

theorem unroll_shift_writeBits_pc {bits : Nat} (state : MachineState) (address : Word)
    (answer : BitVec bits) : (writeBits state address answer).pc = state.pc + 4 := rfl

theorem shift_result_charge (d18 d23 delta : Word) (result : Execution) (cycles calls : Nat) :
    (shiftResult d18 d23 delta result).charge cycles calls =
      shiftResult d18 d23 delta (result.charge cycles calls) := rfl

/-- Matching windows: reference instructions at `base`, related physical instructions
at the relocated program counter. -/
def ShiftCode (image : Image) (d18 d23 delta base : Word) (count : Nat) : Prop :=
  ∀ (state : MachineState) (i : Nat), i < count → state.pc = base + BitVec.ofNat 64 (4 * i) →
    ∃ I J, fetch image state = some (.base I) ∧
      fetch image (unrollShift d18 d23 delta state) = some (.base J) ∧ ShiftRelated d18 d23 I J

/-- Exact-step simulation of the related window, including every fault and reply. -/
theorem unroll_shift_execute (image : Image) (d18 d23 delta base : Word) (count : Nat)
    (code : ShiftCode image d18 d23 delta base count) (allowCoins : Bool) :
    ∀ (steps i : Nat) (state : MachineState), i + steps ≤ count →
      state.pc = base + BitVec.ofNat 64 (4 * i) →
      execute image steps (unrollShift d18 d23 delta state) allowCoins =
        shiftResult d18 d23 delta <$> execute image steps state allowCoins := by
  intro steps
  induction steps with
  | zero =>
    intro i state _ _
    simp [execute, shiftResult]
  | succ steps ih =>
    intro i state bound pc
    obtain ⟨I, J, fetchI, fetchJ, related⟩ := code state i (by omega) pc
    have advance : ∀ next : MachineState, next.pc = state.pc + 4 →
        next.pc = base + BitVec.ofNat 64 (4 * (i + 1)) := by
      intro next h
      rw [h, pc, BitVec.add_assoc]
      congr 1
      rw [show (4 : Word) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_add]
      congr 1
    have step := ih (i + 1)
    by_cases call : I = .ECALL
    · subst call
      cases related
      have r5 := unroll_shift_getReg d18 d23 delta state .x5 (by decide) (by decide)
      have r10 := unroll_shift_getReg d18 d23 delta state .x10 (by decide) (by decide)
      have r11 := unroll_shift_getReg d18 d23 delta state .x11 (by decide) (by decide)
      have r12 := unroll_shift_getReg d18 d23 delta state .x12 (by decide) (by decide)
      simp only [execute, fetchI, fetchJ, r5, r10, r11, r12, unroll_shift_oracleInput,
        unroll_shift_random]
      by_cases zero : state.getReg .x5 = 0
      · simp only [zero, ite_true]
        cases input : oracleInput state with
        | none => simp [shiftResult]
        | some query =>
          simp only [map_bind]
          congr 1
          funext answer
          rw [unroll_shift_writeOracle, step _ (by omega)
            (advance _ (unroll_shift_writeOracle_pc _ _ _ _))]
          simp only [map_pure, bind_map_left, shift_result_charge]
      · simp only [zero, ite_false]
        by_cases one : state.getReg .x5 = 1
        · simp [one, shiftResult]
        · simp only [one, ite_false]
          split
          · simp only [map_bind]
            congr 1
            funext answer
            rw [unroll_shift_writeBits, step _ (by omega)
              (advance _ (unroll_shift_writeBits_pc _ _ _))]
            simp only [map_pure, bind_map_left, shift_result_charge]
            rfl
          · simp [shiftResult]
    · obtain ⟨stepJ, nextPC⟩ := unroll_shift_ordinary d18 d23 delta I J related call state
      have fetchJ' : fetch image (unrollShift d18 d23 delta state) = some (.base J) := fetchJ
      cases related with
      | ecall => exact absurd rfl call
      | _ =>
        simp only [execute, fetchI, fetchJ', stepJ]
        cases hstep : ordinaryStep state _ with
        | none => simp [shiftResult]
        | some next =>
          simp only [Option.map_some, map_bind]
          rw [step _ (by omega) (advance _ (nextPC next hstep))]
          simp only [map_pure, bind_map_left, shift_result_charge]
          try rfl

end CommitGolfCandidate
