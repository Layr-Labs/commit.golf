import CommitGolfCandidate.Check

/-! Execution, termination, register preservation, and memory-region bounds for the
level-7 cap-table verification phase (`k = 128`, indices 87..153 of `check`). -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 4096

/-! ### Cap length gate (indices 87..92, PCs 4444..4464) -/

private def capLenInstructions : List Instr :=
  [.ADDI .x6 .x0 0, .SLLI .x6 .x6 11, .ADDI .x6 .x6 37, .SLLI .x6 .x6 11, .ADDI .x6 .x6 0]

private def capLenPrefix (state : MachineState) (count : Nat) : MachineState :=
  (capLenInstructions.take count).foldl execInstrBr state

private theorem cap_len_prefix (state : MachineState) (pc : state.pc = 4444)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (5 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel
            (capLenPrefix state 5) allowCoins
          return result.charge 5 0) := by
  apply execute_unit_steps (states := capLenPrefix state)
  intro i hi
  refine ⟨.base ((capLenInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply check_fetch _ (87 + i) _ (by omega)
    · interval_cases i <;>
        simp [capLenPrefix, capLenInstructions, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

/-- State after checking `x17 = 75776` in cap mode (`4468` on match, `4432` on mismatch). -/
def checkCapLengthState (state : MachineState) : MachineState :=
  (capLenPrefix (checkDispatchState state) 5).setPC
    (if state.getReg .x17 = 75776 then 4468 else 4432)

/-- For `x16 = 128`, 13 cycles reach the cap proof-length decision. -/
theorem check_cap_length_gate (state : MachineState) (pc : state.pc = 4096)
    (is128 : state.getReg .x16 = 128) (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (13 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel
            (checkCapLengthState state) allowCoins
          return result.charge 13 0) := by
  let disp := checkDispatchState state
  have dispPC : disp.pc = 4444 := if_pos is128
  let ready := capLenPrefix disp 5
  have readyPC : ready.pc = 4464 := by
    simp [ready, capLenPrefix, capLenInstructions, execInstrBr, dispPC, MachineState.setPC]
  have ready6 : ready.getReg .x6 = 75776 := by
    simp [ready, capLenPrefix, capLenInstructions, execInstrBr, signExtend12,
      MachineState.getReg, MachineState.setReg, MachineState.setPC]
  have ready17 : ready.getReg .x17 = state.getReg .x17 := by
    have h := (check_dispatch_registers state).2.2.2.2.2.2.1
    simpa [ready, disp, capLenPrefix, capLenInstructions, execInstrBr, signExtend12,
      MachineState.getReg, MachineState.setReg, MachineState.setPC] using h
  have fetched : fetch (submission.image .check) ready = some (.base (.BNE .x6 .x17 8160)) := by
    apply check_fetch ready 92 _ (by decide) readyPC; rfl
  have stepped : ordinaryStep ready (.base (.BNE .x6 .x17 8160)) = some (checkCapLengthState state) := by
    dsimp only [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr]
    rw [ready6, ready17, readyPC]
    simp only [checkCapLengthState, ready, disp, signExtend13, MachineState.setPC]
    by_cases eq : state.getReg .x17 = 75776
    · simp only [eq, ↓reduceIte]; rfl
    · have ne : ((75776 : Word) == state.getReg .x17) = false :=
        beq_false_of_ne (fun h => eq h.symm)
      simp only [eq, ↓reduceIte, bne, ne, Bool.not_false]; rfl
  rw [show 13 + fuel = 7 + (5 + (fuel + 1)) by omega,
    check_dispatch state pc, cap_len_prefix disp dispPC]
  rw [execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  simp [instructionCycles, Execution.charge, ← Nat.add_assoc]

private theorem cap_len_prefix_reg (s : MachineState) (reg : Reg) (not6 : reg ≠ .x6) :
    (capLenPrefix s 5).getReg reg = s.getReg reg := by
  simp only [capLenPrefix, capLenInstructions, List.take, List.foldl, execInstrBr,
    MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not6)]

private theorem cap_len_prefix_mem (s : MachineState) :
    (capLenPrefix s 5).mem = s.mem := rfl

theorem check_cap_length_registers (state : MachineState) :
    (checkCapLengthState state).getReg .x26 = state.getReg .x11 ∧
    (checkCapLengthState state).getReg .x24 = state.getReg .x13 ∧
    (checkCapLengthState state).getReg .x8 = state.getReg .x14 ∧
    (checkCapLengthState state).getReg .x25 = state.getReg .x15 ∧
    (checkCapLengthState state).getReg .x27 = state.getReg .x16 ∧
    (checkCapLengthState state).mem = state.mem := by
  have disp := check_dispatch_registers state
  have keep (reg : Reg) (not6 : reg ≠ .x6) :
      (checkCapLengthState state).getReg reg = (checkDispatchState state).getReg reg :=
    cap_len_prefix_reg (checkDispatchState state) reg not6
  have memEq : (checkCapLengthState state).mem = (checkDispatchState state).mem :=
    cap_len_prefix_mem (checkDispatchState state)
  exact ⟨(keep .x26 (by decide)).trans disp.1,
    (keep .x24 (by decide)).trans disp.2.1,
    (keep .x8 (by decide)).trans disp.2.2.1,
    (keep .x25 (by decide)).trans disp.2.2.2.1,
    (keep .x27 (by decide)).trans disp.2.2.2.2.1,
    memEq.trans disp.2.2.2.2.2.2.2⟩

private theorem run_check_valid_cap (input : CheckInput)
    (valid : input.proof.length ≤ submission.sizes.proof) :
    submission.run .check input = execute (submission.image .check) (submission.steps .check)
      (submission.initialState .check input) false := by
  simp only [Submission.run, valid, decide_true, if_true]; rfl

theorem check_input_cap_length (input : CheckInput)
    (valid : input.proof.length ≤ submission.sizes.proof) :
    ((submission.initialState .check input).getReg .x17 = 75776) ↔
      input.proof.length = 75776 := by
  have lengthBound : input.proof.length < 2^64 := by
    change input.proof.length ≤ 13153337344 at valid; norm_num; omega
  change BitVec.ofNat 64 input.proof.length = BitVec.ofNat 64 75776 ↔ _
  rw [← BitVec.toNat_inj]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt lengthBound,
    Nat.mod_eq_of_lt (by decide : 75776 < 2^64)]

/-- In cap mode (`k = 128`), any in-capacity proof length other than 75,776 rejects in 16 cycles. -/
theorem check_input_cap_wrong_length (input : CheckInput)
    (valid : input.proof.length ≤ submission.sizes.proof)
    (batch : input.positions.card = BATCH)
    (wrong : input.proof.length ≠ 75776) :
    submission.run .check input =
      pure ⟨.failure, checkExitState (checkCapLengthState (submission.initialState .check input)) false,
        16, 0⟩ := by
  have is128 : (submission.initialState .check input).getReg .x16 = 128 := by
    change BitVec.ofNat 64 input.positions.card = 128; rw [batch]; rfl
  have notLen : (submission.initialState .check input).getReg .x17 ≠ 75776 :=
    fun h => wrong ((check_input_cap_length input valid).mp h)
  have rejectPC : (checkCapLengthState (submission.initialState .check input)).pc = 4432 :=
    if_neg notLen
  have steps : submission.steps .check = 13 + (3 + (submission.steps .check - 16)) := by
    change 214748365824 = 13 + (3 + (214748365824 - 16)); rfl
  rw [run_check_valid_cap input valid, steps, check_cap_length_gate _ rfl is128,
    check_exit _ false rejectPC]
  simp [Execution.charge]

/-! ### Cap copy setup & loop (indices 93..118, PCs 4468..4568) -/

private def capCopySetupInstructions : List Instr :=
  [.ADDI .x6 .x0 0, .SLLI .x6 .x6 11, .ADDI .x6 .x6 35, .SLLI .x6 .x6 11, .ADDI .x6 .x6 0,
   .ADD .x19 .x25 .x6, .ADDI .x23 .x19 0, .ADDI .x22 .x0 512,
   .ADDI .x12 .x0 0, .SLLI .x12 .x12 11, .ADDI .x12 .x12 2, .SLLI .x12 .x12 11, .ADDI .x12 .x12 512,
   .ADDI .x28 .x0 128]

private def capCopySetupPrefix (state : MachineState) (count : Nat) : MachineState :=
  (capCopySetupInstructions.take count).foldl execInstrBr state

def checkCapCopySetupState (state : MachineState) : MachineState :=
  capCopySetupPrefix state 14

theorem check_cap_copy_setup (state : MachineState) (pc : state.pc = 4468)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (14 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel
            (checkCapCopySetupState state) allowCoins
          return result.charge 14 0) := by
  apply execute_unit_steps (states := capCopySetupPrefix state)
  intro i hi
  refine ⟨.base ((capCopySetupInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply check_fetch _ (93 + i) _ (by omega)
    · interval_cases i <;>
        simp [capCopySetupPrefix, capCopySetupInstructions, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem check_cap_copy_setup_registers (state : MachineState) (pc : state.pc = 4468) :
    (checkCapCopySetupState state).pc = 4524 ∧
    (checkCapCopySetupState state).getReg .x19 = state.getReg .x25 + 71680 ∧
    (checkCapCopySetupState state).getReg .x23 = state.getReg .x25 + 71680 ∧
    (checkCapCopySetupState state).getReg .x22 = 512 ∧
    (checkCapCopySetupState state).getReg .x12 = 4608 ∧
    (checkCapCopySetupState state).getReg .x28 = 128 ∧
    (checkCapCopySetupState state).mem = state.mem := by
  dsimp only [checkCapCopySetupState, capCopySetupPrefix, capCopySetupInstructions,
    List.take, List.foldl, execInstrBr, signExtend12, MachineState.getReg,
    MachineState.setReg, MachineState.setPC]
  simp [pc]

theorem check_cap_copy_setup_preserves (state : MachineState) (reg : Reg)
    (kept : reg ∈ [Reg.x8, .x24, .x25, .x26, .x27]) :
    (checkCapCopySetupState state).getReg reg = state.getReg reg := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at kept
  rcases kept with rfl | rfl | rfl | rfl | rfl <;>
    simp [checkCapCopySetupState, capCopySetupPrefix, capCopySetupInstructions,
      execInstrBr, signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC]

private def capCopyDigestInstructions : List Instr :=
  [.LD .x6 .x23 0, .SD .x12 .x6 0,
   .LD .x6 .x23 8, .SD .x12 .x6 8,
   .LD .x6 .x23 16, .SD .x12 .x6 16,
   .LD .x6 .x23 24, .SD .x12 .x6 24]

private def capCopyDigestPrefix (state : MachineState) (count : Nat) : MachineState :=
  (capCopyDigestInstructions.take count).foldl execInstrBr state

def checkCapCopyDigestState (state : MachineState) : MachineState :=
  capCopyDigestPrefix state 8

theorem cap_copy_digest_expansion (state : MachineState) :
    checkCapCopyDigestState state =
      ([.LD .x6 .x23 0, .SD .x12 .x6 0,
        .LD .x6 .x23 8, .SD .x12 .x6 8,
        .LD .x6 .x23 16, .SD .x12 .x6 16,
        .LD .x6 .x23 24, .SD .x12 .x6 24] : List Instr).foldl execInstrBr state := rfl

private theorem cap_copy_prefix_reg (state : MachineState) (count : Nat) (bounded : count ≤ 8)
    (reg : Reg) (not6 : reg ≠ .x6) :
    (capCopyDigestPrefix state count).getReg reg = state.getReg reg := by
  have memReg (s : MachineState) (a v : Word) (r : Reg) : (s.setMem a v).getReg r = s.getReg r := by
    cases r <;> rfl
  interval_cases count <;>
    simp only [capCopyDigestPrefix, capCopyDigestInstructions, List.take, List.foldl, execInstrBr,
      MachineState.getReg_setPC, memReg, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not6)]

theorem cap_copy_digest_register (state : MachineState) (reg : Reg) (not6 : reg ≠ .x6) :
    (checkCapCopyDigestState state).getReg reg = state.getReg reg :=
  cap_copy_prefix_reg state 8 (by decide) reg not6

set_option maxHeartbeats 1200000 in
private theorem check_cap_copy_digest (state : MachineState) (pc : state.pc = 4524)
    (srcValid : ∀ word : Fin 4,
      accessValid (state.getReg .x23 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (dstValid : ∀ word : Fin 4,
      accessValid (state.getReg .x12 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (8 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel
            (checkCapCopyDigestState state) allowCoins
          return result.charge 8 0) := by
  apply execute_unit_steps (states := capCopyDigestPrefix state)
  intro i hi
  refine ⟨.base ((capCopyDigestInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply check_fetch _ (107 + i) _ (by omega)
    · interval_cases i <;>
        simp [capCopyDigestPrefix, capCopyDigestInstructions, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · have srcReg := cap_copy_prefix_reg state i (by omega) .x23 (by decide)
    have dstReg := cap_copy_prefix_reg state i (by omega) .x12 (by decide)
    have s0 := srcValid ⟨0, by decide⟩; have s1 := srcValid ⟨1, by decide⟩
    have s2 := srcValid ⟨2, by decide⟩; have s3 := srcValid ⟨3, by decide⟩
    have d0 := dstValid ⟨0, by decide⟩; have d1 := dstValid ⟨1, by decide⟩
    have d2 := dstValid ⟨2, by decide⟩; have d3 := dstValid ⟨3, by decide⟩
    have valid : memoryArgumentsValid (capCopyDigestPrefix state i)
        ((capCopyDigestInstructions[i]?).getD .EBREAK) = true := by
      interval_cases i <;>
        simp only [capCopyDigestInstructions, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.getD_some, memoryArgumentsValid, memAccess, srcReg, dstReg, signExtend12] <;>
        first | exact s0 | exact s1 | exact s2 | exact s3 |
          exact d0 | exact d1 | exact d2 | exact d3
    interval_cases i <;>
      simp only [capCopyDigestInstructions, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some] at valid ⊢ <;>
      simp only [ordinaryStep, valid, ↓reduceIte] <;> rfl
  · interval_cases i <;> rfl

def checkCapCopyLatchState (state : MachineState) : MachineState :=
  let rem := state.getReg .x28 - 1
  (((state.setReg .x23 (state.getReg .x23 + 32)).setReg .x12 (state.getReg .x12 + 32)).setReg
    .x28 rem).setPC (if rem = 0 then 4572 else 4524)

private theorem check_cap_copy_latch (state : MachineState) (pc : state.pc = 4556)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (4 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel
            (checkCapCopyLatchState state) allowCoins
          return result.charge 4 0) := by
  let s1 := (state.setReg .x23 (state.getReg .x23 + 32)).setPC 4560
  let s2 := (s1.setReg .x12 (state.getReg .x12 + 32)).setPC 4564
  let s3 := (s2.setReg .x28 (state.getReg .x28 - 1)).setPC 4568
  have f0 : fetch (submission.image .check) state = some (.base (.ADDI .x23 .x23 32)) := by
    apply check_fetch _ 115 _ (by decide) pc; rfl
  have f1 : fetch (submission.image .check) s1 = some (.base (.ADDI .x12 .x12 32)) := by
    apply check_fetch _ 116 _ (by decide) rfl; rfl
  have f2 : fetch (submission.image .check) s2 = some (.base (.ADDI .x28 .x28 4095)) := by
    apply check_fetch _ 117 _ (by decide) rfl; rfl
  have f3 : fetch (submission.image .check) s3 = some (.base (.BNE .x28 .x0 8148)) := by
    apply check_fetch _ 118 _ (by decide) rfl; rfl
  have st0 : ordinaryStep state (.base (.ADDI .x23 .x23 32)) = some s1 := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, s1, pc]
  have st1 : ordinaryStep s1 (.base (.ADDI .x12 .x12 32)) = some s2 := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, s1, s2,
      MachineState.getReg, MachineState.setReg, MachineState.setPC]
  have st2 : ordinaryStep s2 (.base (.ADDI .x28 .x28 4095)) = some s3 := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, s1, s2, s3,
      MachineState.getReg, MachineState.setReg, MachineState.setPC, BitVec.sub_eq_add_neg]
  have st3 : ordinaryStep s3 (.base (.BNE .x28 .x0 8148)) = some (checkCapCopyLatchState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13, s1, s2, s3,
      checkCapCopyLatchState, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    split <;> simp_all
  rw [Nat.add_comm 4 fuel]
  simp only [execute, f0, st0, f1, st1, f2, st2, f3, st3, instructionCycles, bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

/-- One iteration of `cap-copy`: copy one 32-byte cap digest from `x23` to `x12`. -/
def checkCapCopyStepState (state : MachineState) : MachineState :=
  checkCapCopyLatchState (checkCapCopyDigestState state)

theorem cap_copy_step_registers (state : MachineState) :
    (checkCapCopyStepState state).getReg .x23 = state.getReg .x23 + 32 ∧
    (checkCapCopyStepState state).getReg .x12 = state.getReg .x12 + 32 ∧
    (checkCapCopyStepState state).getReg .x28 = state.getReg .x28 - 1 ∧
    ∀ reg ∉ [Reg.x6, .x12, .x23, .x28],
      (checkCapCopyStepState state).getReg reg = state.getReg reg := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [checkCapCopyStepState, checkCapCopyLatchState, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x28 ≠ .x23),
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x23),
      MachineState.getReg_setReg_eq (by decide : Reg.x23 ≠ .x0),
      cap_copy_digest_register _ .x23 (by decide)]
  · simp only [checkCapCopyStepState, checkCapCopyLatchState, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x28 ≠ .x12),
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0),
      cap_copy_digest_register _ .x12 (by decide)]
  · simp only [checkCapCopyStepState, checkCapCopyLatchState, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x28 ≠ .x0),
      cap_copy_digest_register _ .x28 (by decide)]
  · intro reg hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rcases hr with ⟨n6, n12, n23, n28⟩
    simp only [checkCapCopyStepState, checkCapCopyLatchState, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n28),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n12),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n23),
      cap_copy_digest_register _ reg n6]

theorem cap_copy_step_pc (state : MachineState) :
    (checkCapCopyStepState state).pc = if state.getReg .x28 - 1 = 0 then 4572 else 4524 := by
  change (if (checkCapCopyDigestState state).getReg .x28 - 1 = 0 then 4572 else 4524) = _
  rw [cap_copy_digest_register _ .x28 (by decide)]

private theorem cap_access_valid (address : Word) (bound : address.toNat + 32 ≤ MEMORY_BYTES)
    (aligned : address.toNat % 8 = 0) (word : Fin 4) :
    accessValid (address + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
  have total : address.toNat + 8 * word.val < 2^64 := by simp only [MEMORY_BYTES] at bound; omega
  have val : (address + BitVec.ofNat 64 (8 * word.val)).toNat = address.toNat + 8 * word.val := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 8 * word.val < 2^64), Nat.mod_eq_of_lt total]
  simp only [accessValid, rangeValid, val, Bool.and_eq_true, decide_eq_true_eq]
  constructor <;> omega

private theorem cap_addr_add (address : Word) (offset : Nat)
    (bound : address.toNat + offset ≤ MEMORY_BYTES) :
    (address + BitVec.ofNat 64 offset).toNat = address.toNat + offset := by
  have small : address.toNat + offset < 2^64 := by simp only [MEMORY_BYTES] at bound; omega
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : offset < 2^64), Nat.mod_eq_of_lt small]

theorem check_cap_copy_loop (remaining : Nat) (bounded : remaining ≤ 128) (state : MachineState)
    (counter : state.getReg .x28 = BitVec.ofNat 64 remaining)
    (pc : 0 < remaining → state.pc = 4524)
    (srcBound : (state.getReg .x23).toNat + 32 * remaining ≤ MEMORY_BYTES)
    (srcAligned : (state.getReg .x23).toNat % 8 = 0)
    (dstBound : (state.getReg .x12).toNat + 32 * remaining ≤ MEMORY_BYTES)
    (dstAligned : (state.getReg .x12).toNat % 8 = 0)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (12 * remaining + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel
            (checkCapCopyStepState^[remaining] state) allowCoins
          return result.charge (12 * remaining) 0) := by
  induction remaining generalizing state with
  | zero => simp [Execution.charge]
  | succ remaining ih =>
    have subtract : BitVec.ofNat 64 (remaining + 1) - 1 = BitVec.ofNat 64 remaining := by
      change BitVec.ofNat 64 (remaining + 1) - BitVec.ofNat 64 1 = _
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (remaining + 1) 1 (by decide) (by omega)]; simp
    have nextCnt : (checkCapCopyStepState state).getReg .x28 = BitVec.ofNat 64 remaining := by
      rw [(cap_copy_step_registers state).2.2.1, counter, subtract]
    have nextPC : 0 < remaining → (checkCapCopyStepState state).pc = 4524 := by
      intro pos
      rw [cap_copy_step_pc, counter, subtract, if_neg]
      intro z; have := congrArg BitVec.toNat z
      change remaining % 2^64 = 0 at this; rw [Nat.mod_eq_of_lt (by omega)] at this; omega
    have nextSrc : ((checkCapCopyStepState state).getReg .x23).toNat = (state.getReg .x23).toNat + 32 := by
      rw [(cap_copy_step_registers state).1]; exact cap_addr_add _ 32 (by omega)
    have nextDst : ((checkCapCopyStepState state).getReg .x12).toNat = (state.getReg .x12).toNat + 32 := by
      rw [(cap_copy_step_registers state).2.1]; exact cap_addr_add _ 32 (by omega)
    have copyPC : (checkCapCopyDigestState state).pc = 4556 := by
      simp [checkCapCopyDigestState, capCopyDigestPrefix, capCopyDigestInstructions, execInstrBr,
        pc (by omega), MachineState.setPC]
    have stepDef : checkCapCopyLatchState (checkCapCopyDigestState state) = checkCapCopyStepState state := rfl
    rw [show 12 * (remaining + 1) + fuel = 8 + (4 + (12 * remaining + fuel)) by omega,
      check_cap_copy_digest state (pc (by omega))
        (cap_access_valid _ (by omega) srcAligned) (cap_access_valid _ (by omega) dstAligned),
      check_cap_copy_latch _ copyPC, stepDef,
      ih (by omega) (checkCapCopyStepState state) nextCnt nextPC
        (by rw [nextSrc]; omega) (by rw [nextSrc]; omega)
        (by rw [nextDst]; omega) (by rw [nextDst]; omega)]
    simp only [Function.iterate_succ_apply, bind_assoc, pure_bind]
    apply bind_congr
    intro res
    congr 1
    simp only [Execution.charge, Execution.mk.injEq, true_and]
    constructor <;> omega

theorem cap_copy_loop_finished (remaining : Nat) (pos : 0 < remaining) (bounded : remaining ≤ 128)
    (state : MachineState) (counter : state.getReg .x28 = BitVec.ofNat 64 remaining) :
    (checkCapCopyStepState^[remaining] state).pc = 4572 := by
  induction remaining generalizing state with
  | zero => omega
  | succ remaining ih =>
    have subtract : BitVec.ofNat 64 (remaining + 1) - 1 = BitVec.ofNat 64 remaining := by
      change BitVec.ofNat 64 (remaining + 1) - BitVec.ofNat 64 1 = _
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (remaining + 1) 1 (by decide) (by omega)]; simp
    have nextCnt : (checkCapCopyStepState state).getReg .x28 = BitVec.ofNat 64 remaining := by
      rw [(cap_copy_step_registers state).2.2.1, counter, subtract]
    cases remaining with
    | zero =>
      simp only [Function.iterate_succ_apply, Function.iterate_zero, id_eq]
      rw [cap_copy_step_pc, counter, subtract]; rfl
    | succ remaining =>
      rw [Function.iterate_succ_apply]; exact ih (by omega) (by omega) _ nextCnt

theorem cap_copy_loop_preserves (iterations : Nat) (state : MachineState) (reg : Reg)
    (kept : reg ∉ [Reg.x6, .x12, .x23, .x28]) :
    (checkCapCopyStepState^[iterations] state).getReg reg = state.getReg reg := by
  induction iterations with
  | zero => rfl
  | succ iterations ih =>
    rw [Function.iterate_succ_apply', (cap_copy_step_registers _).2.2.2 reg kept, ih]

theorem cap_copy_digest_outside (state : MachineState) (address : Word)
    (outside : ∀ word : Fin 4, address ≠ state.getReg .x12 + BitVec.ofNat 64 (8 * word.val)) :
    (checkCapCopyDigestState state).getMem address = state.getMem address := by
  have regMem (s : MachineState) (a v : Word) (r : Reg) : (s.setMem a v).getReg r = s.getReg r := by
    cases r <;> rfl
  have a0 : address ≠ state.getReg .x12 := by simpa using outside ⟨0, by decide⟩
  have a1 : address ≠ state.getReg .x12 + 8#64 := outside ⟨1, by decide⟩
  have a2 : address ≠ state.getReg .x12 + 16#64 := outside ⟨2, by decide⟩
  have a3 : address ≠ state.getReg .x12 + 24#64 := outside ⟨3, by decide⟩
  have s0 : signExtend12 0 = 0#64 := rfl
  have s8 : signExtend12 8 = 8#64 := rfl
  have s16 : signExtend12 16 = 16#64 := rfl
  have s24 : signExtend12 24 = 24#64 := rfl
  rw [cap_copy_digest_expansion]
  simp only [List.foldl, execInstrBr, s0, s8, s16, s24, BitVec.add_zero,
    MachineState.getMem_setPC, MachineState.getMem_setReg, MachineState.getReg_setPC, regMem,
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x12),
    MachineState.getMem_setMem_ne a3, MachineState.getMem_setMem_ne a2,
    MachineState.getMem_setMem_ne a1, MachineState.getMem_setMem_ne a0]

/-- `cap-copy` only writes `[dst, dst + 32 * count)`; all words outside are unchanged. -/
theorem cap_copy_loop_outside (count : Nat) (state : MachineState) (address : Word)
    (dstBound : (state.getReg .x12).toNat + 32 * count ≤ MEMORY_BYTES)
    (outside : address.toNat < (state.getReg .x12).toNat ∨
      (state.getReg .x12).toNat + 32 * count ≤ address.toNat) :
    (checkCapCopyStepState^[count] state).getMem address = state.getMem address := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
    have nextDst : ((checkCapCopyStepState state).getReg .x12).toNat = (state.getReg .x12).toNat + 32 := by
      rw [(cap_copy_step_registers state).2.1]; exact cap_addr_add _ 32 (by omega)
    rw [Function.iterate_succ_apply, ih _ (by rw [nextDst]; omega) (by rw [nextDst]; omega)]
    change (checkCapCopyDigestState state).getMem address = state.getMem address
    apply cap_copy_digest_outside
    intro word eq
    have small : (state.getReg .x12).toNat + 8 * word.val < 2^64 := by
      simp only [MEMORY_BYTES] at dstBound; omega
    have same := congrArg BitVec.toNat eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 8 * word.val < 2^64), Nat.mod_eq_of_lt small] at same
    omega

/-! ### Cap parent setup & 127-node tree loop (indices 119..135, PCs 4572..4636) -/

private def capParentSetupInstructions : List Instr :=
  [.ADDI .x5 .x0 0, .ADDI .x11 .x0 64, .ADDI .x13 .x0 0,
   .ADDI .x10 .x0 0, .SLLI .x10 .x10 11, .ADDI .x10 .x10 4, .SLLI .x10 .x10 11, .ADDI .x10 .x10 448,
   .ADDI .x12 .x0 0, .SLLI .x12 .x12 11, .ADDI .x12 .x12 2, .SLLI .x12 .x12 11, .ADDI .x12 .x12 480]

private def capParentSetupPrefix (state : MachineState) (count : Nat) : MachineState :=
  (capParentSetupInstructions.take count).foldl execInstrBr state

def checkCapParentSetupState (state : MachineState) : MachineState :=
  capParentSetupPrefix state 13

theorem check_cap_parent_setup (state : MachineState) (pc : state.pc = 4572)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (13 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel
            (checkCapParentSetupState state) allowCoins
          return result.charge 13 0) := by
  apply execute_unit_steps (states := capParentSetupPrefix state)
  intro i hi
  refine ⟨.base ((capParentSetupInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply check_fetch _ (119 + i) _ (by omega)
    · interval_cases i <;>
        simp [capParentSetupPrefix, capParentSetupInstructions, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem check_cap_parent_setup_registers (state : MachineState) (pc : state.pc = 4572) :
    (checkCapParentSetupState state).pc = 4624 ∧
    (checkCapParentSetupState state).getReg .x5 = 0 ∧
    (checkCapParentSetupState state).getReg .x11 = 64 ∧
    (checkCapParentSetupState state).getReg .x13 = 0 ∧
    (checkCapParentSetupState state).getReg .x10 = 8640 ∧
    (checkCapParentSetupState state).getReg .x12 = 4576 ∧
    (checkCapParentSetupState state).mem = state.mem := by
  dsimp only [checkCapParentSetupState, capParentSetupPrefix, capParentSetupInstructions,
    List.take, List.foldl, execInstrBr, signExtend12, MachineState.getReg,
    MachineState.setReg, MachineState.setPC]
  simp [pc]

theorem check_cap_parent_setup_preserves (state : MachineState) (reg : Reg)
    (kept : reg ∈ [Reg.x8, .x19, .x22, .x24, .x25, .x26, .x27]) :
    (checkCapParentSetupState state).getReg reg = state.getReg reg := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at kept
  rcases kept with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [checkCapParentSetupState, capParentSetupPrefix, capParentSetupInstructions,
      execInstrBr, signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC]

def checkCapParentLatchState (state : MachineState) : MachineState :=
  let nextDst := state.getReg .x12 - 32
  ((state.setReg .x10 (state.getReg .x10 - 64)).setReg .x12 nextDst).setPC
    (if nextDst = state.getReg .x22 then 4640 else 4624)

private theorem check_cap_parent_latch (state : MachineState) (pc : state.pc = 4628)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (3 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel
            (checkCapParentLatchState state) allowCoins
          return result.charge 3 0) := by
  let s1 := (state.setReg .x10 (state.getReg .x10 - 64)).setPC 4632
  let s2 := (s1.setReg .x12 (state.getReg .x12 - 32)).setPC 4636
  have f0 : fetch (submission.image .check) state = some (.base (.ADDI .x10 .x10 4032)) := by
    apply check_fetch _ 133 _ (by decide) pc; rfl
  have f1 : fetch (submission.image .check) s1 = some (.base (.ADDI .x12 .x12 4064)) := by
    apply check_fetch _ 134 _ (by decide) rfl; rfl
  have f2 : fetch (submission.image .check) s2 = some (.base (.BNE .x12 .x22 8180)) := by
    apply check_fetch _ 135 _ (by decide) rfl; rfl
  have st0 : ordinaryStep state (.base (.ADDI .x10 .x10 4032)) = some s1 := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, s1, pc,
      BitVec.sub_eq_add_neg]
  have st1 : ordinaryStep s1 (.base (.ADDI .x12 .x12 4064)) = some s2 := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, s1, s2,
      MachineState.getReg, MachineState.setReg, MachineState.setPC, BitVec.sub_eq_add_neg]
  have st2 : ordinaryStep s2 (.base (.BNE .x12 .x22 8180)) = some (checkCapParentLatchState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13, s1, s2,
      checkCapParentLatchState, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    split <;> simp_all
  rw [Nat.add_comm 3 fuel]
  simp only [execute, f0, st0, f1, st1, f2, st2, instructionCycles, bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

/-- One iteration of `cap-parent`: hash pair `[x10, x10+64) || 0^32` into `x12`, then step down. -/
def checkCapParentStepState (state : MachineState) (answer : BitVec 256) : MachineState :=
  checkCapParentLatchState (paddedCompressionState state answer)

theorem cap_parent_step_registers (state : MachineState) (answer : BitVec 256) :
    (checkCapParentStepState state answer).getReg .x10 = state.getReg .x10 - 64 ∧
    (checkCapParentStepState state answer).getReg .x12 = state.getReg .x12 - 32 ∧
    ∀ reg ∉ [Reg.x10, .x11, .x12, .x14, .x15, .x16, .x17, .x31],
      (checkCapParentStepState state answer).getReg reg = state.getReg reg := by
  have padReg (r : Reg) (n11 : r ≠ .x11) (n14 : r ≠ .x14) (n15 : r ≠ .x15)
      (n16 : r ≠ .x16) (n17 : r ≠ .x17) (n31 : r ≠ .x31) :
      (paddedCompressionState state answer).getReg r = state.getReg r :=
    padded_compression_register state answer r n14 n15 n16 n17 n31 n11
  refine ⟨?_, ?_, ?_⟩
  · simp only [checkCapParentStepState, checkCapParentLatchState, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10),
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0),
      padReg .x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  · simp only [checkCapParentStepState, checkCapParentLatchState, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0),
      padReg .x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  · intro reg hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rcases hr with ⟨n10, n11, n12, n14, n15, n16, n17, n31⟩
    simp only [checkCapParentStepState, checkCapParentLatchState, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n12),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n10)]
    exact padReg reg n11 n14 n15 n16 n17 n31

theorem cap_parent_step_pc (state : MachineState) (answer : BitVec 256) :
    (checkCapParentStepState state answer).pc =
      if state.getReg .x12 - 32 = state.getReg .x22 then 4640 else 4624 := by
  change (if (paddedCompressionState state answer).getReg .x12 - 32 =
      (paddedCompressionState state answer).getReg .x22 then 4640 else 4624) = _
  rw [padded_compression_register state answer .x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    padded_compression_register state answer .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]

/-- Semantic loop for `count` top-7 parent compressions (indices `count` down to `1`). -/
def checkCapParentLoop (state : MachineState) : Nat → OracleComp World MachineState
  | 0 => pure state
  | count + 1 => do
      let answer ← World.query (.inr (.inl (padInput (readBuffer state (state.getReg .x10).toNat 64))))
      checkCapParentLoop (checkCapParentStepState state answer) count

theorem check_cap_parent_loop (count : Nat) (bounded : count ≤ 127) (state : MachineState)
    (pc : 0 < count → state.pc = 4624)
    (r5 : state.getReg .x5 = 0) (r13 : state.getReg .x13 = 0)
    (r22 : state.getReg .x22 = 512)
    (r10 : state.getReg .x10 = BitVec.ofNat 64 (512 + 64 * count))
    (r12 : state.getReg .x12 = BitVec.ofNat 64 (512 + 32 * count))
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (20 * count + fuel) state allowCoins =
      (do let finished ← checkCapParentLoop state count
          let result ← execute (submission.image .check) fuel finished allowCoins
          return result.charge (27 * count) count) := by
  induction count generalizing state with
  | zero => simp [checkCapParentLoop, Execution.charge]
  | succ count ih =>
    have r10Nat : (state.getReg .x10).toNat = 512 + 64 * (count + 1) := by
      rw [r10, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have r12Nat : (state.getReg .x12).toNat = 512 + 32 * (count + 1) := by
      rw [r12, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have srcValid : rangeValid (state.getReg .x10) 96 = true := by
      simp only [rangeValid, r10Nat, MEMORY_BYTES, decide_eq_true_eq]; omega
    have dstValid : rangeValid (state.getReg .x12) 32 = true := by
      simp only [rangeValid, r12Nat, MEMORY_BYTES, decide_eq_true_eq]; omega
    have call := padding_call true state 132 (Or.inr rfl) (pc (by omega))
      r5 r13 srcValid dstValid (by rw [r10Nat]; omega) (by rw [r12Nat]; omega)
      (by rw [r10Nat, r12Nat]; omega) (3 + (20 * count + fuel)) allowCoins
    simp only [paddingProgram] at call
    rw [show 20 * (count + 1) + fuel = 17 + (3 + (20 * count + fuel)) by omega]
    erw [call]
    simp only [checkCapParentLoop, bind_assoc, pure_bind]
    apply congrArg (fun k =>
      (liftM (World.query (.inr (.inl (padInput (readBuffer state (state.getReg .x10).toNat 64))))) :
        OracleComp World (BitVec 256)) >>= k)
    funext answer
    change BitVec 256 at answer
    have afterPC : (paddedCompressionState state answer).pc = 4628 := by
      rw [padded_compression_pc, pc (by omega)]; rfl
    have next10 : (checkCapParentStepState state answer).getReg .x10 =
        BitVec.ofNat 64 (512 + 64 * count) := by
      rw [(cap_parent_step_registers state answer).1, r10]
      change BitVec.ofNat 64 (512 + 64 * (count + 1)) - BitVec.ofNat 64 64 = _
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) _ _ (by omega) (by omega)]
      congr 1
    have next12 : (checkCapParentStepState state answer).getReg .x12 =
        BitVec.ofNat 64 (512 + 32 * count) := by
      rw [(cap_parent_step_registers state answer).2.1, r12]
      change BitVec.ofNat 64 (512 + 32 * (count + 1)) - BitVec.ofNat 64 32 = _
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) _ _ (by omega) (by omega)]
      congr 1
    have nextPC : 0 < count → (checkCapParentStepState state answer).pc = 4624 := by
      intro pos
      rw [cap_parent_step_pc, ← (cap_parent_step_registers state answer).2.1, next12, r22, if_neg]
      intro eq
      have n := congrArg BitVec.toNat eq
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 512 + 32 * count < 2^64)] at n
      change 512 + 32 * count = 512 at n
      omega
    have stepDef : checkCapParentLatchState (paddedCompressionState state answer) =
        checkCapParentStepState state answer := rfl
    rw [check_cap_parent_latch _ afterPC, stepDef,
      ih (by omega) (checkCapParentStepState state answer) nextPC
        (((cap_parent_step_registers state answer).2.2 .x5 (by decide)).trans r5)
        (((cap_parent_step_registers state answer).2.2 .x13 (by decide)).trans r13)
        (((cap_parent_step_registers state answer).2.2 .x22 (by decide)).trans r22)
        next10 next12]
    simp only [bind_assoc, pure_bind]
    apply bind_congr
    intro finished
    apply bind_congr
    intro res
    congr 1
    simp only [Execution.charge, Execution.mk.injEq, true_and]
    constructor <;> omega

theorem cap_parent_loop_finished (count : Nat) (bounded : count ≤ 127) (state : MachineState)
    (r22 : state.getReg .x22 = 512)
    (r12 : state.getReg .x12 = BitVec.ofNat 64 (512 + 32 * count))
    (finished : MachineState) (reached : finished ∈ support (checkCapParentLoop state count)) :
    (0 < count → finished.pc = 4640) ∧
    ∀ reg ∉ [Reg.x10, .x11, .x12, .x14, .x15, .x16, .x17, .x31],
      finished.getReg reg = state.getReg reg := by
  induction count generalizing state with
  | zero =>
    simp only [checkCapParentLoop, support_pure, Set.mem_singleton_iff] at reached
    subst finished
    exact ⟨by omega, fun _ _ => rfl⟩
  | succ count ih =>
    simp only [checkCapParentLoop, mem_support_bind_iff] at reached
    obtain ⟨answer, _, tailReached⟩ := reached
    change BitVec 256 at answer
    have next12 : (checkCapParentStepState state answer).getReg .x12 =
        BitVec.ofNat 64 (512 + 32 * count) := by
      rw [(cap_parent_step_registers state answer).2.1, r12]
      change BitVec.ofNat 64 (512 + 32 * (count + 1)) - BitVec.ofNat 64 32 = _
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) _ _ (by omega) (by omega)]
      congr 1
    have next22 : (checkCapParentStepState state answer).getReg .x22 = 512 :=
      ((cap_parent_step_registers state answer).2.2 .x22 (by decide)).trans r22
    have rest := ih (by omega) _ next22 next12 tailReached
    refine ⟨?_, ?_⟩
    · intro _
      cases count with
      | zero =>
        simp only [checkCapParentLoop, support_pure, Set.mem_singleton_iff] at tailReached
        subst finished
        rw [cap_parent_step_pc, ← (cap_parent_step_registers state answer).2.1, next12, r22]
        rfl
      | succ count => exact rest.1 (by omega)
    · intro reg hr
      exact (rest.2 reg hr).trans ((cap_parent_step_registers state answer).2.2 reg hr)

private theorem align_to_dword_of_nat (n : Nat) (hn : n < 2 ^ 64) :
    alignToDword (BitVec.ofNat 64 n) = BitVec.ofNat 64 (8 * (n / 8)) := by
  have offset : byteOffset (BitVec.ofNat 64 n) = n % 8 := by
    unfold byteOffset
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
    change n &&& (2 ^ 3 - 1) = n % 2 ^ 3
    exact Nat.and_two_pow_sub_one_eq_mod _ _
  have parts : alignToDword (BitVec.ofNat 64 n) + BitVec.ofNat 64 (byteOffset (BitVec.ofNat 64 n)) =
      BitVec.ofNat 64 n := by
    unfold alignToDword byteOffset
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have disjoint : (BitVec.ofNat 64 n &&& ~~~7#64) &&& (BitVec.ofNat 64 n &&& 7#64) = 0 := by
      ext i; simp only [BitVec.getElem_and, BitVec.getElem_not]; cases (7#64)[i] <;> simp
    have combined : (BitVec.ofNat 64 n &&& ~~~7#64) ||| (BitVec.ofNat 64 n &&& 7#64) =
        BitVec.ofNat 64 n := by
      ext i; simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not]; cases (7#64)[i] <;> simp
    rw [BitVec.add_eq_or_of_and_eq_zero _ _ disjoint, combined]
  rw [offset] at parts
  have joined : BitVec.ofNat 64 (8 * (n / 8)) + BitVec.ofNat 64 (n % 8) = BitVec.ofNat 64 n := by
    rw [← BitVec.ofNat_add]; congr 1; omega
  have canceled := congrArg (fun value : Word => value - BitVec.ofNat 64 (n % 8)) (parts.trans joined.symm)
  simpa only [BitVec.add_sub_cancel] using canceled

/-- Every supported run of `checkCapParentLoop` writes only inside `[544, 544 + 32 * count)`. -/
theorem cap_parent_loop_support_outside (count : Nat) (bounded : count ≤ 127) (state : MachineState)
    (r12 : state.getReg .x12 = BitVec.ofNat 64 (512 + 32 * count))
    (finished : MachineState) (reached : finished ∈ support (checkCapParentLoop state count))
    (address : Word)
    (outside : address.toNat < 544 ∨ 512 + 32 * (count + 1) ≤ address.toNat) :
    finished.getMem address = state.getMem address := by
  induction count generalizing state with
  | zero =>
    simp only [checkCapParentLoop, support_pure, Set.mem_singleton_iff] at reached
    subst finished; rfl
  | succ count ih =>
    simp only [checkCapParentLoop, mem_support_bind_iff] at reached
    obtain ⟨answer, _, tailReached⟩ := reached
    change BitVec 256 at answer
    have next12 : (checkCapParentStepState state answer).getReg .x12 =
        BitVec.ofNat 64 (512 + 32 * count) := by
      rw [(cap_parent_step_registers state answer).2.1, r12]
      change BitVec.ofNat 64 (512 + 32 * (count + 1)) - BitVec.ofNat 64 32 = _
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) _ _ (by omega) (by omega)]
      congr 1
    rw [ih (by omega) _ next12 tailReached (by omega)]
    change (paddedCompressionState state answer).mem address = state.mem address
    rw [padded_compression_memory state answer]
    apply writeBits_memory_outside
    intro i hi
    change i < 32 at hi
    rw [r12]
    intro eq
    have addEq : BitVec.ofNat 64 (512 + 32 * (count + 1)) + BitVec.ofNat 64 i =
        BitVec.ofNat 64 (512 + 32 * (count + 1) + i) := (BitVec.ofNat_add _ _).symm
    rw [addEq, align_to_dword_of_nat _ (by omega)] at eq
    have same := congrArg BitVec.toNat eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at same
    omega

/-! ### Cap root comparison setup (136..137) and transition to unified loop (150..153) -/

def checkCapRootSetupState (state : MachineState) : MachineState :=
  ((state.setReg .x21 (state.getReg .x22 + 32)).setReg .x23 (state.getReg .x26)).setPC 4648

theorem check_cap_root_setup (state : MachineState) (pc : state.pc = 4640)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (2 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel
            (checkCapRootSetupState state) allowCoins
          return result.charge 2 0) := by
  let s1 := (state.setReg .x21 (state.getReg .x22 + 32)).setPC 4644
  have f0 : fetch (submission.image .check) state = some (.base (.ADDI .x21 .x22 32)) := by
    apply check_fetch _ 136 _ (by decide) pc; rfl
  have f1 : fetch (submission.image .check) s1 = some (.base (.ADDI .x23 .x26 0)) := by
    apply check_fetch _ 137 _ (by decide) rfl; rfl
  have st0 : ordinaryStep state (.base (.ADDI .x21 .x22 32)) = some s1 := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, s1, pc]
  have st1 : ordinaryStep s1 (.base (.ADDI .x23 .x26 0)) = some (checkCapRootSetupState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, s1,
      checkCapRootSetupState, MachineState.getReg, MachineState.setReg, MachineState.setPC]
  rw [Nat.add_comm 2 fuel]
  simp only [execute, f0, st0, f1, st1, instructionCycles, bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

private def capEnterLoopInstructions : List Instr :=
  [.ADDI .x26 .x19 0, .ADDI .x30 .x0 17, .ADDI .x21 .x0 256, .JAL .x0 2096600]

private def capEnterLoopPrefix (state : MachineState) (count : Nat) : MachineState :=
  (capEnterLoopInstructions.take count).foldl execInstrBr state

def checkCapEnterLoopState (state : MachineState) : MachineState :=
  (((state.setReg .x26 (state.getReg .x19)).setReg .x30 17).setReg .x21 256).setPC 4156

set_option maxRecDepth 4096 in
theorem check_cap_enter_loop (state : MachineState) (pc : state.pc = 4696)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (4 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel
            (checkCapEnterLoopState state) allowCoins
          return result.charge 4 0) := by
  let s1 := (state.setReg .x26 (state.getReg .x19)).setPC 4700
  let s2 := (s1.setReg .x30 17).setPC 4704
  let s3 := (s2.setReg .x21 256).setPC 4708
  have f0 : fetch (submission.image .check) state = some (.base (.ADDI .x26 .x19 0)) := by
    apply check_fetch _ 150 _ (by decide) pc; rfl
  have f1 : fetch (submission.image .check) s1 = some (.base (.ADDI .x30 .x0 17)) := by
    apply check_fetch _ 151 _ (by decide) rfl; rfl
  have f2 : fetch (submission.image .check) s2 = some (.base (.ADDI .x21 .x0 256)) := by
    apply check_fetch _ 152 _ (by decide) rfl; rfl
  have f3 : fetch (submission.image .check) s3 = some (.base (.JAL .x0 2096600)) := by
    apply check_fetch _ 153 _ (by decide) rfl; rfl
  have st0 : ordinaryStep state (.base (.ADDI .x26 .x19 0)) = some s1 := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, s1, pc]
  have st1 : ordinaryStep s1 (.base (.ADDI .x30 .x0 17)) = some s2 := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, s1, s2,
      MachineState.getReg, MachineState.setReg, MachineState.setPC]
  have st2 : ordinaryStep s2 (.base (.ADDI .x21 .x0 256)) = some s3 := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, s1, s2, s3,
      MachineState.getReg, MachineState.setReg, MachineState.setPC]
  have st3 : ordinaryStep s3 (.base (.JAL .x0 2096600)) = some (checkCapEnterLoopState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend21, s1, s2, s3,
      checkCapEnterLoopState, MachineState.getReg, MachineState.setReg, MachineState.setPC]
  rw [Nat.add_comm 4 fuel]
  simp only [execute, f0, st0, f1, st1, f2, st2, f3, st3, instructionCycles, bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

/-! ### Complete cap-tree computation prior to the root comparison -/

attribute [local irreducible] checkCapCopyStepState checkCapParentStepState

/-- State distribution right at the cap-root comparison (PC 4648) for an admitted
`k = 128` input of length `75776`. -/
def checkCapHash (initial : MachineState) : OracleComp World MachineState := do
  let afterCopy := checkCapCopyStepState^[128] (checkCapCopySetupState (checkCapLengthState initial))
  let afterParents ← checkCapParentLoop (checkCapParentSetupState afterCopy) 127
  return checkCapRootSetupState afterParents

/-- Execute the entire cap-copy and 127-compression top-tree phase from `initial` (PC 4096)
to the cap-root comparison (PC 4648): 4118 instructions, 5007 cycles, 127 queries. -/
theorem check_cap_hash (initial : MachineState) (pc : initial.pc = 4096)
    (is128 : initial.getReg .x16 = 128) (isLen : initial.getReg .x17 = 75776)
    (proofBase : initial.getReg .x15 = BitVec.ofNat 64 submission.layout.proof)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (4118 + fuel) initial allowCoins =
      (do let hashed ← checkCapHash initial
          let result ← execute (submission.image .check) fuel hashed allowCoins
          return result.charge 5007 127) := by
  let lenState := checkCapLengthState initial
  have lenPC : lenState.pc = 4468 := if_pos isLen
  let copySetup := checkCapCopySetupState lenState
  have csRegs := check_cap_copy_setup_registers lenState lenPC
  have csSrc : copySetup.getReg .x23 = BitVec.ofNat 64 (submission.layout.proof + 71680) := by
    rw [csRegs.2.2.1, (check_cap_length_registers initial).2.2.2.1, proofBase]; rfl
  let afterCopy := checkCapCopyStepState^[128] copySetup
  have copyEndPC : afterCopy.pc = 4572 :=
    cap_copy_loop_finished 128 (by decide) (by decide) copySetup csRegs.2.2.2.2.2.1
  let parSetup := checkCapParentSetupState afterCopy
  have psRegs := check_cap_parent_setup_registers afterCopy copyEndPC
  have ps22 : parSetup.getReg .x22 = 512 := by
    rw [check_cap_parent_setup_preserves afterCopy .x22 (by simp),
      cap_copy_loop_preserves 128 copySetup .x22 (by decide), csRegs.2.2.2.1]
  rw [show 4118 + fuel = 13 + (14 + (12 * 128 + (13 + (20 * 127 + (2 + fuel))))) by omega,
    check_cap_length_gate initial pc is128,
    check_cap_copy_setup lenState lenPC,
    check_cap_copy_loop 128 (by decide) copySetup csRegs.2.2.2.2.2.1 (fun _ => csRegs.1)
      (by rw [csSrc]; decide) (by rw [csSrc]; decide)
      (by rw [csRegs.2.2.2.2.1]; decide) (by rw [csRegs.2.2.2.2.1]; decide),
    check_cap_parent_setup afterCopy copyEndPC,
    check_cap_parent_loop 127 (by decide) parSetup (fun _ => psRegs.1)
      psRegs.2.1 psRegs.2.2.2.1 ps22
      (by rw [psRegs.2.2.2.2.1]; rfl) (by rw [psRegs.2.2.2.2.2.1]; rfl)]
  simp only [checkCapHash, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro finished reached
  have parEnd := cap_parent_loop_finished 127 (by decide) parSetup ps22
    (by rw [psRegs.2.2.2.2.2.1]; rfl) finished reached
  rw [check_cap_root_setup finished (parEnd.1 (by decide))]
  simp only [bind_assoc, pure_bind]
  apply bind_congr
  intro res
  congr 1
  simp only [Execution.charge, Execution.mk.injEq, true_and]
  constructor <;> omega

theorem check_cap_hash_registers (initial hashed : MachineState)
    (is128 : initial.getReg .x16 = 128) (isLen : initial.getReg .x17 = 75776)
    (reached : hashed ∈ support (checkCapHash initial)) :
    hashed.pc = 4648 ∧
    hashed.getReg .x21 = 544 ∧
    hashed.getReg .x23 = initial.getReg .x11 ∧
    hashed.getReg .x19 = initial.getReg .x15 + 71680 ∧
    hashed.getReg .x8 = initial.getReg .x14 ∧
    hashed.getReg .x24 = initial.getReg .x13 ∧
    hashed.getReg .x25 = initial.getReg .x15 ∧
    hashed.getReg .x27 = 128 := by
  simp only [checkCapHash, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reached
  obtain ⟨afterParents, parReached, rfl⟩ := reached
  let lenState := checkCapLengthState initial
  have lenPC : lenState.pc = 4468 := if_pos isLen
  let copySetup := checkCapCopySetupState lenState
  have csRegs := check_cap_copy_setup_registers lenState lenPC
  let afterCopy := checkCapCopyStepState^[128] copySetup
  have copyEndPC : afterCopy.pc = 4572 :=
    cap_copy_loop_finished 128 (by decide) (by decide) copySetup csRegs.2.2.2.2.2.1
  let parSetup := checkCapParentSetupState afterCopy
  have psRegs := check_cap_parent_setup_registers afterCopy copyEndPC
  have ps22 : parSetup.getReg .x22 = 512 := by
    rw [check_cap_parent_setup_preserves afterCopy .x22 (by simp),
      cap_copy_loop_preserves 128 copySetup .x22 (by decide), csRegs.2.2.2.1]
  have parEnd := cap_parent_loop_finished 127 (by decide) parSetup ps22
    (by rw [psRegs.2.2.2.2.2.1]; rfl) afterParents parReached
  have lenRegs := check_cap_length_registers initial
  have keep (reg : Reg) (hr : reg ∈ [Reg.x8, .x24, .x25, .x26, .x27]) :
      afterParents.getReg reg = (checkCapLengthState initial).getReg reg := by
    have hr1 : reg ∉ [Reg.x10, .x11, .x12, .x14, .x15, .x16, .x17, .x31] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
    have hr2 : reg ∈ [Reg.x8, .x19, .x22, .x24, .x25, .x26, .x27] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp
    have hr3 : reg ∉ [Reg.x6, .x12, .x23, .x28] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [parEnd.2 reg hr1, check_cap_parent_setup_preserves afterCopy reg hr2,
      cap_copy_loop_preserves 128 copySetup reg hr3,
      check_cap_copy_setup_preserves lenState reg hr]
  have keep22 : afterParents.getReg .x22 = 512 := (parEnd.2 .x22 (by decide)).trans ps22
  have keep19 : afterParents.getReg .x19 = initial.getReg .x15 + 71680 := by
    rw [parEnd.2 .x19 (by decide), check_cap_parent_setup_preserves afterCopy .x19 (by simp),
      cap_copy_loop_preserves 128 copySetup .x19 (by decide), csRegs.2.1, lenRegs.2.2.2.1]
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [checkCapRootSetupState, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x23 ≠ .x21),
      MachineState.getReg_setReg_eq (by decide : Reg.x21 ≠ .x0), keep22]; rfl
  · simp only [checkCapRootSetupState, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x23 ≠ .x0), keep .x26 (by simp), lenRegs.1]
  · simp only [checkCapRootSetupState, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x23 ≠ .x19),
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x21 ≠ .x19), keep19]
  · simp only [checkCapRootSetupState, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x23 ≠ .x8),
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x21 ≠ .x8), keep .x8 (by simp), lenRegs.2.2.1]
  · simp only [checkCapRootSetupState, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x23 ≠ .x24),
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x21 ≠ .x24), keep .x24 (by simp), lenRegs.2.1]
  · simp only [checkCapRootSetupState, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x23 ≠ .x25),
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x21 ≠ .x25), keep .x25 (by simp), lenRegs.2.2.2.1]
  · simp only [checkCapRootSetupState, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x23 ≠ .x27),
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x21 ≠ .x27), keep .x27 (by simp), lenRegs.2.2.2.2.1, is128]

/-- `checkCapHash` preserves every memory address outside `[544, 8704)`,
including all input buffers (`commitment`, `indices`, `values`, `proof`). -/
theorem check_cap_hash_support_outside (initial hashed : MachineState)
    (isLen : initial.getReg .x17 = 75776)
    (reached : hashed ∈ support (checkCapHash initial))
    (address : Word) (outside : address.toNat < 544 ∨ 8704 ≤ address.toNat) :
    hashed.getMem address = initial.getMem address := by
  simp only [checkCapHash, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reached
  obtain ⟨afterParents, parReached, rfl⟩ := reached
  let lenState := checkCapLengthState initial
  have lenPC : lenState.pc = 4468 := if_pos isLen
  let copySetup := checkCapCopySetupState lenState
  have csRegs := check_cap_copy_setup_registers lenState lenPC
  let afterCopy := checkCapCopyStepState^[128] copySetup
  have copyEndPC : afterCopy.pc = 4572 :=
    cap_copy_loop_finished 128 (by decide) (by decide) copySetup csRegs.2.2.2.2.2.1
  let parSetup := checkCapParentSetupState afterCopy
  have psRegs := check_cap_parent_setup_registers afterCopy copyEndPC
  change afterParents.getMem address = initial.getMem address
  rw [cap_parent_loop_support_outside 127 (by decide) parSetup
      (by rw [psRegs.2.2.2.2.2.1]; rfl) afterParents parReached address (by omega)]
  change afterCopy.getMem address = initial.getMem address
  rw [cap_copy_loop_outside 128 copySetup address
      (by rw [csRegs.2.2.2.2.1]; decide) (by rw [csRegs.2.2.2.2.1]; change address.toNat < 4608 ∨ 8704 ≤ address.toNat; omega)]
  change copySetup.mem address = initial.mem address
  rw [csRegs.2.2.2.2.2.2, (check_cap_length_registers initial).2.2.2.2.2]

end CommitGolfCandidate
