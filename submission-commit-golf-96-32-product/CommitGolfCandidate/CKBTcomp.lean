import CommitGolfCandidate.LateNormalPad
import CommitGolfCandidate.CKBHalf

/-! The A96 truncating compression adapter `tcomp` (check words 438..457), called by
`jal x31 ->438` from words 59 (normal path), 542 and 626 (batch path). Words 438..452 are the padded
adapter's words 181..195; then `andi x7,x9,1; srli x9,x9,1; beq x7,x0,+8; sh x0,30(x12); jalr x0,0(x31)`:
bit 0 of x9 selects the 240-bit store, and x9 shifts right by one. -/
namespace CommitGolfCandidate.Late.Check.Normal
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 12000
set_option maxHeartbeats 1500000

theorem tcomp_fetch (state : MachineState) (index : Nat) (inside : index < 15)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * (438 + index))) :
    fetch (checkerImage) state =
      some (.base ((paddingInstructions[index]?).getD .EBREAK)) := by
  have pcNat : state.pc.toNat = 4096 + 4 * (438 + index) := by
    rw [pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  rw [fetch, pcNat, if_pos (by omega)]
  have quotient : (4096 + 4 * (438 + index) - 4096) / 4 = 438 + index := by omega
  rw [quotient]
  interval_cases index <;> rfl

private theorem word_fetch (state : MachineState) (index : Nat)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * index)) (inside : index < 814) :
    fetch (checkerImage) state = (checkerImage.code[index]?).bind decodeInstruction := by
  have pcNat : state.pc.toNat = 4096 + 4 * index := by
    rw [pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  rw [fetch, pcNat, if_pos (by omega)]
  have quotient : (4096 + 4 * index - 4096) / 4 = index := by omega
  rw [quotient]
  cases checkerImage.code[index]? <;> rfl

/-- The tail after the 15 adapter words: `andi`, `srli`, `beq`, optional `sh`, `jalr`. -/
def tcompTailState (s : MachineState) : MachineState :=
  let b := s.getReg .x9 &&& 1
  let base := (s.setReg .x7 b).setReg .x9 (s.getReg .x9 >>> 1)
  let stored := if b = 0 then base else base.setHalfword (s.getReg .x12 + 30) 0
  stored.setPC ((s.getReg .x31 + signExtend12 0) &&& ~~~1#64)

def tcompTailSteps (s : MachineState) : Nat := if s.getReg .x9 &&& 1 = 0 then 4 else 5

private theorem set_pc_set_reg (s : MachineState) (r : Reg) (v p : Word) :
    (s.setReg r v).setPC p = (s.setPC p).setReg r v := by cases r <;> rfl

private theorem set_pc_set_half (s : MachineState) (a : Word) (h : BitVec 16) (p : Word) :
    (s.setHalfword a h).setPC p = (s.setPC p).setHalfword a h := rfl

theorem tcomp_tail (s : MachineState) (pc : s.pc = BitVec.ofNat 64 (4096 + 4 * 453))
    (dest : rangeValid (s.getReg .x12) 32 = true) (destAligned : (s.getReg .x12).toNat % 8 = 0)
    (fuel : Nat) (allowCoins : Bool) :
    execute (checkerImage) (tcompTailSteps s + fuel) s allowCoins =
      (do let result ← execute (checkerImage) fuel (tcompTailState s) allowCoins
          return result.charge (tcompTailSteps s) 0) := by
  let s1 := (s.setReg .x7 (s.getReg .x9 &&& 1)).setPC (s.pc + 4)
  let s2 := (s1.setReg .x9 (s1.getReg .x9 >>> 1)).setPC (s1.pc + 4)
  have r7 : s2.getReg .x7 = s.getReg .x9 &&& 1 := by simp [s2, s1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq]
  have r12 : s2.getReg .x12 = s.getReg .x12 := by simp [s2, s1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne]
  have p1 : s1.pc = BitVec.ofNat 64 (4096 + 4 * 454) := by change s.pc + 4 = _; rw [pc]; rfl
  have p2 : s2.pc = BitVec.ofNat 64 (4096 + 4 * 455) := by change s1.pc + 4 = _; rw [p1]; rfl
  have f0 : fetch checkerImage s = some (.base (.ANDI .x7 .x9 1)) := by rw [word_fetch s 453 pc (by decide)]; rfl
  have f1 : fetch checkerImage s1 = some (.base (.SRLI .x9 .x9 1)) := by rw [word_fetch s1 454 p1 (by decide)]; rfl
  have f2 : fetch checkerImage s2 = some (.base (.BEQ .x7 .x0 8)) := by rw [word_fetch s2 455 p2 (by decide)]; rfl
  have e0 : ordinaryStep s (.base (.ANDI .x7 .x9 1)) = some s1 := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, s1]
  have e1 : ordinaryStep s1 (.base (.SRLI .x9 .x9 1)) = some s2 := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, s2]
  have jalr (t : MachineState) (pt : t.pc = BitVec.ofNat 64 (4096 + 4 * 457)) :
      fetch checkerImage t = some (.base (.JALR .x0 .x31 0)) ∧
      ordinaryStep t (.base (.JALR .x0 .x31 0)) = some (t.setPC ((t.getReg .x31 + signExtend12 0) &&& ~~~1#64)) := by
    refine ⟨by rw [word_fetch t 457 pt (by decide)]; rfl, ?_⟩
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.setReg]
  by_cases zero : s.getReg .x9 &&& 1 = 0
  · -- not truncated: beq taken to 457
    let s3 := s2.setPC (s2.pc + signExtend13 8)
    have p3 : s3.pc = BitVec.ofNat 64 (4096 + 4 * 457) := by change s2.pc + signExtend13 8 = _; rw [p2]; rfl
    have e2 : ordinaryStep s2 (.base (.BEQ .x7 .x0 8)) = some s3 := by
      have : (s2.getReg .x7 == s2.getReg .x0) = true := by rw [r7, zero]; rfl
      simp only [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, this, if_true]; rfl
    obtain ⟨f3, e3⟩ := jalr s3 p3
    have steps : tcompTailSteps s = 4 := if_pos zero
    rw [steps, show 4 + fuel = fuel + 1 + 1 + 1 + 1 by omega,
      execute_ordinary_step _ _ _ _ _ _ f0 e0, execute_ordinary_step _ _ _ _ _ _ f1 e1,
      execute_ordinary_step _ _ _ _ _ _ f2 e2, execute_ordinary_step _ _ _ _ _ _ f3 e3]
    have final : s3.setPC ((s3.getReg .x31 + signExtend12 0) &&& ~~~1#64) = tcompTailState s := by
      simp only [tcompTailState]
      rw [if_pos zero]
      rfl
    rw [final]
    simp only [instructionCycles, bind_assoc, pure_bind, bind_pure_comp, Functor.map_map]
    congr 1
    funext r
    cases r
    simp only [Execution.charge, Execution.mk.injEq, true_and]
    omega
  · -- truncated: beq falls through to the store at 456
    let s3 := s2.setPC (s2.pc + 4)
    have p3 : s3.pc = BitVec.ofNat 64 (4096 + 4 * 456) := by change s2.pc + 4 = _; rw [p2]; rfl
    have e2 : ordinaryStep s2 (.base (.BEQ .x7 .x0 8)) = some s3 := by
      have : (s2.getReg .x7 == s2.getReg .x0) = false := by
        rw [r7]; simpa [MachineState.getReg] using zero
      simp only [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, this]; rfl
    have f3 : fetch checkerImage s3 = some (.base (.SH .x12 .x0 30)) := by rw [word_fetch s3 456 p3 (by decide)]; rfl
    have r12' : s3.getReg .x12 = s.getReg .x12 := r12
    have destOk : accessValid (s3.getReg .x12 + signExtend12 30) 2 = true := by
      rw [r12']
      have nat : s.getReg .x12 = BitVec.ofNat 64 (s.getReg .x12).toNat := by simp
      rw [nat]
      have bound : (s.getReg .x12).toNat + 32 ≤ MEMORY_BYTES := by simpa [rangeValid] using dest
      exact CKBHalf.half_access_valid _ 30 (by omega) (by omega) (by decide)
    let s4 := (s3.setHalfword (s3.getReg .x12 + signExtend12 30) ((s3.getReg .x0).truncate 16)).setPC (s3.pc + 4)
    have e3 : ordinaryStep s3 (.base (.SH .x12 .x0 30)) = some s4 := by
      simp only [ordinaryStep, memoryArgumentsValid, memAccess, destOk, ↓reduceIte]; rfl
    have p4 : s4.pc = BitVec.ofNat 64 (4096 + 4 * 457) := by change s3.pc + 4 = _; rw [p3]; rfl
    obtain ⟨f4, e4⟩ := jalr s4 p4
    have steps : tcompTailSteps s = 5 := if_neg zero
    rw [steps, show 5 + fuel = fuel + 1 + 1 + 1 + 1 + 1 by omega,
      execute_ordinary_step _ _ _ _ _ _ f0 e0, execute_ordinary_step _ _ _ _ _ _ f1 e1,
      execute_ordinary_step _ _ _ _ _ _ f2 e2, execute_ordinary_step _ _ _ _ _ _ f3 e3,
      execute_ordinary_step _ _ _ _ _ _ f4 e4]
    have final : s4.setPC ((s4.getReg .x31 + signExtend12 0) &&& ~~~1#64) = tcompTailState s := by
      simp only [tcompTailState]
      rw [if_neg zero]
      rfl
    rw [final]
    simp only [instructionCycles, bind_assoc, pure_bind, bind_pure_comp, Functor.map_map]
    congr 1
    funext r
    cases r
    simp only [Execution.charge, Execution.mk.injEq, true_and]
    omega

/-- The adapter's effect from the caller's `jal x31 ->438` (same hypotheses as `padding_call`). -/
theorem tcomp_call (state : MachineState) (index : Nat)
    (location : index = 59 ∨ index = 542 ∨ index = 626)
    (pc : state.pc = BitVec.ofNat 64 (4096+4*index))
    (syscall : state.getReg .x5 = 0) (compression : state.getReg .x13 = 0)
    (sourceValid : rangeValid (state.getReg .x10) 96 = true)
    (destinationValid : rangeValid (state.getReg .x12) 32 = true)
    (sourceAligned : (state.getReg .x10).toNat % 8 = 0)
    (destinationAligned : (state.getReg .x12).toNat % 8 = 0)
    (beforePadding : (state.getReg .x12).toNat+32 ≤ (state.getReg .x10).toNat+64)
    (fuel : Nat) (allowCoins : Bool) :
    execute (checkerImage) (tcompSteps state+fuel) state allowCoins =
      (do let answer ← World.query
            (.inr (.inl (padInput (readBuffer state (state.getReg .x10).toNat 64))))
          let result ← execute (checkerImage) fuel (tcompState state answer) allowCoins
          return result.charge (tcompSteps state+7) 1) := by
  let instruction := Instr.JAL .x31 (BitVec.ofInt 21 (4*((438 : Int)-index)))
  let next := (state.setReg .x31 (state.pc+4)).setPC (BitVec.ofNat 64 (4096+4*438))
  have fetched : fetch (checkerImage) state = some (.base instruction) := by
    rcases location with rfl | rfl | rfl <;> simp only [fetch, pc] <;> rfl
  have stepped : ordinaryStep state (.base instruction) = some next := by
    rcases location with rfl | rfl | rfl <;>
      simp [instruction, next, ordinaryStep, memoryArgumentsValid,
        memAccess, execInstrBr, signExtend21, pc, MachineState.setPC]
  have alignedReturn : (state.pc+4) &&& ~~~1 = state.pc+4 := by
    rcases location with rfl | rfl | rfl <;> rw [pc] <;> rfl
  have separate := padding_output_separate (state.getReg .x10) (state.getReg .x12)
    sourceValid destinationValid beforePadding
  -- register facts of `next`
  have nreg (r : Reg) (ne : r ≠ .x31) : next.getReg r = state.getReg r := by
    simp only [next, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm ne)]
  have n5 := (nreg .x5 (by decide)).trans syscall
  have n13 := (nreg .x13 (by decide)).trans compression
  have n10 := nreg .x10 (by decide)
  have n12 := nreg .x12 (by decide)
  have sourceWords := padding_source_words (state.getReg .x10) sourceValid sourceAligned
  -- the 9 setup words
  have setup (remaining : Nat) :
      execute (checkerImage) (9+remaining) next allowCoins =
        (do let result ← execute (checkerImage) remaining
              (paddingSetupPrefix next 9) allowCoins
            return result.charge 9 0) := by
    apply execute_unit_steps (states := paddingSetupPrefix next)
    intro i hi
    refine ⟨.base ((paddingSetupInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
    · have fetched := tcomp_fetch (paddingSetupPrefix next i) i (by omega) (by
        interval_cases i <;>
          simp [next, paddingSetupPrefix, paddingSetupInstructions, execInstrBr,
            MachineState.setPC, BitVec.add_assoc, Nat.mul_add, ← BitVec.ofNat_add, Nat.add_assoc])
      interval_cases i <;> exact fetched
    · have source := padding_setup_register next i (by omega) .x10
        (by decide) (by decide) (by decide) (by decide) (by decide)
      rw [n10] at source
      have s0 := sourceWords ⟨0, by decide⟩
      have s1 := sourceWords ⟨1, by decide⟩
      have s2 := sourceWords ⟨2, by decide⟩
      have s3 := sourceWords ⟨3, by decide⟩
      have valid : memoryArgumentsValid (paddingSetupPrefix next i)
          ((paddingSetupInstructions[i]?).getD .EBREAK) = true := by
        interval_cases i <;>
          simp only [paddingSetupInstructions, List.getElem?_cons_zero, List.getElem?_cons_succ,
            Option.getD_some, memoryArgumentsValid, memAccess, source, signExtend12] <;>
          first | exact s0 | exact s1 | exact s2 | exact s3 | rfl
      interval_cases i <;>
        simp only [paddingSetupInstructions, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.getD_some] at valid ⊢ <;>
        simp only [ordinaryStep, valid, ↓reduceIte] <;> rfl
    · interval_cases i <;> rfl
  let ready := paddingSetupPrefix next 9
  have readyPC : ready.pc = BitVec.ofNat 64 (4096+4*(438+9)) := by
    simp [ready, padding_setup_shape, next, MachineState.setPC, Nat.mul_add, ← BitVec.ofNat_add, Nat.add_assoc]
  have fetchedCall : fetch (checkerImage) ready = some (.base .ECALL) :=
    tcomp_fetch ready 9 (by decide) readyPC
  have call : ready.getReg .x5 = 0 :=
    (padding_setup_register next 9 (by decide) .x5
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans n5
  have destination : ready.getReg .x12 = state.getReg .x12 :=
    (padding_setup_register next 9 (by decide) .x12
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans n12
  have input := padding_setup_input next n13 (by rw [n10]; exact sourceValid) (by rw [n12]; exact destinationValid)
    (by rw [n10]; exact sourceAligned) (by rw [n12]; exact destinationAligned)
  rw [n10] at input
  -- the 5 restoring words (448..452)
  have finish (answer : BitVec 256) (remaining : Nat) :
      execute (checkerImage) (5+remaining)
          (writeBits ready (state.getReg .x12) answer) allowCoins =
        (do let result ← execute (checkerImage) remaining
              (paddingFinishPrefix (writeBits ready (state.getReg .x12) answer) 5) allowCoins
            return result.charge 5 0) := by
    let written := writeBits ready (state.getReg .x12) answer
    apply execute_unit_steps (states := paddingFinishPrefix written)
    intro i hi
    refine ⟨.base ((paddingFinishInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
    · have fetched := tcomp_fetch (paddingFinishPrefix written i) (10+i) (by omega) (by
        have writtenPC : written.pc = BitVec.ofNat 64 (4096+4*(438+10)) := by
          change ready.pc+4 = _
          rw [readyPC]
          erw [← BitVec.ofNat_add]
        interval_cases i <;>
          simp [paddingFinishPrefix, paddingFinishInstructions, execInstrBr,
            MachineState.setPC, writtenPC, Nat.mul_add, ← BitVec.ofNat_add, Nat.add_assoc])
      interval_cases i <;> exact fetched
    · have source : (paddingFinishPrefix written i).getReg .x10 = state.getReg .x10 := by
        rw [padding_finish_register _ _ (by omega) _ (by decide), writeBits_register]
        exact (padding_setup_register next 9 (by decide) .x10
          (by decide) (by decide) (by decide) (by decide) (by decide)).trans n10
      have s0 := sourceWords ⟨0, by decide⟩
      have s1 := sourceWords ⟨1, by decide⟩
      have s2 := sourceWords ⟨2, by decide⟩
      have s3 := sourceWords ⟨3, by decide⟩
      have valid : memoryArgumentsValid (paddingFinishPrefix written i)
          ((paddingFinishInstructions[i]?).getD .EBREAK) = true := by
        interval_cases i <;>
          simp only [paddingFinishInstructions, List.getElem?_cons_zero, List.getElem?_cons_succ,
            Option.getD_some, memoryArgumentsValid, memAccess, source, signExtend12] <;>
          first | exact s0 | exact s1 | exact s2 | exact s3 | rfl
      interval_cases i <;>
        simp only [paddingFinishInstructions, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.getD_some] at valid ⊢ <;>
        simp only [ordinaryStep, valid, ↓reduceIte] <;> rfl
    · interval_cases i <;> rfl
  -- relate the 5-word prefix to the padded adapter's effect
  have five (answer : BitVec 256) :
      let F := paddingFinishPrefix (writeBits ready (state.getReg .x12) answer) 5
      F.setPC ((F.getReg .x31 + signExtend12 0) &&& ~~~1#64) = paddedCompressionState state answer ∧
      F.pc = BitVec.ofNat 64 (4096+4*453) := by
    intro F
    have six : paddingFinishPrefix (writeBits ready (state.getReg .x12) answer) 6 =
        F.setPC ((F.getReg .x31 + signExtend12 0) &&& ~~~1#64) := by
      simp only [F, paddingFinishPrefix, paddingFinishInstructions, List.take, List.foldl]
      simp only [execInstrBr, MachineState.setReg]
    refine ⟨six.symm.trans (padding_finished state _ answer alignedReturn separate), ?_⟩
    have writtenPC : (writeBits ready (state.getReg .x12) answer).pc = BitVec.ofNat 64 (4096+4*(438+10)) := by
      change ready.pc+4 = _
      rw [readyPC]
      erw [← BitVec.ofNat_add]
    simp [F, paddingFinishPrefix, paddingFinishInstructions, execInstrBr, MachineState.setPC, writtenPC,
      ← BitVec.ofNat_add]
  have regsF (answer : BitVec 256) (r : Reg) (h9 : r = .x9 ∨ r = .x12) :
      (paddingFinishPrefix (writeBits ready (state.getReg .x12) answer) 5).getReg r = state.getReg r := by
    have e := congrArg (fun t : MachineState => t.getReg r) (five answer).1
    simp only [MachineState.getReg_setPC] at e
    rw [e]
    rcases h9 with rfl | rfl <;>
      exact padded_compression_register state answer _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  let tailN := if tcompBit state = 0 then 4 else 5
  have tailF (answer : BitVec 256) :
      tcompTailSteps (paddingFinishPrefix (writeBits ready (state.getReg .x12) answer) 5) = tailN := by
    rw [tcompTailSteps, regsF answer .x9 (Or.inl rfl)]; rfl
  have total : tcompSteps state + fuel = (9 + ((5 + (tailN + fuel)) + 1)) + 1 := by
    simp only [tcompSteps, tailN]; split <;> omega
  rw [total, execute_ordinary_step _ _ _ _ _ _ fetched stepped, setup, execute, fetchedCall, if_pos call, input]
  simp only [writeOracleAnswer, destination, bind_assoc, pure_bind]
  have destination' : (paddingSetupPrefix next 9).getReg .x12 = state.getReg .x12 := destination
  simp only [destination']
  apply congrArg (fun continuation =>
    (liftM (World.query
      (.inr (.inl (padInput (readBuffer state (state.getReg .x10).toNat 64))))) :
      OracleComp World (BitVec 256)) >>= continuation)
  funext answer
  change BitVec 256 at answer
  obtain ⟨padded, fpc⟩ := five answer
  have destF : rangeValid ((paddingFinishPrefix (writeBits ready (state.getReg .x12) answer) 5).getReg .x12) 32 = true := by
    rw [regsF answer .x12 (Or.inr rfl)]; exact destinationValid
  have alignF : ((paddingFinishPrefix (writeBits ready (state.getReg .x12) answer) 5).getReg .x12).toNat % 8 = 0 := by
    rw [regsF answer .x12 (Or.inr rfl)]; exact destinationAligned
  have tail := tcomp_tail _ fpc destF alignF fuel allowCoins
  rw [tailF answer] at tail
  have state_eq : tcompTailState (paddingFinishPrefix (writeBits ready (state.getReg .x12) answer) 5) =
      tcompState state answer := by
    unfold tcompTailState tcompState
    rw [← padded]
    simp only [MachineState.getReg_setPC, regsF answer .x9 (Or.inl rfl), regsF answer .x12 (Or.inr rfl), tcompBit]
    by_cases h : state.getReg .x9 &&& 1 = 0
    · simp only [h, ↓reduceIte]
      rw [set_pc_set_reg, set_pc_set_reg]
    · simp only [h, ↓reduceIte]
      rw [set_pc_set_half, set_pc_set_reg, set_pc_set_reg]
  have fin := finish answer (tailN + fuel)
  simp only [ready] at fin
  erw [fin, tail, state_eq]
  simp only [bind_assoc, pure_bind, bind_pure_comp, Functor.map_map]
  congr 1
  funext r
  cases r
  simp only [Execution.charge, Execution.mk.injEq, true_and, oracleCycles, COMPRESSION_CYCLES, tcompSteps, tailN]
  have jalCost : instructionCycles (Instruction.base instruction) = 1 := rfl
  rw [jalCost]
  constructor
  · split <;> omega
  · omega

end CommitGolfCandidate.Late.Check.Normal
