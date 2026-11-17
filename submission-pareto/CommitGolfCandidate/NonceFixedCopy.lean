import CommitGolfCandidate.NonceCopyProcedure

/-! The fixed-size opening helper copies three nonce words with immediate offsets.
Loads and stores remain interleaved, including for overlapping proof buffers. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

private def fixedCopyInstructions : List Instr :=
  [.LD .x6 .x23 0, .SD .x25 .x6 0,
   .LD .x6 .x23 8, .SD .x25 .x6 8,
   .LD .x6 .x23 16, .SD .x25 .x6 16,
   .ADDI .x23 .x23 24, .ADDI .x25 .x25 24, .ADDI .x28 .x0 0,
   .JALR .x0 .x1 0]

private def fixedCopyPrefix (state : MachineState) (count : Nat) : MachineState :=
  (fixedCopyInstructions.take count).foldl execInstrBr (state.setPC 4648)

private def copyWordReference (state : MachineState) : MachineState :=
  NonceWordCopy.copyPrefix false state 6

private def copyWordLinear (state : MachineState) : MachineState :=
  let word := state.getMem (state.getReg .x23)
  let copied := (state.setReg .x6 word).setMem (state.getReg .x25) word
  let advanced := (copied.setReg .x23 (state.getReg .x23 + 8)).setReg .x25 (state.getReg .x25 + 8)
  (advanced.setReg .x28 (state.getReg .x28 - 1)).setPC 0

private theorem setPC_overwrite (state : MachineState) (before after : Word) :
    (state.setPC before).setPC after = state.setPC after := rfl

private theorem copyWord_same_data (state : MachineState) :
    (copyWordReference state).setPC 0 = copyWordLinear state := by
  unfold copyWordReference
  rw [show 6 = 5 + 1 by rfl, NonceWordCopy.copy_prefix_next _ _ _ (by decide)]
  change (execInstrBr (NonceWordCopy.copyPrefix false state 5) (.BNE .x28 .x0 8172)).setPC 0 = _
  have branch (current : MachineState) :
      (execInstrBr current (.BNE .x28 .x0 8172)).setPC 0 = current.setPC 0 := by
    simp only [execInstrBr]
    split <;> exact setPC_overwrite _ _ _
  rw [branch]
  simp [copyWordLinear, NonceWordCopy.copyPrefix, NonceWordCopy.copyInstructions,
    execInstrBr, MachineState.getMem, MachineState.setPC, MachineState.setMem,
    MachineState.getReg, MachineState.setReg, signExtend12, BitVec.sub_eq_add_neg]

private theorem copyWord_pc (state : MachineState) (pc : Word) :
    copyWordLinear (state.setPC pc) = copyWordLinear state := by
  cases state
  rfl

private theorem copyReturn_pc (state : MachineState) (pc : Word) :
    NonceCopyProcedure.returnState (state.setPC pc) = NonceCopyProcedure.returnState state := by
  cases state
  rfl

private theorem copyWord_ignores_pc (state : MachineState) :
    copyWordLinear (copyWordReference state) = copyWordLinear (copyWordLinear state) :=
  (copyWord_pc _ 0).symm.trans (congrArg copyWordLinear (copyWord_same_data state))

private theorem copyReturn_ignores_pc (state : MachineState) :
    NonceCopyProcedure.returnState (copyWordReference state) =
      NonceCopyProcedure.returnState (copyWordLinear state) :=
  (copyReturn_pc _ 0).symm.trans
    (congrArg NonceCopyProcedure.returnState (copyWord_same_data state))

private theorem fixedCopySame (state : MachineState) (count : state.getReg .x28 = 3) :
    fixedCopyPrefix state 10 = NonceCopyProcedure.returnState
      (capCountedRun (fun current => NonceWordCopy.copyPrefix false current 6) 3 state) := by
  change _ = NonceCopyProcedure.returnState
    (copyWordReference (copyWordReference (copyWordReference state)))
  simp only [copyReturn_ignores_pc, copyWord_ignores_pc]
  simp only [fixedCopyPrefix, fixedCopyInstructions, NonceCopyProcedure.returnState,
    copyWordLinear, List.take, List.foldl, execInstrBr, MachineState.getMem, MachineState.setPC,
    MachineState.setMem, MachineState.getReg, MachineState.setReg,
    show signExtend12 (0 : BitVec 12) = (0 : Word) by decide,
    show signExtend12 (8 : BitVec 12) = (8 : Word) by decide,
    show signExtend12 (16 : BitVec 12) = (16 : Word) by decide,
    show signExtend12 (24 : BitVec 12) = (24 : Word) by decide,
    BitVec.zero_add, BitVec.add_assoc] at count ⊢
  simp [count, BitVec.add_assoc]
  funext reg
  cases reg <;> simp

private theorem fixedCopyAccess (base offset : Nat) (aligned : base % 8 = 0)
    (window : base + 24 ≤ MEMORY_BYTES) (small : offset ≤ 16)
    (offsetAligned : offset % 8 = 0) :
    accessValid (BitVec.ofNat 64 base + BitVec.ofNat 64 offset) 8 = true := by
  have fits : base+offset < 2^64 := by
    norm_num [MEMORY_BYTES] at window
    omega
  rw [← BitVec.ofNat_add]
  simp only [accessValid, rangeValid, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits,
    Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem nonce_fixed_copy_execute (source target : Nat) (state : MachineState)
    (ready : NonceCopyReady.Forward 4620 source target 3 3 state)
    (fuel : Nat) (coins : Bool) :
    execute nonceCompactImage (10+fuel) (state.setPC 4648) coins =
      (do let result ← execute nonceCompactImage fuel
            (NonceCopyProcedure.returnState
              (capCountedRun (fun current => NonceWordCopy.copyPrefix false current 6) 3 state)) coins
          return result.charge 10 0) := by
  have count : state.getReg .x28 = 3 := ready.counter
  have src : state.getReg .x23 = BitVec.ofNat 64 source := by simpa using ready.source
  have dst : state.getReg .x25 = BitVec.ofNat 64 target := by simpa using ready.target
  have sourceAccess (offset : Nat) (small : offset ≤ 16) (aligned : offset % 8 = 0) :
      accessValid (state.getReg .x23 + BitVec.ofNat 64 offset) 8 = true := by
    rw [src]
    exact fixedCopyAccess source offset ready.source_aligned ready.source_window small aligned
  have targetAccess (offset : Nat) (small : offset ≤ 16) (aligned : offset % 8 = 0) :
      accessValid (state.getReg .x25 + BitVec.ofNat 64 offset) 8 = true := by
    rw [dst]
    exact fixedCopyAccess target offset ready.target_aligned ready.target_window small aligned
  have s0 : accessValid (state.getReg .x23) 8 = true := by simpa using sourceAccess 0 (by decide) (by decide)
  have t0 : accessValid (state.getReg .x25) 8 = true := by simpa using targetAccess 0 (by decide) (by decide)
  have s8 := sourceAccess 8 (by decide) (by decide)
  have t8 := targetAccess 8 (by decide) (by decide)
  have s16 := sourceAccess 16 (by decide) (by decide)
  have t16 := targetAccess 16 (by decide) (by decide)
  rw [← fixedCopySame state count]
  apply execute_unit_steps (states := fixedCopyPrefix state)
  intro index bounded
  refine ⟨.base ((fixedCopyInstructions[index]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply cap_image_fetch _ _ (138+index) _ (by omega)
    · interval_cases index <;> rfl
    · interval_cases index <;> rfl
  · simp only [MachineState.getReg] at s0 t0 s8 t8 s16 t16
    interval_cases index <;>
      simp [fixedCopyPrefix, fixedCopyInstructions, ordinaryStep, memoryArgumentsValid,
        memAccess, execInstrBr, signExtend12, MachineState.setPC, MachineState.setReg,
        MachineState.setMem, MachineState.getReg, s0, t0, s8, t8, s16, t16] <;> rfl
  · interval_cases index <;> rfl

end CommitGolfCandidate
