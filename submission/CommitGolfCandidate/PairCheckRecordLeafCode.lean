-- Pair-heads copy of TwoPermutationPackedRecordLeafCode (stack/check/work/mkcopy.py); edits below are marked PAIR.
import CommitGolfCandidate.PairCheckCheckerSteps
import CommitGolfCandidate.PairCheckNamespaces
import CommitGolfCandidate.TwoPermutationSyscall
import CommitGolfCandidate.TwoPermutationOpeningBlocks

namespace TwoPermutationPrototype.PairCk.Packed.RecordLeaf
open  TwoPermutationPrototype.Packed
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.PairCk.Packed.Checker (pairImage fetch_at)
open TwoPermutationPrototype.RV64
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
attribute [local simp] Opening.getReg_setMem Opening.getReg_setReg MachineState.getReg_setPC
@[local simp] private theorem mem_set_reg (s : MachineState) (r : Reg) (v : Word) :
    (s.setReg r v).mem = s.mem := by cases r <;> rfl

@[local simp] private theorem mem_set_pc (s : MachineState) (v : Word) :
    (s.setPC v).mem = s.mem := rfl

@[local simp] private theorem set_pc_pc (s : MachineState) (pc : Word) :
    (s.setPC pc).pc = pc := rfl

/-- PAIR: the parity branch at words 44–45: `andi t6,t1,1; beq t6,zero,+1796` (to word 494 when even). -/
def branchCode : List Instr := [.ANDI .x31 .x6 1, .BEQ .x31 .x0 1796]

def branched (state : MachineState) : MachineState := branchCode.foldl execInstrBr state

theorem execute_branch (state : MachineState) (pc : state.pc = 0x10b0) (fuel : Nat) :
    execute pairImage (2 + fuel) state false =
      (do let result ← execute pairImage fuel (branched state) false
          return result.charge 2 0) := by
  apply execute_unit_steps (states := fun i => (branchCode.take i).foldl execInstrBr state)
  intro i bounded
  refine ⟨.base (branchCode[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply fetch_at _ (44+i) _ (by omega)
    · interval_cases i <;> simp [branchCode,execInstrBr,pc]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem parity_bit (n : Nat) : (BitVec.ofNat 64 n &&& 1#64) = BitVec.ofNat 64 (n % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.and_one_is_mod]
  rw [Nat.mod_eq_of_lt (by omega : n % 2 < 2^64), Nat.mod_mod_of_dvd n (by decide : 2 ∣ 2^64)]

private theorem zero_register (s : MachineState) : s.getReg .x0 = 0#64 := rfl

private theorem branch_unfold (state : MachineState) :
    branched state =
      let after := (state.setReg .x31 (state.getReg .x6 &&& 1#64)).setPC (state.pc + 4)
      if (after.getReg .x31 == 0#64) = true then after.setPC (after.pc + 1796#64) else after.setPC (after.pc + 4) := by
  simp only [branched, branchCode, List.foldl, execInstrBr, zero_register,
    show signExtend12 (1 : BitVec 12) = 1#64 by decide, show signExtend13 (1796 : BitVec 13) = 1796#64 by decide]

theorem branched_register (state : MachineState) (reg : Reg) (other : reg ≠ .x31) :
    (branched state).getReg reg = state.getReg reg := by
  rw [branch_unfold]
  dsimp only
  rw [apply_ite (fun s : MachineState => s.getReg reg)]
  simp [Ne.symm other]

theorem branched_mem (state : MachineState) : (branched state).mem = state.mem := by
  rw [branch_unfold]
  dsimp only
  rw [apply_ite (fun s : MachineState => s.mem)]
  simp

theorem branched_pc (state : MachineState) (pc : state.pc = 0x10b0) (index : Nat)
    (node : state.getReg .x6 = BitVec.ofNat 64 index) :
    (branched state).pc = if index % 2 = 0 then BitVec.ofNat 64 (4096+4*494) else 0x10b8 := by
  rw [branch_unfold]
  dsimp only
  rw [apply_ite (fun s : MachineState => s.pc)]
  simp only [MachineState.getReg_setPC, Opening.getReg_setReg, node, parity_bit, set_pc_pc, pc]
  by_cases even : index % 2 = 0
  · simp [even] <;> decide
  · have odd : index % 2 = 1 := by omega
    simp [odd] <;> decide

/-- PAIR: A′'s words 44–45 now sit at 46–47. -/
def firstPreamble : List Instr := [.ADDI .x12 .x10 8, .ADDI .x10 .x10 40]

/-- PAIR: A′'s words 47–48 and 51–56 (the two no-ops at 49–50 are gone) now sit at 49–56. -/
def secondPreamble : List Instr :=
  [.ADDI .x10 .x10 56, .ADDI .x31 .x28 96,
   .SD .x10 .x31 0, .LD .x31 .x4 0, .SD .x10 .x31 8,
   .LD .x31 .x4 8, .SD .x10 .x31 16, .ADDI .x12 .x23 0]

def firstPrefix (state : MachineState) (count : Nat) : MachineState :=
  (firstPreamble.take count).foldl execInstrBr state

def secondPrefix (state : MachineState) (count : Nat) : MachineState :=
  (secondPreamble.take count).foldl execInstrBr state

theorem execute_first_prefix (state : MachineState) (pc : state.pc = 0x10b8) (fuel : Nat) :
    execute pairImage (2 + fuel) state false =
      (do let result ← execute pairImage fuel (firstPrefix state 2) false
          return result.charge 2 0) := by
  apply execute_unit_steps (states := firstPrefix state)
  intro i bounded
  refine ⟨.base (firstPreamble[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply fetch_at _ (46+i) _ (by omega)
    · interval_cases i <;> simp [firstPrefix,firstPreamble,execInstrBr,pc]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem execute_second_prefix (state : MachineState) (pc : state.pc = 0x10c4) (fuel : Nat)
    (tagDst : accessValid (state.getReg .x10 + 56#64) 8 = true)
    (saltDst : accessValid (state.getReg .x10 + 64#64) 8 = true)
    (saltDstTail : accessValid (state.getReg .x10 + 72#64) 8 = true)
    (saltSrc : accessValid (state.getReg .x4) 8 = true)
    (saltSrcTail : accessValid (state.getReg .x4 + 8#64) 8 = true) :
    execute pairImage (8 + fuel) state false =
      (do let result ← execute pairImage fuel (secondPrefix state 8) false
          return result.charge 8 0) := by
  apply execute_unit_steps (states := secondPrefix state)
  intro i bounded
  refine ⟨.base (secondPreamble[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply fetch_at _ (49+i) _ (by omega)
    · interval_cases i <;> simp [secondPrefix,secondPreamble,execInstrBr,pc]
    · interval_cases i <;> rfl
  · interval_cases i <;>
      simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend12,
        secondPrefix,secondPreamble,BitVec.add_assoc,
        show 56#64+8#64=64#64 by decide,show 56#64+16#64=72#64 by decide,
        tagDst,saltDst,saltDstTail,saltSrc,saltSrcTail] <;> assumption
  · interval_cases i <;> rfl

theorem checker_first_ecall (state : MachineState) (pc : state.pc = 0x10c0) :
    fetch pairImage state = some (.base .ECALL) :=
  fetch_at state 48 .ECALL (by decide) pc rfl

theorem checker_second_ecall (state : MachineState) (pc : state.pc = 0x10e4) :
    fetch pairImage state = some (.base .ECALL) :=
  fetch_at state 57 .ECALL (by decide) pc rfl

def checkerNonce (state : MachineState) : Words 2 := fun i =>
  if i.val = 0 then state.getMem (state.getReg .x4) else state.getMem (state.getReg .x4+8#64)

def secondHeaderMemory (state : MachineState) : MachineState :=
  let tag := state.getReg .x28+96#64
  let afterTag := state.setMem (state.getReg .x10+56#64) tag
  let afterNonce := afterTag.setMem (state.getReg .x10+64#64) (checkerNonce state 0)
  afterNonce.setMem (state.getReg .x10+72#64) (checkerNonce state 1)

theorem first_prefix_post (state : MachineState) :
    let after := firstPrefix state 2
    after.mem = state.mem ∧ after.getReg .x10 = state.getReg .x10 + 40 ∧
    after.getReg .x12 = state.getReg .x10 + 8 ∧ after.pc = state.pc + 8 ∧
    after.getReg .x5 = state.getReg .x5 ∧ after.getReg .x11 = state.getReg .x11 ∧
    after.getReg .x13 = state.getReg .x13 := by
  simp [firstPrefix,firstPreamble,execInstrBr,signExtend12,BitVec.add_assoc] <;> rfl

theorem second_prefix_post (state : MachineState)
    (d0 : state.getReg .x4 ≠ state.getReg .x10+56#64)
    (e0 : state.getReg .x4+8#64 ≠ state.getReg .x10+56#64)
    (e8 : state.getReg .x4+8#64 ≠ state.getReg .x10+64#64) :
    let after := secondPrefix state 8
    after.mem = (secondHeaderMemory state).mem ∧
    after.getReg .x10 = state.getReg .x10+56#64 ∧ after.getReg .x12 = state.getReg .x23 ∧
    after.pc = state.pc + 32 ∧ after.getReg .x5 = state.getReg .x5 ∧
    after.getReg .x11 = state.getReg .x11 ∧ after.getReg .x13 = state.getReg .x13 := by
  simp [secondPrefix,secondPreamble,secondHeaderMemory,checkerNonce,execInstrBr,signExtend12,
    MachineState.setPC,MachineState.setMem,MachineState.getMem, MachineState.getReg,
    MachineState.setReg,BitVec.add_assoc] at d0 e0 e8 ⊢
  simp [d0,e0,e8]

theorem first_prefix_register (state : MachineState) (reg : Reg)
    (a : reg ≠ .x10) (b : reg ≠ .x12) :
    (firstPrefix state 2).getReg reg = state.getReg reg := by
  simp [firstPrefix,firstPreamble,execInstrBr,Ne.symm a,Ne.symm b]

theorem second_prefix_register (state : MachineState) (reg : Reg)
    (a : reg ≠ .x10) (b : reg ≠ .x12) (c : reg ≠ .x31) :
    (secondPrefix state 8).getReg reg = state.getReg reg := by
  simp [secondPrefix,secondPreamble,execInstrBr,Ne.symm a,Ne.symm b,Ne.symm c]

end TwoPermutationPrototype.PairCk.Packed.RecordLeaf
