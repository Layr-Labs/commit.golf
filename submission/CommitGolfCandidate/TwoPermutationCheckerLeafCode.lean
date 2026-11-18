import CommitGolfCandidate.TwoPermutationCheckerImage
import CommitGolfCandidate.TwoPermutationSyscall
import CommitGolfCandidate.TwoPermutationOpeningBlocks
import CommitGolfCandidate.OverlapInputs

namespace TwoPermutationPrototype.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64
attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[local simp] private theorem changed_pc (s : MachineState) (pc : Word) :
    (s.setPC pc).pc = pc := rfl

/-- The backward-compatible entry address dispatches to the leaf at word 221. -/
def firstPreamble : List Instr :=
  [.JAL .x0 656, .SD .x10 .x0 32, .ADDI .x10 .x10 32, .ADDI .x12 .x23 0]

/-- Build the second input in the opened value's consumed prefix. The first reply
is in digest scratch, so its 200-byte write cannot damage an adjacent entry. -/
def secondPreamble : List Instr :=
  [.ADDI .x31 .x28 96, .SD .x10 .x31 64,
   .LD .x31 .x23 168, .SD .x10 .x31 72, .LD .x31 .x23 176, .SD .x10 .x31 80,
   .LD .x31 .x23 184, .SD .x10 .x31 88, .LD .x31 .x23 192, .SD .x10 .x31 96,
   .LD .x31 .x21 0, .SD .x10 .x31 104, .LD .x31 .x21 8, .SD .x10 .x31 112,
   .ADDI .x10 .x10 64, .JAL .x0 2096472]

def firstPrefix (state : MachineState) (n : Nat) : MachineState :=
  (firstPreamble.take n).foldl execInstrBr state

def secondPrefix (state : MachineState) (n : Nat) : MachineState :=
  (secondPreamble.take n).foldl execInstrBr state

theorem execute_first_prefix (state : MachineState) (pc : state.pc = 0x10e4) (fuel : Nat)
    (valid : accessValid (state.getReg .x10 + 32#64) 8 = true) :
    execute checkerImage (4+fuel) state false =
      (do let r ← execute checkerImage fuel (firstPrefix state 4) false
          return r.charge 4 0) := by
  apply execute_unit_steps (states := firstPrefix state)
  intro i hi
  refine ⟨.base (firstPreamble[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply checker_fetch _ (if i=0 then 57 else 220+i) _ (by split <;> omega)
    · interval_cases i <;> simp [firstPrefix, firstPreamble, execInstrBr, pc, signExtend21]
    · interval_cases i <;> rfl
  · interval_cases i <;> simp [ordinaryStep, memoryArgumentsValid, memAccess, firstPrefix,
      firstPreamble, execInstrBr, signExtend12, valid]
  · interval_cases i <;> rfl

theorem execute_second_prefix (state : MachineState) (pc : state.pc = 4996) (fuel : Nat)
    (target : ∀ i : Fin 7, accessValid (state.getReg .x10 + BitVec.ofNat 64 (64+8*i.val)) 8 = true)
    (scratch : ∀ i : Fin 4, accessValid (state.getReg .x23 + BitVec.ofNat 64 (168+8*i.val)) 8 = true)
    (nonce : ∀ i : Fin 2, accessValid (state.getReg .x21 + BitVec.ofNat 64 (8*i.val)) 8 = true) :
    execute checkerImage (16+fuel) state false =
      (do let r ← execute checkerImage fuel (secondPrefix state 16) false
          return r.charge 16 0) := by
  apply execute_unit_steps (states := secondPrefix state)
  intro i hi
  refine ⟨.base (secondPreamble[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply checker_fetch _ (225+i) _ (by omega)
    · interval_cases i <;> simp [secondPrefix, secondPreamble, execInstrBr, pc]
    · interval_cases i <;> rfl
  · have nz : accessValid (state.getReg .x21) 8 = true := by simpa using nonce 0
    interval_cases i <;> simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,
      secondPrefix,secondPreamble,signExtend12,nz] <;>
      first | exact target 0 | exact target 1 | exact target 2 | exact target 3 |
            exact target 4 | exact target 5 | exact target 6 | exact scratch 0 |
            exact scratch 1 | exact scratch 2 | exact scratch 3 | exact nonce 1
  · interval_cases i <;> rfl

theorem checker_first_ecall (state : MachineState) (pc : state.pc = 4992) :
    fetch checkerImage state = some (.base .ECALL) :=
  checker_fetch state 224 .ECALL (by decide) pc rfl

theorem checker_second_ecall (state : MachineState) (pc : state.pc = 0x1118) :
    fetch checkerImage state = some (.base .ECALL) :=
  checker_fetch state 70 .ECALL (by decide) pc rfl

def checkerNonce (state : MachineState) : Words 2 := fun i =>
  if i.val = 0 then state.getMem (state.getReg .x21) else state.getMem (state.getReg .x21+8#64)

theorem first_prefix_pc (s : MachineState) (h : s.pc=0x10e4) :
    (firstPrefix s 4).pc = 4992 := by
  simp [firstPrefix, firstPreamble, execInstrBr, h, signExtend21]

theorem second_prefix_pc (s : MachineState) (h : s.pc=4996) :
    (secondPrefix s 16).pc = 0x1118 := by
  simp [secondPrefix, secondPreamble, execInstrBr, h, signExtend21]

theorem first_prefix_input (s : MachineState) :
    (firstPrefix s 4).getReg .x10 = s.getReg .x10+32#64 := rfl

theorem first_prefix_output (s : MachineState) :
    (firstPrefix s 4).getReg .x12 = s.getReg .x23 := by
  simp [firstPrefix,firstPreamble,execInstrBr,signExtend12]

theorem second_prefix_input (s : MachineState) :
    (secondPrefix s 16).getReg .x10 = s.getReg .x10+64#64 := rfl

theorem first_prefix_register (s : MachineState) (reg : Reg) (h10 : reg ≠ .x10)
    (h12 : reg ≠ .x12) : (firstPrefix s 4).getReg reg = s.getReg reg := by
  cases reg <;> first | exact absurd rfl h10 | exact absurd rfl h12 | rfl

theorem second_prefix_register (s : MachineState) (reg : Reg) (h10 : reg ≠ .x10)
    (h31 : reg ≠ .x31) : (secondPrefix s 16).getReg reg = s.getReg reg := by
  cases reg <;> first | exact absurd rfl h10 | exact absurd rfl h31 | rfl

theorem first_prefix_mem (s : MachineState) :
    (firstPrefix s 4).mem = (s.setMem (s.getReg .x10+32#64) 0).mem := rfl

def copyHeader (s : MachineState) (d sc no tag : Word) : Nat → MachineState
  | 0 => s.setMem (d+64#64) tag
  | n+1 =>
    let prev := copyHeader s d sc no tag n
    let fromAddr := if n<4 then sc+BitVec.ofNat 64 (168+8*n) else no+BitVec.ofNat 64 (8*(n-4))
    prev.setMem (d+BitVec.ofNat 64 (72+8*n)) (prev.getMem fromAddr)

theorem second_prefix_mem (s : MachineState) :
    (secondPrefix s 16).mem = (copyHeader s (s.getReg .x10) (s.getReg .x23)
      (s.getReg .x21) (s.getReg .x28+96#64) 6).mem := by
  simp [secondPrefix,secondPreamble,copyHeader,execInstrBr,signExtend12,MachineState.setPC,
    MachineState.setReg,MachineState.getReg,MachineState.setMem,MachineState.getMem]
  <;> rfl

end TwoPermutationPrototype.Checker
