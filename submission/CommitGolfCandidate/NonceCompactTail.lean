import CommitGolfCandidate.NonceCompactCall

/-! The actual outer-loop decrement and branch. The copy procedure leaves x24
unchanged, so each finished record consumes exactly two control instructions. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

def nonceCompactTailDecrement (state : MachineState) : MachineState :=
  execInstrBr state (.ADDI .x24 .x24 4095)

def nonceCompactTailState (state : MachineState) : MachineState :=
  execInstrBr (nonceCompactTailDecrement state) (.BNE .x24 .x0 8168)

theorem nonce_compact_tail_execute (state : MachineState) (pc : state.pc=4580)
    (fuel : Nat) (coins : Bool) :
    execute nonceCompactImage (2+fuel) state coins=
      (do let result ← execute nonceCompactImage fuel (nonceCompactTailState state) coins
          return result.charge 2 0) := by
  have first : fetch nonceCompactImage state=some (.base (.ADDI .x24 .x24 4095)) := by
    apply cap_image_fetch _ state 121 _ (by decide) pc
    rfl
  have second : fetch nonceCompactImage (nonceCompactTailDecrement state)=
      some (.base (.BNE .x24 .x0 8168)) := by
    apply cap_image_fetch _ _ 122 _ (by decide)
    · simp only [nonceCompactTailDecrement, execInstrBr, MachineState.setPC, pc]
      rfl
    · rfl
  have firstStep : ordinaryStep state (.base (.ADDI .x24 .x24 4095))=
      some (nonceCompactTailDecrement state) := rfl
  have secondStep : ordinaryStep (nonceCompactTailDecrement state) (.base (.BNE .x24 .x0 8168))=
      some (nonceCompactTailState state) := rfl
  rw [show 2+fuel=(fuel+1)+1 by omega,
    execute_ordinary_step _ _ _ _ (fuel+1) coins first firstStep,
    execute_ordinary_step _ _ _ _ fuel coins second secondStep]
  simp [instructionCycles, Execution.charge, bind_assoc, ← Nat.add_assoc]

private theorem branch_memory (state : MachineState) (offset : BitVec 13) :
    (execInstrBr state (.BNE .x24 .x0 offset)).mem=state.mem := by
  simp only [execInstrBr]
  split <;> rfl

private theorem branch_register (state : MachineState) (offset : BitVec 13) (reg : Reg) :
    (execInstrBr state (.BNE .x24 .x0 offset)).getReg reg=state.getReg reg := by
  simp only [execInstrBr]
  split <;> exact MachineState.getReg_setPC

theorem nonce_compact_tail_memory (state : MachineState) :
    (nonceCompactTailState state).mem=state.mem := by
  rw [nonceCompactTailState, branch_memory]
  rfl

theorem nonce_compact_tail_register (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x24) :
    (nonceCompactTailState state).getReg reg=state.getReg reg := by
  rw [nonceCompactTailState, branch_register]
  simp only [nonceCompactTailDecrement, execInstrBr,
    MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside)]

theorem nonce_compact_tail_counter (state : MachineState) (remaining : Nat)
    (small : remaining+1 < 2^64)
    (counter : state.getReg .x24=BitVec.ofNat 64 (remaining+1)) :
    (nonceCompactTailState state).getReg .x24=BitVec.ofNat 64 remaining := by
  rw [nonceCompactTailState, branch_register]
  simp only [nonceCompactTailDecrement, execInstrBr,
    MachineState.getReg_setPC, MachineState.getReg_setReg_eq]
  rw [counter]
  exact NonceWordCopy.decrement (remaining+1) (by omega)

theorem nonce_compact_tail_pc (state : MachineState) (remaining : Nat)
    (pc : state.pc=4580) (small : remaining+1 < 2^64)
    (counter : state.getReg .x24=BitVec.ofNat 64 (remaining+1)) :
    (nonceCompactTailState state).pc=if remaining=0 then 4588 else 4560 := by
  have counterAfter : (nonceCompactTailDecrement state).getReg .x24=BitVec.ofNat 64 remaining := by
    simp only [nonceCompactTailDecrement, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq, counter]
    exact NonceWordCopy.decrement (remaining+1) (by omega)
  have zero : (BitVec.ofNat 64 remaining : Word)=0 ↔ remaining=0 := by
    constructor
    · intro equal
      have numeric:=congrArg BitVec.toNat equal
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : remaining<2^64)] at numeric
      exact numeric
    · rintro rfl
      rfl
  simp only [nonceCompactTailState, execInstrBr, counterAfter,
    show (nonceCompactTailDecrement state).getReg .x0=0 from rfl, bne_iff_ne,
    ne_eq, zero]
  by_cases empty : remaining=0
  · simp [empty, nonceCompactTailDecrement, execInstrBr, MachineState.setPC, pc]

  · simp [empty, nonceCompactTailDecrement, execInstrBr, MachineState.setPC, pc,
      signExtend13]


end CommitGolfCandidate
