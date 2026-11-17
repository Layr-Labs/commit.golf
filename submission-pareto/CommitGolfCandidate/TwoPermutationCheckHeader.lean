import CommitGolfCandidate.TwoPermutationGroupCode

namespace TwoPermutationPrototype.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
attribute [local simp] Opening.getReg_setReg MachineState.getReg_setPC

/-- First charge depends only on public input registers. -/
def requiredProofWord (s : MachineState) : Word := s.getReg .x16*528

private def requirementStart (s : MachineState) := execInstrBr s (.SLLI .x6 .x16 4)
private def requirementPair (s : MachineState) :=
  execInstrBr (execInstrBr s (.SLLI .x7 .x16 5)) (.ADD .x6 .x6 .x7)

def measureState : Nat → MachineState → MachineState
  | 0,s => requirementStart s
  | n+1,s => requirementPair (measureState n s)

private theorem measure_one (s : MachineState) (pc : s.pc=4096) (fuel : Nat) :
    execute checkerImage (1+fuel) s false = do
      let result ← execute checkerImage fuel (requirementStart s) false
      return result.charge 1 0 := by
  rw [Nat.add_comm 1 fuel]
  rw [execute, checker_fetch s 0 _ (by decide) pc (by rfl : checkerInstructions[0]?=some (.SLLI .x6 .x16 4))]
  rfl

private theorem measure_pair (s : MachineState) (i : Nat) (small : i<16)
    (pc : s.pc=BitVec.ofNat 64 (4100+8*i)) (fuel : Nat) :
    execute checkerImage (2+fuel) s false = do
      let result ← execute checkerImage fuel (requirementPair s) false
      return result.charge 2 0 := by
  let middle := execInstrBr s (.SLLI .x7 .x16 5)
  let state (j : Nat) := if j=0 then s else if j=1 then middle else requirementPair s
  change execute checkerImage (2+fuel) (state 0) false = do
    let result ← execute checkerImage fuel (state 2) false
    return result.charge 2 0
  apply execute_unit_steps (states := state)
  intro j inside
  interval_cases j
  · refine ⟨.base (.SLLI .x7 .x16 5), checker_fetch s (1+2*i) _ (by omega) ?_ ?_,rfl,rfl⟩
    · rw [pc]; congr 1; omega
    · interval_cases i <;> rfl
  · refine ⟨.base (.ADD .x6 .x6 .x7), checker_fetch middle (2+2*i) _ (by omega) ?_ ?_,rfl,rfl⟩
    · change s.pc+4=_
      rw [pc,show (4 : Word)=BitVec.ofNat 64 4 by rfl,← BitVec.ofNat_add]
      congr 1
      omega
    · interval_cases i <;> rfl

private theorem measure_pc (s : MachineState) (count : Nat) (pc : s.pc=4096) :
    (measureState count s).pc=BitVec.ofNat 64 (4100+8*count) := by
  induction count with
  | zero => change s.pc+4=_;rw [pc];rfl
  | succ n ih =>
    change (measureState n s).pc+4+4=_
    rw [ih,BitVec.add_assoc,show (4:Word)+4=BitVec.ofNat 64 8 by rfl,← BitVec.ofNat_add]
    congr 1

theorem execute_measure (s : MachineState) (count : Nat) (small : count≤16)
    (pc : s.pc=4096) (fuel : Nat) :
    execute checkerImage (1+2*count+fuel) s false = do
      let result ← execute checkerImage fuel (measureState count s) false
      return result.charge (1+2*count) 0 := by
  induction count generalizing fuel with
  | zero => exact measure_one s pc fuel
  | succ n ih =>
    rw [show 1+2*(n+1)+fuel=1+2*n+(2+fuel) by omega,ih (by omega) (2+fuel),
      measure_pair _ n (by omega) (measure_pc s n pc)]
    simp only [measureState,bind_assoc,pure_bind,Execution.charge,Nat.zero_add]
    congr 1
    funext result
    congr 2
    omega

private theorem pair_index (s : MachineState) : (requirementPair s).getReg .x16=s.getReg .x16 := by
  simp [requirementPair,execInstrBr]

private theorem pair_required (s : MachineState) :
    (requirementPair s).getReg .x6=s.getReg .x6+s.getReg .x16*32 := by
  have shift : (s.getReg .x16 <<< 5)=s.getReg .x16*32 := BitVec.shiftLeft_eq_mul_twoPow _ _
  simp [requirementPair,execInstrBr,shift]

private theorem measure_count (s : MachineState) (n : Nat) : (measureState n s).getReg .x16=s.getReg .x16 := by
  induction n with
  | zero => simp [measureState,requirementStart,execInstrBr]
  | succ n ih => exact (pair_index _).trans ih

private theorem measure_accum (s : MachineState) (n : Nat) :
    (measureState n s).getReg .x6=s.getReg .x16 * BitVec.ofNat 64 (16+32*n) := by
  induction n with
  | zero =>
    have shift : (s.getReg .x16 <<< 4)=s.getReg .x16*16 := BitVec.shiftLeft_eq_mul_twoPow _ _
    simp [measureState,requirementStart,execInstrBr,shift]
  | succ n ih =>
    rw [measureState,pair_required,ih,measure_count,←BitVec.mul_add]
    have add : 16+32*(n+1)=16+32*n+32 := by omega
    rw [add,BitVec.ofNat_add (16+32*n) 32]
    rfl

theorem measure_post (s : MachineState) (pc : s.pc=4096) :
    let t := measureState 16 s
    t.pc=4228 ∧ t.getReg .x6=requiredProofWord s ∧ t.mem=s.mem ∧
      ∀ r : Reg, r≠.x6 → r≠.x7 → t.getReg r=s.getReg r := by
  refine ⟨measure_pc s 16 pc,measure_accum s 16,?_,?_⟩
  · have mem (n : Nat) : (measureState n s).mem=s.mem := by
      induction n with
      | zero => rfl
      | succ n ih => exact ih
    exact mem 16
  · intro r a b
    have kept (n : Nat) : (measureState n s).getReg r=s.getReg r := by
      induction n with
      | zero => simp [measureState,requirementStart,execInstrBr,Ne.symm a]
      | succ n ih =>
        simp [measureState,requirementPair,execInstrBr,Ne.symm a,Ne.symm b,ih]
    exact kept 16

end TwoPermutationPrototype.Checker
