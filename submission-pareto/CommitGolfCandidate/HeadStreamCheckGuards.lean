import CommitGolfCandidate.HeadStreamCheckEntry
import CommitGolfCandidate.TailStreamCheckGuards

namespace TwoPermutationPrototype.Packed.Checker.HeadRestore
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open PackedOpening.Pack (ordinaryInstr w_add w_mul w_shl w_shr ult_ofNat)
attribute [local simp] Opening.getReg_setReg
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

def rejectHigh : List Nat := [0,1,2,3,4,5,6,7,8]
def rejectLow : List Nat := [0,1,2,3,4,5,6,7,8,9,10,11]
@[simp] theorem high_guard_target : 6320#64+signExtend13 7424#13=5552#64 := by decide
@[simp] theorem low_guard_target : 6332#64+signExtend13 7412#13=5552#64 := by decide

theorem reject_high (k N : Nat) (s : MachineState)
    (pc : s.pc=pcOf 0) (x16 : s.getReg .x16=BitVec.ofNat 64 k)
    (x17 : s.getReg .x17=BitVec.ofNat 64 N) (kb : k≤2^24) (incoming : N≤8355061248)
    (bad : 8355061248<N+k) :
    Hop s (run s rejectHigh) 9 9 ∧ (run s rejectHigh).pc=5552 := by
  have ok : PathOK s rejectHigh := by
    simp (disch := omega) [PathOK,rejectHigh,execInstrBr,pc,x16,x17,ordinaryInstr,
      memoryArgumentsValid,memAccess,w_add,w_mul,w_shl,w_shr,ult_ofNat,bad,pcOf]
  refine ⟨(runs_path s rejectHigh ok).cast rfl (by decide),?_⟩
  simp (disch := omega) [run,rejectHigh,execInstrBr,pc,x16,x17,w_add,w_shl,w_shr,ult_ofNat,bad,pcOf]

theorem reject_low (k N : Nat) (s : MachineState)
    (pc : s.pc=pcOf 0) (x16 : s.getReg .x16=BitVec.ofNat 64 k)
    (x17 : s.getReg .x17=BitVec.ofNat 64 N) (kb : k≤2^24) (incoming : N≤8355061248)
    (capacity : N+k≤8355061248) (bad : N+k<481*k) :
    Hop s (run s rejectLow) 12 15 ∧ (run s rejectLow).pc=5552 := by
  have high : ¬8355061248<N+k := by omega
  have low : N+k<k*481 := by omega
  have ok : PathOK s rejectLow := by
    simp (disch := omega) [PathOK,rejectLow,execInstrBr,pc,x16,x17,ordinaryInstr,
      memoryArgumentsValid,memAccess,w_add,w_mul,w_shl,w_shr,ult_ofNat,high,low,pcOf]
  refine ⟨(runs_path s rejectLow ok).cast rfl (by decide),?_⟩
  simp (disch := omega) [run,rejectLow,execInstrBr,pc,x16,x17,w_add,w_mul,w_shl,w_shr,ult_ofNat,high,low,pcOf]

variable [UnpackOrigin]

theorem tail_steps_bound (input : CheckInput) (fits : input.proof.length≤8355061248) :
    tailSteps input.positions.card input.proof.length≤2^37 := by
  have kb := TwoPermutationPrototype.Checker.checker_positions_bound input
  have bound := TailRestore.restore_steps_bound input.positions.card (input.proof.length+input.positions.card/8)
  unfold tailSteps
  omega

theorem tail_guard_reject (input : CheckInput) (fits : input.proof.length≤8355061248)
    (bad : 8355061248< input.proof.length+input.positions.card/8 ∨
      input.proof.length+input.positions.card/8<480*input.positions.card) :
    ∃ steps cycles t,steps≤14 ∧ ∀ fuel,
      execute packedImage (steps+3+fuel) (Assembly.submission.initialState .check input) false=
        pure ⟨.failure,headerRejectState t,cycles+3,0⟩ := by
  have kb := TwoPermutationPrototype.Checker.checker_positions_bound input
  have r16 : (tailStart input).getReg .x16=BitVec.ofNat 64 input.positions.card := by
    rw [tailStart,factor_getReg,assembly_getReg]
    rfl
  have r17 : (tailStart input).getReg .x17=BitVec.ofNat 64 input.proof.length := by
    rw [tailStart,factor_getReg,assembly_getReg]
    rfl
  by_cases high : 8355061248< input.proof.length+input.positions.card/8
  · obtain ⟨hop,pc⟩ := TailRestore.reject_high input.positions.card input.proof.length (tailStart input)
      rfl r16 r17 kb fits high
    have both := (tail_entry_hop input).thenDo hop
    refine ⟨11,11,TailRestore.run (tailStart input) TailRestore.rejectHigh,by omega,?_⟩
    intro fuel
    rw [show 11+3+fuel=11+(3+fuel) by omega,both (3+fuel),execute_header_reject _ pc fuel]
    simp [Execution.charge]
  · have low : input.proof.length+input.positions.card/8<480*input.positions.card := bad.resolve_left high
    obtain ⟨hop,pc⟩ := TailRestore.reject_low input.positions.card input.proof.length (tailStart input)
      rfl r16 r17 kb fits (by omega) low
    have both := (tail_entry_hop input).thenDo hop
    refine ⟨14,17,TailRestore.run (tailStart input) TailRestore.rejectLow,by omega,?_⟩
    intro fuel
    rw [show 14+3+fuel=14+(3+fuel) by omega,both (3+fuel),execute_header_reject _ pc fuel]
    simp [Execution.charge]

theorem entry_guard_reject (input : CheckInput) (fits : input.proof.length≤8355061248)
    (bad : 8355061248< input.proof.length+input.positions.card/8+input.positions.card ∨
      input.proof.length+input.positions.card/8+input.positions.card<481*input.positions.card) :
    ∃ steps cycles t,steps≤2^37+14 ∧ ∀ fuel,
      execute packedImage (steps+3+fuel) (Assembly.submission.initialState .check input) false=
        pure ⟨.failure,headerRejectState t,cycles+3,0⟩ := by
  by_cases capacity : input.proof.length+input.positions.card/8≤8355061248
  · by_cases records : 480*input.positions.card ≤ input.proof.length+input.positions.card/8
    · obtain ⟨middle,stage,first⟩ := tail_stage input fits capacity records
      have kb := TwoPermutationPrototype.Checker.checker_positions_bound input
      have r16 : middle.getReg .x16=BitVec.ofNat 64 input.positions.card := by
        rw [stage.low .x16 (by decide) (by decide),headStart,factor_getReg,assembly_getReg]
        rfl
      have r17 : middle.getReg .x17=BitVec.ofNat 64 (input.proof.length+input.positions.card/8) := by
        simpa only [seven_length] using stage.length
      have high : 8355061248< input.proof.length+input.positions.card/8+input.positions.card := by omega
      obtain ⟨hop,pc⟩ := reject_high input.positions.card (input.proof.length+input.positions.card/8)
        middle stage.pc r16 r17 kb capacity high
      have both := first.thenDo hop
      refine ⟨tailSteps input.positions.card input.proof.length+9,
        tailCycles input.positions.card input.proof.length+9,run middle rejectHigh,
        by have := tail_steps_bound input fits;omega,?_⟩
      intro fuel
      rw [show tailSteps input.positions.card input.proof.length+9+3+fuel=
        (tailSteps input.positions.card input.proof.length+9)+(3+fuel) by omega,
        both (3+fuel),execute_header_reject _ pc fuel]
      simp [Execution.charge,Nat.add_assoc]
    · obtain ⟨steps,cycles,t,bound,ran⟩ := tail_guard_reject input fits (Or.inr (by omega))
      exact ⟨steps,cycles,t,by omega,ran⟩
  · obtain ⟨steps,cycles,t,bound,ran⟩ := tail_guard_reject input fits (Or.inl (by omega))
    exact ⟨steps,cycles,t,by omega,ran⟩

end TwoPermutationPrototype.Packed.Checker.HeadRestore
