import CommitGolfCandidate.ChainedContinuationLoop

/-! The repeated loop reaches the single final mask and returns to its caller. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

theorem loop_after_pc (s : MachineState) (base buffer : Word) (answer : BitVec 256)
    (pc : s.pc = base+36) (remaining : Nat) (small : remaining < 8)
    (counter : s.getReg .x18 = BitVec.ofNat 64 (remaining+1)) :
    (loopAfter buffer s answer).pc = if remaining = 0 then base+60 else base+36 := by
  have written : (writeBits s buffer answer).pc = base+40 := by
    simp only [writeBits,MachineState.setPC]
    rw [pc,BitVec.add_assoc]
    rfl
  have count : (writeBits s buffer answer).getReg .x18 = BitVec.ofNat 64 (remaining+1) := by
    rw [writeBits_register]
    exact counter
  simpa only [loopAfter] using tail_pc (writeBits s buffer answer) base written remaining small count

theorem loop_trace_post (base buffer : Word) (remaining : Nat) (small : remaining ≤ 7)
    (s : MachineState) (args : LoopArgs s buffer)
    (counter : s.getReg .x18 = BitVec.ofNat 64 remaining)
    (pc : s.pc = if remaining = 0 then base+60 else base+36)
    (out : MachineState) (reached : out ∈ support (loopTrace buffer remaining s)) :
    LoopArgs out buffer ∧ out.getReg .x18 = 0 ∧ out.pc = base+60 := by
  induction remaining generalizing s with
  | zero =>
    simp only [loopTrace,support_pure,Set.mem_singleton_iff] at reached
    subst out
    exact ⟨args,counter,by simpa using pc⟩
  | succ remaining ih =>
    simp only [loopTrace,mem_support_bind_iff] at reached
    obtain ⟨answer,_,last⟩ := reached
    have here : s.pc = base+36 := by simpa using pc
    apply ih (by omega) _ (args.after answer) _ _ last
    · apply tail_counter _ remaining (by omega)
      rw [writeBits_register]
      exact counter
    · exact loop_after_pc s base buffer answer here remaining (by omega) counter

theorem loop_mask_execution (image : Image) (base buffer : Word) (code : ContinuationAt image base)
    (remaining : Nat) (small : remaining ≤ 7) (s : MachineState) (args : LoopArgs s buffer)
    (counter : s.getReg .x18 = BitVec.ofNat 64 remaining)
    (pc : s.pc = if remaining = 0 then base+60 else base+36)
    (valid : accessValid (buffer+24) 8 = true) (fuel : Nat) (coins : Bool) :
    execute image (6*remaining+4+fuel) s coins =
      (do let out ← loopTrace buffer remaining s
          let result ← execute image fuel (ordinaryPrefix out 15 4) coins
          return result.charge (13*remaining+4) remaining) := by
  have here : remaining ≠ 0 → s.pc = base+36 := by
    intro positive
    simpa only [ite_eq_right positive] using pc
  rw [show 6*remaining+4+fuel = 6*remaining+(4+fuel) by omega,
    loop_execution image base buffer code remaining small s args counter here]
  apply bind_congr_of_forall_mem_support
  intro out reached
  obtain ⟨outArgs,_,outPc⟩ := loop_trace_post base buffer remaining small s args counter pc out reached
  have outValid : accessValid (out.getReg .x10+24) 8 = true := by rw [outArgs.source]; exact valid
  rw [mask_execution image base code out outPc outValid fuel coins]
  simp [Execution.charge,Nat.add_assoc]

end CommitGolfCandidate.Chained.Native
