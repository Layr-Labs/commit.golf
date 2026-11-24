import CommitGolfCandidate.ChainedContinuationTail

/-! An actual compression call and back-edge tail, with exact interpreter costs. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
attribute [local irreducible] execute writeBits

private theorem reply_pc {bits : Nat} (s : MachineState) (address : Word) (answer : BitVec bits) :
    (writeBits s address answer).pc = s.pc+4 := by
  simp only [writeBits,MachineState.setPC]

theorem iteration_execution (image : Image) (base : Word) (code : ContinuationAt image base)
    (s : MachineState) (pc : s.pc = base+36) (selector : s.getReg .x5 = 0)
    (payload : BitVec 512) (query : oracleInput s = some (.inl payload))
    (valid : accessValid (s.getReg .x10+32) 8 = true) (fuel : Nat) (coins : Bool) :
    execute image (6+fuel) s coins =
      (do let answer ← (liftM (World.query (.inr (.inl payload))) : OracleComp World (BitVec 256))
          let result ← execute image fuel (tailAfter (writeBits s (s.getReg .x12) answer)) coins
          return result.charge 13 1) := by
  have fetched : fetch image s = some (.base .ECALL) := code ⟨9,by decide⟩ s pc
  rw [show 6+fuel = (5+fuel)+1 by omega]
  simp only [execute,fetched,selector,ite_eq_left,query,writeOracleAnswer,oracleCycles,COMPRESSION_CYCLES]
  apply bind_congr
  intro answer
  have nextPc : (writeBits s (s.getReg .x12) answer).pc = base+40 := by
    rw [reply_pc,pc,BitVec.add_assoc]
    rfl
  have nextValid : accessValid ((writeBits s (s.getReg .x12) answer).getReg .x10+32) 8 = true := by
    rw [writeBits_register]
    exact valid
  rw [tail_execution image base code _ nextPc nextValid fuel coins]
  simp [Execution.charge,← Nat.add_assoc]
  rfl

end CommitGolfCandidate.Chained.Native
