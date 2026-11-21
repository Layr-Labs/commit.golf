import CommitGolfCandidate.ChainedContinuationIteration
import CommitGolfCandidate.QueryBudget

/-! Repeated native continuation calls under concrete in-place compression arguments. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

structure LoopArgs (s : MachineState) (buffer : Word) : Prop where
  source : s.getReg .x10 = buffer
  target : s.getReg .x12 = buffer
  selector : s.getReg .x5 = 0
  size : s.getReg .x11 = 64
  kind : s.getReg .x13 = 0
  aligned : buffer.toNat % 8 = 0
  inputValid : rangeValid buffer 64 = true
  outputValid : rangeValid buffer 32 = true
  access : accessValid (buffer+32) 8 = true

def loopAfter (buffer : Word) (s : MachineState) (answer : BitVec 256) : MachineState :=
  tailAfter (writeBits s buffer answer)

theorem LoopArgs.query {s : MachineState} {buffer : Word} (args : LoopArgs s buffer) :
    oracleInput s = some (.inl (readBuffer s buffer.toNat 64)) := by
  have kind : (s.getReg .x13).toNat = 0 := by rw [args.kind]; rfl
  unfold oracleInput
  dsimp only
  rw [kind]
  simp [args.source,args.target,args.size,args.aligned,
    args.inputValid,args.outputValid,COMPRESSION_INPUT_LENGTH,COMPRESSION_OUTPUT_LENGTH]

theorem LoopArgs.after {s : MachineState} {buffer : Word} (args : LoopArgs s buffer)
    (answer : BitVec 256) : LoopArgs (loopAfter buffer s answer) buffer := by
  have get (reg : Reg) (a : reg ≠ .x29) (b : reg ≠ .x18) :
      (loopAfter buffer s answer).getReg reg = s.getReg reg := by
    rw [loopAfter,tail_register _ reg a b,writeBits_register]
  exact ⟨(get .x10 (by decide) (by decide)).trans args.source,
    (get .x12 (by decide) (by decide)).trans args.target,
    (get .x5 (by decide) (by decide)).trans args.selector,
    (get .x11 (by decide) (by decide)).trans args.size,
    (get .x13 (by decide) (by decide)).trans args.kind,
    args.aligned,args.inputValid,args.outputValid,args.access⟩

def loopTrace (buffer : Word) : Nat → MachineState → OracleComp World MachineState
  | 0,s => pure s
  | remaining+1,s => do
    let answer ← (liftM (World.query (.inr (.inl (readBuffer s buffer.toNat 64)))) :
      OracleComp World (BitVec 256))
    loopTrace buffer remaining (loopAfter buffer s answer)

theorem loop_trace_bounded (buffer : Word) (remaining : Nat) (s : MachineState) :
    PublicQueryBound (loopTrace buffer remaining s) remaining := by
  induction remaining generalizing s with
  | zero => trivial
  | succ remaining ih =>
    change 1 ≤ remaining+1 ∧ ∀ answer,
      PublicQueryBound (loopTrace buffer remaining (loopAfter buffer s answer)) (remaining+1-1)
    exact ⟨by omega,fun answer => by simpa using ih (loopAfter buffer s answer)⟩

theorem loop_execution (image : Image) (base buffer : Word) (code : ContinuationAt image base)
    (remaining : Nat) (small : remaining ≤ 7) (s : MachineState) (args : LoopArgs s buffer)
    (counter : s.getReg .x18 = BitVec.ofNat 64 remaining)
    (pc : remaining ≠ 0 → s.pc = base+36) (fuel : Nat) (coins : Bool) :
    execute image (6*remaining+fuel) s coins =
      (do let out ← loopTrace buffer remaining s
          let result ← execute image fuel out coins
          return result.charge (13*remaining) remaining) := by
  induction remaining generalizing s with
  | zero => simp [loopTrace,Execution.charge]
  | succ remaining ih =>
    have here := pc (by omega)
    have valid : accessValid (s.getReg .x10+32) 8 = true := by rw [args.source]; exact args.access
    rw [show 6*(remaining+1)+fuel = 6+(6*remaining+fuel) by omega,
      iteration_execution image base code s here args.selector _ args.query valid]
    rw [args.target]
    simp only [loopTrace,bind_assoc]
    apply bind_congr
    intro answer
    have nextCounter : (loopAfter buffer s answer).getReg .x18 = BitVec.ofNat 64 remaining := by
      apply tail_counter _ remaining (by omega)
      rw [writeBits_register]
      exact counter
    have nextPc : remaining ≠ 0 → (loopAfter buffer s answer).pc = base+36 := by
      intro positive
      have written : (writeBits s buffer answer).pc = base+40 := by
        simp only [writeBits,MachineState.setPC]
        rw [here,BitVec.add_assoc]
        rfl
      have next := tail_pc (writeBits s buffer answer) base written remaining (by omega) (by
        rw [writeBits_register]; exact counter)
      simpa only [loopAfter,ite_eq_right positive] using next
    change (do let result ← execute image (6*remaining+fuel) (loopAfter buffer s answer) coins
               return result.charge 13 1) = _
    rw [ih (by omega) _ (args.after answer) nextCounter nextPc]
    simp [Execution.charge,Nat.mul_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

end CommitGolfCandidate.Chained.Native
