import CommitGolfCandidate.TruncBPrepare
namespace CommitGolfCandidate.Trunc.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 6000
set_option maxHeartbeats 90000
attribute [local irreducible] Late.Check.Normal.checkEvaluation execute readBuffer

def exitCalls (r : Execution × Nat) : Exit × Nat := (r.1.exit,r.2)

theorem compressionObs (o : Oracle) (x : BitVec COMPRESSION_INPUT_LENGTH) (rest : Digest → OracleComp World Execution) :
    exitCalls (Late.Check.Normal.checkEvaluation o (do
      let d ← (liftM (World.query (.inr (.inl x))) : OracleComp World Digest)
      let e ← rest d
      return e.charge 13 1)) =
    ((Late.Check.Normal.checkEvaluation o (rest (o.compression x))).1.exit,1+(Late.Check.Normal.checkEvaluation o (rest (o.compression x))).2) := by
  let k (d : Digest) : OracleComp World Execution := do
    let e ← rest d
    return e.charge 13 1
  have call := Late.Check.Normal.check_evaluation_public_bind o (α:=Execution) (.inl x) k
  change exitCalls (Late.Check.Normal.checkEvaluation o ((liftM (World.query (.inr (.inl x))) : OracleComp World Digest) >>= k)) = _
  apply (congrArg exitCalls call).trans
  change ((Late.Check.Normal.checkEvaluation o (k (o.compression x))).1.exit,1+(Late.Check.Normal.checkEvaluation o (k (o.compression x))).2)=_
  simp only [k,bind_pure_comp,Late.Check.Normal.check_evaluation_map]
  rfl

theorem hashRuns (o : Oracle) (t : MachineState) (pc : t.pc=5408)
    (sb : rangeValid (t.getReg .x23) 96) (sa : (t.getReg .x23).toNat%8=0)
    (db : rangeValid (t.getReg .x24) 32) (da : (t.getReg .x24).toNat%8=0) :
    Runs o t (hashed t (o.compression (readBuffer t (t.getReg .x23).toNat 96))) 6 1 := by
  intro fuel;unfold obs;rw [hashRun t pc sb sa db da fuel false]
  exact compressionObs o (readBuffer t (t.getReg .x23).toNat 96)
    (fun d=>execute (Trunc.wireImage true) fuel (hashed t d) false)

theorem hashKeeps (t : MachineState) (d : Digest) : Carries t (hashed t d) := by
  intro r hr
  apply (writeBits_register (hashSetupState t) (t.getReg .x24) d r).trans
  simp only [pairRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

end CommitGolfCandidate.Trunc.Batch
