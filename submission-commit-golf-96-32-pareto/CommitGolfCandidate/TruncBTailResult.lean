import CommitGolfCandidate.TruncBTailRuntime
import CommitGolfCandidate.TruncBRowRegs
import CommitGolfCandidate.TruncBRowLogic
namespace CommitGolfCandidate.Trunc.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 6000
set_option maxHeartbeats 25000
attribute [local irreducible] execute Late.Check.Normal.checkEvaluation readBuffer storedAt lowerHash

structure TailEvidence (fresh : Bool) (zero matchOK writeRun compareRun : Prop)
    (old : Option Digest) (current : Digest) : Prop where
  flag : if fresh then zero else ¬zero
  agrees : fresh=false → matchOK
  run : if fresh then writeRun else compareRun
  prior : old=if fresh then none else some current

abbrev TailOK (o : Oracle) (input : CheckInput) (n : Nat) (s : MachineState) (fresh : Bool) : Prop :=
  TailEvidence fresh ((bucketState s).getReg .x7=0) (equalWords (tested s))
    (Runs o s (copied s) 29 0) (Runs o s (compared s) 32 0)
    (storedAt s (rowBucket input n)) (lowerHash o.compression input n)

theorem tailFresh {zero same write compare : Prop} {old : Option Digest} {current : Digest}
    (z : zero) (run : write) (empty : old=none) : TailEvidence true zero same write compare old current :=
  ⟨z,fun bad=>False.elim ((by decide : true≠false) bad),run,empty⟩

theorem tailSeen {zero same write compare : Prop} {old : Option Digest} {current : Digest}
    (z : ¬zero) (run : compare) (equal : same) (full : old=some current) : TailEvidence false zero same write compare old current :=
  ⟨z,fun _=>equal,run,full⟩

theorem flagDecide (b : Bool) (P : Prop) [Decidable P] (h : if b then P else ¬P) : b=decide P := by
  cases b
  · exact (decide_eq_false h).symm
  · exact (decide_eq_true h).symm

attribute [local irreducible] copied compared Runs
private theorem muxRun (o : Oracle) (s l r : MachineState) (b : Bool)
    (h : if b then Runs o s l 29 0 else Runs o s r 32 0) :
    Runs o s (if b then l else r) (if b then 29 else 32) 0 := by cases b <;> exact h

theorem tailRun (o : Oracle) (i : CheckInput) (n : Nat) (s : MachineState) (b : Bool) (h : TailOK o i n s b) :
    Runs o s (finishRow b s) (if b then 29 else 32) 0 :=
  muxRun o s (copied s) (compared s) b h.run

theorem flagZeroIff (v : Byte) : v.zeroExtend 64=0 ↔ v=0 := by
  constructor
  · intro e;have b:=congrArg (fun w : Word=>w.truncate 8) e;simpa using b
  · rintro rfl;rfl

end CommitGolfCandidate.Trunc.Batch
