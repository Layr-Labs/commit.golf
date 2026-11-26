import CommitGolfCandidate.TruncBRecordAdvance
import CommitGolfCandidate.TruncCap
import CommitGolfCandidate.Stage3Record
namespace CommitGolfCandidate.Trunc.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8000
set_option maxHeartbeats 30000
attribute [local irreducible] readBuffer storedAt prefixNode lowerHash

theorem advance (o : Oracle) (input : CheckInput) (n : Nat) (hn : n<128) (s : MachineState)
    (inv : RecordInvariant o.compression input n s) (fresh : Bool)
    (m : MachineState) (higher : Late.Check3.Micro.High s m) (h : HashedFrame o input n m) (passed : TailOK o input n m fresh) :
    RecordInvariant o.compression input (n+1) (finishRow fresh m) :=
  finishInvariant o input n hn m h fresh passed
    (fun v=>(hashedTable higher v).trans (inv.table v)) inv.consistent
    (fun w hw al hb=>(highWord higher w (by omega) al hb).trans (inv.inputWords w hw al hb))
    (fun p=>(hashGap higher p).trans (inv.gap p))

private theorem tailBound (k : Nat) (cap : k≤1010) (fresh : Bool) : k+(if fresh then 29 else 32)≤1044 := by cases fresh <;> simp <;> omega

theorem rowStep (o : Oracle) (input : CheckInput) (b : input.positions.card=BATCH)
    (n : Nat) (hn : n<128) (s : MachineState) (inv : RecordInvariant o.compression input n s) :
    (¬BatchValid o.compression input ∧ ∃ k≤1044, Rejects o s k 20) ∨
    ∃ t k, k≤1044 ∧ Runs o s t k 20 ∧ RecordInvariant o.compression input (n+1) t := by
  obtain ⟨m,k,cap,run,h,higher⟩ := hashRecord o input b n hn s inv
  have tab := (hashedTable higher (rowBucket input n)).trans (inv.table _)
  rcases classifyRow o input n hn m h tab with ⟨rej,invalid⟩|⟨fresh,passed⟩
  · exact Or.inl ⟨invalid,k+31,by omega,runs_rejects run rej⟩
  · refine Or.inr ⟨_,_,?_,runs_trans run (tailRun o input n m fresh passed),advance o input n hn s inv fresh m higher h passed⟩
    exact tailBound k cap fresh

theorem allRows (o : Oracle) (input : CheckInput) (b : input.positions.card=BATCH)
    (left n : Nat) (total : n+left=128) (s : MachineState) (inv : RecordInvariant o.compression input n s) :
    (¬BatchValid o.compression input ∧ ∃ k≤1044*left, ∃ q≤20*left, Rejects o s k q) ∨
    ∃ t k, k≤1044*left ∧ Runs o s t k (20*left) ∧ RecordInvariant o.compression input 128 t := by
  induction left generalizing n s with
  | zero =>
    have eqn : n=128 := by omega
    subst n
    exact Or.inr ⟨s,0,by decide,fun fuel => by simp,inv⟩
  | succ left ih =>
    rcases rowStep o input b n (by omega) s inv with ⟨bad,k,hk,rej⟩|⟨t,k,hk,step,inv'⟩
    · exact Or.inl ⟨bad,k,by omega,20,by omega,rej⟩
    · rcases ih (n+1) (by omega) t inv' with ⟨bad,j,hj,q,hq,rej⟩|⟨z,j,hj,tail,final⟩
      · exact Or.inl ⟨bad,k+j,by omega,20+q,by omega,runs_rejects step rej⟩
      · exact Or.inr ⟨z,k+j,by omega,by simpa only [Nat.mul_succ,Nat.add_comm 20 (20*left)] using runs_trans step tail,final⟩
end CommitGolfCandidate.Trunc.Batch
