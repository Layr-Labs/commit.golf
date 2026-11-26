import CommitGolfCandidate.TruncBPairs
import CommitGolfCandidate.TruncBRows
import CommitGolfCandidate.TruncBatchStart
import CommitGolfCandidate.TruncNormalEntry
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp Batch
set_option maxRecDepth 10000
set_option maxHeartbeats 180000
attribute [local irreducible] execute Late.Check.Normal.checkEvaluation Batch.expandedFirst lowerHash unpack

theorem finishBatch (o : Oracle) (input : CheckInput) (b : input.positions.card=BATCH)
    (size : input.proof.length=72704) (first : MachineState)
    (start : RecordInvariant o.compression input 0 first) (budget : Nat) (big : 150000≤budget) :
    (obs o budget first).1≠.unfinished ∧ (obs o budget first).2≤2815 ∧
      ((obs o budget first).1=.success ↔ BatchValid o.compression input) := by
  rcases allRows o input b 128 0 (by decide) first start with ⟨invalid,k,hk,q,hq,reject⟩|⟨s,k,hk,rows,done⟩
  · have eqn := reject (budget-k)
    rw [show k+(budget-k)=budget by omega] at eqn
    rw [eqn]
    exact ⟨(by decide : Exit.failure≠Exit.unfinished),by omega,⟨fun bad=>False.elim ((by decide : Exit.failure≠.success) bad),fun v=>False.elim (invalid v)⟩⟩
  · obtain ⟨init,cap⟩:=pairStart o input s done
    obtain ⟨t,j,q,hj,hq,pairs,last⟩:=allPairs o input 128 0 (by decide) _ cap
    obtain ⟨ex,fin,term,root⟩:=finishCap o input t (completedCap o input t last)
    have complete := runs_finish (runs_trans (runs_trans rows init) pairs) fin
    let need:=((k+10)+j)+3460
    have enough : need≤budget := by dsimp [need];omega
    have all := complete (budget-need)
    rw [show k+10+j+3460+(budget-need)=budget by dsimp [need];omega] at all
    rw [all]
    exact ⟨term,by omega,⟨fun ok=>⟨size,completedRecords o input s done,root.mp ok⟩,fun v=>root.mpr v.root⟩⟩


theorem batchEvaluation (o : Oracle) (i : CheckInput) (b : i.positions.card=BATCH) :
    let out:=Late.Check.Normal.checkEvaluation o (submission.run .check i)
    out.1.exit≠.unfinished ∧ out.2≤2815 ∧ (out.1.exit=.success ↔ i.proof.length=69120 ∧ BatchValid o.compression (wideInput i)) := by
  dsimp only
  let s:=submission.initialState .check i
  have mode : s.getReg .x16=128 := by change BitVec.ofNat 64 i.positions.card=128;rw [b];rfl
  by_cases admitted : i.proof.length≤submission.sizes.proof
  · have run : submission.run .check i=execute (Trunc.wireImage true) (submission.steps .check) s false := by
      simp only [Submission.run,admitted,decide_true,ite_true];rfl
    rw [run]
    by_cases good : i.proof.length=69120
    · have len : s.getReg .x17=69120 := by change BitVec.ofNat 64 i.proof.length=69120;rw [good];rfl
      have card : (wideInput i).positions.card=BATCH := by unfold wideInput;rw [if_pos b];exact b
      have size : (wideInput i).proof.length=72704 := by unfold wideInput;rw [if_pos b];exact unpack_length i.proof
      have h:=finishBatch o (wideInput i) card size _ (startInvariant o i b good) (submission.steps .check-71981) (by decide)
      rw [show submission.steps .check=71981+(submission.steps .check-71981) by decide,headerRun s rfl mode len,
        bind_pure_comp,Late.Check.Normal.check_evaluation_map]
      change (obs o _ _).1≠.unfinished ∧ (obs o _ _).2≤2815 ∧ ((obs o _ _).1=.success ↔ _)
      exact ⟨h.1,h.2.1,⟨fun e=>⟨good,h.2.2.mp e⟩,fun e=>h.2.2.mpr e.2⟩⟩
    · have wrong : s.getReg .x17≠69120 := by
        intro e;apply good
        change BitVec.ofNat 64 i.proof.length=69120 at e
        have v:=congrArg BitVec.toNat e
        change i.proof.length≤13421772800 at admitted
        rwa [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at v
      have dispPC : (Trunc.dispatched s).pc=loc 433 := by change (if _ then _ else _)=_;rw [if_pos mode];rfl
      have r17:= (dispatchFrame s).2.2.2.2.2.2.1
      have failPC : (afterGate (Trunc.dispatched s)).pc=4432 := by rw [gatePC _ dispPC,if_neg (fun eqn=>wrong (r17.symm.trans eqn))];rfl
      rw [show submission.steps .check=7+(4+(3+(submission.steps .check-14))) by decide,
        patchedDispatch s rfl,readShortLength _ dispPC,Normal.check_exit _ false failPC]
      simp [Late.Check.Normal.check_evaluation_pure,wrong,good,Execution.charge]
  · have fail : submission.run .check i=pure ⟨.failure,initialMachine,0,0⟩ := by simp [Submission.run,admitted]
    rw [fail,Late.Check.Normal.check_evaluation_pure]
    have wrong : i.proof.length≠69120 := by intro eq;apply admitted;rw [eq];decide
    simp [wrong]

end CommitGolfCandidate.Trunc
