import CommitGolfCandidate.PairPairs
import CommitGolfCandidate.PairRows
import CommitGolfCandidate.PairStart
namespace CommitGolfCandidate.PairCap
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp Batch
set_option maxRecDepth 8000
set_option maxHeartbeats 180000
private theorem validOfPairs (o : Oracle) (input : CheckInput) (length : input.proof.length=69120)
    (agree : ∀ r<128, let i:=openingIndex input.positions r
      (childrenAt o.compression input (i/131072)).child (i.testBit 16)=some (lowerHash o.compression input r))
    (root : referenceHeap o.compression 128 (capTable o.compression input) 1=input.commitment) :
    BatchValid o.compression input := ⟨length,agree,root⟩

private theorem rootOfPairs (o : Oracle) (input : CheckInput) (v : BatchValid o.compression input) :
    referenceHeap o.compression 128 (capTable o.compression input) 1=input.commitment := v.root

attribute [local irreducible] Late.Check.Normal.checkEvaluation execute Late.Check.Micro.initialRows lowerHash

private theorem finishBatch (o : Oracle) (input : CheckInput) (b : input.positions.card=BATCH)
    (size : input.proof.length=69120) (first : MachineState)
    (start : RecordInvariant o.compression input 0 first) (budget : Nat) (big : 10000000≤budget) :
    (obs o budget first).1≠.unfinished ∧ (obs o budget first).2≤2815 ∧
      ((obs o budget first).1=.success ↔ BatchValid o.compression input) := by
  rcases allRows o input b 128 0 (by decide) first start with ⟨invalid,k,hk,q,hq,reject⟩|⟨s,k,hk,rows,done⟩
  · have eqn := reject (budget-k)
    rw [show k+(budget-k)=budget by omega] at eqn
    rw [eqn]
    exact ⟨(by decide : Exit.failure≠Exit.unfinished),by omega,⟨fun bad=>False.elim ((by decide : Exit.failure≠.success) bad),fun v=>False.elim (invalid v)⟩⟩
  · obtain ⟨init,cap⟩:=pairStart o input s done
    obtain ⟨t,j,q,hj,hq,pairs,last⟩:=allPairs o input 128 0 (by decide) _ cap
    obtain ⟨jump,capped⟩:=completedCap o input t last
    obtain ⟨ex,fin,term,root⟩:=finishCap o input (t.setPC 5492) capped
    have complete := runs_finish (runs_trans (runs_trans (runs_trans rows init) pairs) jump) fin
    let need:=(((k+11)+j)+1)+2571
    have enough : need≤budget := by dsimp [need];omega
    have all := complete (budget-need)
    rw [show k+11+j+1+2571+(budget-need)=budget by dsimp [need];omega] at all
    rw [all]
    exact ⟨term,by omega,⟨fun ok=>validOfPairs o input size (completedRecords o input s done) (root.mp ok),fun v=>root.mpr (rootOfPairs o input v)⟩⟩

private theorem evaluationAt (o : Oracle) (s : MachineState) (fuel : Nat) (valid : Prop)
    (h : (obs o fuel s).1≠.unfinished ∧ (obs o fuel s).2≤2815 ∧ ((obs o fuel s).1=.success ↔ valid)) :
    let out:=Late.Check.Normal.checkEvaluation o (execute Late.Check.Normal.checkerImage fuel s false)
    out.1.exit≠.unfinished ∧ out.2≤2815 ∧ (out.1.exit=.success ↔ valid) := h

theorem batchEvaluation : Late.Check.BatchEvaluation := by
  intro o input b size
  dsimp only;rw [Late.Check.Normal.checker_image_eq]
  exact evaluationAt o _ _ _ (finishBatch o input b size _ (startInvariant o input b size)
    (Late.submission.steps .check-17) (by decide))
end CommitGolfCandidate.PairCap
