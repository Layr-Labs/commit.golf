import CommitGolfCandidate.TruncReplayLow
import CommitGolfCandidate.BindingReplay
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv OracleComp OracleSpec
set_option maxRecDepth 10000
set_option maxHeartbeats 55000
attribute [local irreducible] lowerHash climb storeNode pathInputs

def queryChildren (input : CheckInput) (p : Nat) : OracleComp World Children := do
  let l := firstAt input (2*p)
  let r := firstAt input (2*p+1)
  let a ← queryLow input (l.getD 0)
  let b ← queryLow input (r.getD 0)
  return ⟨l.map (fun _ => a),r.map (fun _ => b)⟩

private theorem lookupMap {α : Type} (f : Nat → α) (row : Option Nat) :
    (row.map fun _ => f (row.getD 0)) = row.map f := by cases row <;> rfl

theorem childrenRun (o : Oracle) (input : CheckInput) (p : Nat) :
    o.run (queryChildren input p) = pure (childrenAt o.compression input p,40) := by
  simp only [queryChildren,oracle_run_bind,lowRun,pure_bind,oracle_run_pure]
  unfold childrenAt
  simp only [lookupMap]

theorem childrenBound (input : CheckInput) (p : Nat) : IsTotalQueryBound (queryChildren input p) 40 := by
  unfold queryChildren
  change IsTotalQueryBound (_ >>= _) (20+20)
  apply isTotalQueryBound_bind (lowBound _ _)
  intro a
  simp only [bind_pure_comp,IsTotalQueryBound,isQueryBound_map_iff]
  exact lowBound _ _

end CommitGolfCandidate.Trunc
