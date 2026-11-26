import CommitGolfCandidate.PairBatchModel
import CommitGolfCandidate.BindingReplay
namespace CommitGolfCandidate.PairCap
open CommitGolf CommitGolf.Riscv OracleComp OracleSpec
set_option maxRecDepth 10000
attribute [local irreducible] firstAt lowerHash

/-- For the reduction only, replay both child records even when one is absent.
This fixes the reconstruction cost at forty queries per cap pair. -/
def queryLow (input : CheckInput) (r : Nat) : OracleComp World Digest := do
  let leaf ← replayLeaf (recordIndex input r) (batchSalt input r) (recordValue input r)
  let node ← replayPath leaf.1 (recordPathPrefix 16 (recordIndex input r) (lowerSibling input r))
  return node.1

theorem lowRun (o : Oracle) (input : CheckInput) (r : Nat) :
    o.run (queryLow input r) = pure (lowerHash o.compression input r,20) := by
  simp only [queryLow,oracle_run_bind,replay_leaf_run,pure_bind,replay_path_run,oracle_run_pure]
  simp [lowerHash,recordAncestor,record_path_prefix_length]

theorem lowBound (input : CheckInput) (r : Nat) : IsTotalQueryBound (queryLow input r) 20 := by
  unfold queryLow
  change IsTotalQueryBound (_ >>= _) (4+16)
  apply isTotalQueryBound_bind (replay_leaf_query_bound _ _ _)
  intro leaf
  simp only [bind_pure_comp,IsTotalQueryBound,isQueryBound_map_iff]
  exact replay_path_query_bound _ _

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

def queryParent (input : CheckInput) (p : Nat) : OracleComp World Digest := do
  let ch ← queryChildren input p
  let slot := supplied input p
  let d ← liftM (World.query (.inr (.inl (padInput ((ch.right.getD slot) ++ (ch.left.getD slot))))))
  return if ch.left.isNone && ch.right.isNone then slot else d

theorem parentRun (o : Oracle) (input : CheckInput) (p : Nat) :
    o.run (queryParent input p) = pure (parentAt o.compression input p,41) := by
  simp only [queryParent, oracle_run_bind,childrenRun,pure_bind]
  erw [oracle_run_public_bind]
  simp only [oracle_run_pure,pure_bind]
  unfold parentAt Children.parent
  cases (childrenAt o.compression input p).left <;> cases (childrenAt o.compression input p).right <;> rfl

theorem parentBound (input : CheckInput) (p : Nat) : IsTotalQueryBound (queryParent input p) 41 := by
  unfold queryParent
  change IsTotalQueryBound (_ >>= _) (40+1)
  apply isTotalQueryBound_bind (childrenBound _ _)
  intro ch
  erw [isTotalQueryBound_query_bind_iff]
  exact ⟨by decide,fun _ => trivial⟩

def parents (input : CheckInput) : Nat → OracleComp World (Nat → Digest)
  | 0 => pure fun _ => 0
  | k+1 => do
    let tab ← parents input k
    let d ← queryParent input k
    return fun i => if i=k then d else tab i

theorem parentsRun (o : Oracle) (input : CheckInput) (n : Nat) :
    o.run (parents input n) = pure (fun i => if i<n then parentAt o.compression input i else 0,41*n) := by
  induction n with
  | zero => simp [parents,oracle_run_pure]
  | succ n ih =>
    simp only [parents,oracle_run_bind,ih,pure_bind,parentRun,oracle_run_pure]
    congr 1
    apply Prod.ext
    · funext i
      by_cases eqn : i=n
      · subst i; simp
      · by_cases lt : i<n <;> simp [eqn,lt,show (i<n+1) ↔ i<n by omega]
    · dsimp; omega

theorem parentsBound (input : CheckInput) (n : Nat) : IsTotalQueryBound (parents input n) (41*n) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    rw [show 41*(n+1)=41*n+41 by omega]
    apply isTotalQueryBound_bind ih
    intro tab
    simp only [bind_pure_comp,IsTotalQueryBound,isQueryBound_map_iff]
    exact parentBound _ _

end CommitGolfCandidate.PairCap
