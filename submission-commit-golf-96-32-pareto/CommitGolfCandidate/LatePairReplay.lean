import CommitGolfCandidate.LatePathReplay
namespace CommitGolfCandidate.Late.Check
open CommitGolf OracleComp OracleSpec PairCap
set_option maxRecDepth 10000
attribute [local irreducible] first lower

def queryLow (input : CheckInput) (r : Nat) : OracleComp World Digest := do
  let i := recordIndex input.positions r
  let leaf ← Late.replay (i.val.testBit 0) (salt input r) (recordValue input r)
  let node ← replayPath leaf.1 (path i 16 (sibling input r))
  return node.1

theorem lowRun (o : Oracle) (input : CheckInput) (r : Nat) :
    o.run (queryLow input r) = pure (lower o.compression input r 16,20) := by
  simp only [queryLow,oracle_run_bind,Late.replay_run,pure_bind,replay_path_run,oracle_run_pure]
  simp [lower,path]

theorem lowBound (input : CheckInput) (r : Nat) : IsTotalQueryBound (queryLow input r) 20 := by
  unfold queryLow
  change IsTotalQueryBound (_ >>= _) (4+16)
  apply isTotalQueryBound_bind (replay_bound _ _ _)
  intro val
  simp only [bind_pure_comp, IsTotalQueryBound,isQueryBound_map_iff]
  simpa [path,IsTotalQueryBound] using replay_path_query_bound val.1 (path (recordIndex input.positions r) 16 (sibling input r))

def queryChildren (input : CheckInput) (p : Nat) : OracleComp World Children := do
  let l := first input (2*p)
  let r := first input (2*p+1)
  let a ← queryLow input (l.getD 0)
  let b ← queryLow input (r.getD 0)
  return ⟨l.map (fun _ => a),r.map (fun _ => b)⟩

private theorem lookupMap {α : Type} (f : Nat → α) (row : Option Nat) :
    (row.map fun _ => f (row.getD 0)) = row.map f := by cases row <;> rfl

theorem childrenRun (o : Oracle) (input : CheckInput) (p : Nat) :
    o.run (queryChildren input p) = pure (children o.compression input p,40) := by
  simp only [queryChildren,oracle_run_bind,lowRun,pure_bind,oracle_run_pure]
  unfold children
  exact congrArg (fun c : Children => pure (c,40)) (congrArg₂ Children.mk
    (lookupMap (fun r => lower o.compression input r 16) (first input (2*p)))
    (lookupMap (fun r => lower o.compression input r 16) (first input (2*p+1))))

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
    o.run (queryParent input p) = pure (parent o.compression input p,41) := by
  simp only [queryParent, oracle_run_bind,childrenRun,pure_bind]
  erw [oracle_run_public_bind]
  simp only [oracle_run_pure,pure_bind]
  unfold parent Children.parent
  cases (children o.compression input p).left <;> cases (children o.compression input p).right <;> rfl

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
    o.run (parents input n) = pure (fun i => if i<n then parent o.compression input i else 0,41*n) := by
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

end CommitGolfCandidate.Late.Check
