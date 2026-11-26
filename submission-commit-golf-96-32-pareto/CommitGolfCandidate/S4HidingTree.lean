import CommitGolfCandidate.S4Model
import CommitGolfCandidate.LateHidingTree

set_option Elab.async false
namespace CommitGolfCandidate.S4Hiding
open CommitGolf OracleComp OracleSpec
set_option maxRecDepth 10000
set_option maxHeartbeats 130000
open CommitGolfCandidate.LateHiding (run_mapM run_hash mapM_bound hash_bound run_leaf leaf_bound leafDigest leafLayer leafLayerExcept)

def parents (H : Compression) (h : Nat) (ns : List Late.Digest) :=
  (List.range (S4.width (h+1))).map (fun j=>S4.retained S4.active (h+1) (H (S4.readRow h ns j)))

def levels (H : Compression) : Nat → List Late.Digest → Late.Levels
  | 0,ns => [ns]
  | d+1,ns => ns :: levels H d (parents H (23-d) ns)

theorem run_parents (o : Oracle) (h : Nat) (ns : List Late.Digest) {α : Type}
    (k : List Late.Digest → OracleComp World α) :
    fixedOracleRun o (S4.parentsM S4.active Late.hash h ns >>= k)=fixedOracleRun o (k (parents o.compression h ns)) := by
  unfold S4.parentsM parents
  apply run_mapM
  intro j β rest
  simp only [bind_assoc,pure_bind]
  exact run_hash o _ _

theorem run_levels (o : Oracle) (d : Nat) (ns : List Late.Digest) {α : Type} (k : Late.Levels → OracleComp World α) :
    fixedOracleRun o (S4.levelsM S4.active Late.hash d ns >>= k)=fixedOracleRun o (k (levels o.compression d ns)) := by
  induction d generalizing ns k with
  | zero=>simp [S4.levelsM,levels]
  | succ d ih=>simp only [S4.levelsM,levels,bind_assoc,pure_bind];rw [run_parents,ih]

theorem levels_bound (d : Nat) (ns : List Late.Digest) : PublicQueryBound (S4.levelsM S4.active Late.hash d ns) (S4.parentCost d) := by
  induction d generalizing ns with
  | zero=>trivial
  | succ d ih=>
    unfold S4.levelsM S4.parentsM
    have row (j : Nat) : PublicQueryBound (do return S4.retained S4.active (23-d+1) (← Late.hash (S4.readRow (23-d) ns j))) 1 :=
      public_query_bound_bind (hash_bound _) (fun _=> (show PublicQueryBound (pure _ : OracleComp World Late.Digest) 0 from trivial))
    have endCost (upper : List Late.Digest) : PublicQueryBound (do let t←S4.levelsM S4.active Late.hash d upper;pure (ns::t)) (S4.parentCost d) := by
      simpa only [Nat.add_zero] using public_query_bound_bind (ih upper)
        (fun t=>(show PublicQueryBound (pure (ns::t) : OracleComp World Late.Levels) 0 from trivial))
    have h:=mapM_bound (List.range (S4.width (23-d+1))) _ 1 row _ (S4.parentCost d) (fun upper _=>endCost upper)
    -- The cost uses the same successor height as the interpreter, even off the 24-level schedule.
    simpa only [List.length_range,Nat.one_mul,S4.parentCost] using h

def tree (H : Compression) (m : Message) (s : Late.SaltTape) := levels H 24 (leafLayer H m s)
def treeExceptM (m : Message) (s : Late.SaltTape) (hidden : Index) (digest : Late.Digest) : OracleComp World Late.Levels := do
  let leaves ← (List.finRange LENGTH).mapM fun i=>if i=hidden then (pure digest : OracleComp World Late.Digest) else Late.leafM Late.hash (i.val.testBit 0) (s i) (m i)
  S4.levelsM S4.active Late.hash 24 leaves

attribute [local irreducible] List.finRange S4.parentCost S4.levelsM

theorem run_tree (o : Oracle) (m : Message) (s : Late.SaltTape) {α : Type} (k : Late.Levels→OracleComp World α) :
    fixedOracleRun o (S4.treeM S4.active Late.hash m s >>= k)=fixedOracleRun o (k (tree o.compression m s)) := by
  unfold S4.treeM tree leafLayer
  rw [bind_assoc,run_mapM o (List.finRange LENGTH) _ (fun i=>leafDigest o.compression (i.val.testBit 0) (s i) (m i))
    (fun i _ k=>run_leaf o _ _ _ k),run_levels]

theorem run_tree_except (o : Oracle) (m : Message) (s : Late.SaltTape) (hidden : Index) (digest : Late.Digest) {α : Type}
    (k : Late.Levels→OracleComp World α) :
    fixedOracleRun o (treeExceptM m s hidden digest >>= k)=fixedOracleRun o (k (levels o.compression 24 (leafLayerExcept o.compression m s hidden digest))) := by
  unfold treeExceptM leafLayerExcept
  rw [bind_assoc,run_mapM o (List.finRange LENGTH) _ (fun i=>if i=hidden then digest else leafDigest o.compression (i.val.testBit 0) (s i) (m i))
    (fun i _ k=>by by_cases e:i=hidden
                   · simp only [e,ite_true,pure_bind]
                   · simp only [e,ite_false];exact run_leaf o _ _ _ k),run_levels]

theorem tree_except_bound (m : Message) (s : Late.SaltTape) (hidden : Index) (digest : Late.Digest) :
    PublicQueryBound (treeExceptM m s hidden digest) (5*LENGTH) := by
  have each (i : Index) : PublicQueryBound (if i=hidden then (pure digest : OracleComp World Late.Digest) else Late.leafM Late.hash (i.val.testBit 0) (s i) (m i)) 4 := by
    split
    · trivial
    · exact leaf_bound _ _ _
  have last (r : List Late.Digest) : PublicQueryBound (S4.levelsM S4.active Late.hash 24 r) (S4.parentCost 24) := levels_bound 24 r
  have bound:=mapM_bound (List.finRange LENGTH) _ 4 each (S4.levelsM S4.active Late.hash 24) (S4.parentCost 24) (fun r _=>last r)
  rw [List.length_finRange] at bound
  exact bound.mono (by have:=S4.parentAllowance;omega)

theorem opening_hidden_salt (t : Late.Levels) (s : Late.SaltTape) (ps : Positions) (i : Index) (unopened : i∉ps) (x y : Late.Salt) :
    S4.actualOpening t (Function.update s i x) ps=S4.actualOpening t (Function.update s i y) ps := by
  apply S4.actualOpening_salt_congr;intro j hj
  have ne : j≠i:=fun eq=>unopened (eq ▸ hj)
  rw [Function.update_of_ne ne,Function.update_of_ne ne]
end CommitGolfCandidate.S4Hiding
