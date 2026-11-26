import CommitGolfCandidate.S5Model
import CommitGolfCandidate.LateHidingTree
namespace CommitGolfCandidate.S5Hiding
open CommitGolf OracleComp OracleSpec
set_option maxRecDepth 10000
set_option maxHeartbeats 130000
open CommitGolfCandidate.LateHiding (run_mapM run_hash mapM_bound hash_bound run_leaf leaf_bound leafDigest leafLayer leafLayerExcept)

def parents (H : Compression) (h : Nat) (ns : List Late.Digest) :=
  (List.range (S4.width (h+1))).map (S5.parentM (M:=Id) H h ns)

def levels (H : Compression) : Nat → List Late.Digest → Late.Levels
  | 0,ns => [ns]
  | d+1,ns => ns :: levels H d (parents H (23-d) ns)

theorem run_chain (o : Oracle) (h : Chained.Height) (seed : Chained.Seed) (n : Nat) {α : Type}
    (k : Late.Digest→OracleComp World α) :
    fixedOracleRun o (S5.chainM Late.hash h seed n >>= k)=fixedOracleRun o (k (S5.chainM (M:=Id) o.compression h seed n)) := by
  induction n generalizing k with
  | zero=>exact run_hash .. 
  | succ j ih=>simp only [S5.chainM,bind_assoc];rw [ih];exact run_hash .. 

theorem run_parent (o : Oracle) (d : Nat) (ns : List Late.Digest) (j : Nat) {α : Type} (k : Late.Digest→OracleComp World α) :
    fixedOracleRun o (S5.parentM Late.hash d ns j >>= k)=fixedOracleRun o (k (S5.parentM (M:=Id) o.compression d ns j)) := by
  by_cases bottom : d=0
  · simp only [S5.parentM,bottom,ite_true];exact run_hash ..
  · simp only [S5.parentM,bottom,ite_false,bind_assoc,pure_bind];rw [run_chain];rfl

theorem run_parents (o : Oracle) (h : Nat) (ns : List Late.Digest) {α : Type}
    (k : List Late.Digest→OracleComp World α) :
    fixedOracleRun o (S5.parentsM Late.hash h ns >>= k)=fixedOracleRun o (k (parents o.compression h ns)) := by
  apply run_mapM;intro j β rest;exact run_parent o h ns j rest

theorem chain_bound (h : Chained.Height) (seed : Chained.Seed) (n : Nat) :
    PublicQueryBound (S5.chainM Late.hash h seed n) (n+1) := by
  induction n with
  | zero=>exact hash_bound _
  | succ n ih=>exact public_query_bound_bind ih (fun _=>hash_bound _)

theorem parent_bound (d : Nat) (ns : List Late.Digest) (j : Nat) :
    PublicQueryBound (S5.parentM Late.hash d ns j) (Chained.calls (S5.height d)) := by
  by_cases bottom : d=0
  · subst d;exact hash_bound _
  · unfold S5.parentM;rw [if_neg bottom]
    have joined:=public_query_bound_bind (chain_bound (S5.height d) ((ns[S4.radix d*j+1]?.getD 0)++(ns[S4.radix d*j]?.getD 0)) (Chained.calls (S5.height d)-1))
      (fun v=>show PublicQueryBound (pure (Chained.storeReply (S5.height d) v) : OracleComp World _) 0 from trivial)
    convert joined using 1
    have :=Chained.calls_positive (S5.height d);omega

theorem run_levels (o : Oracle) (d : Nat) (ns : List Late.Digest) {α : Type} (k : Late.Levels → OracleComp World α) :
    fixedOracleRun o (S5.levelsM Late.hash d ns >>= k)=fixedOracleRun o (k (levels o.compression d ns)) := by
  induction d generalizing ns k with
  | zero=>simp [S5.levelsM,levels]
  | succ d ih=>simp only [S5.levelsM,levels,bind_assoc,pure_bind];rw [run_parents,ih]

theorem levels_bound (d : Nat) (ns : List Late.Digest) : PublicQueryBound (S5.levelsM Late.hash d ns) (S5.parentCost d) := by
  induction d generalizing ns with
  | zero=>trivial
  | succ d ih=>
    simp only [S5.levelsM,S5.parentsM]
    have endCost (upper : List Late.Digest) : PublicQueryBound (do let t←S5.levelsM Late.hash d upper;pure (ns::t)) (S5.parentCost d) := by
      simpa only [Nat.add_zero] using public_query_bound_bind (ih upper)
        (fun t=>(show PublicQueryBound (pure (ns::t) : OracleComp World Late.Levels) 0 from trivial))
    have h:=mapM_bound (List.range (S4.width (23-d+1))) _ (Chained.calls (S5.height (23-d))) (parent_bound (23-d) ns) _ (S5.parentCost d) (fun upper _=>endCost upper)
    -- The cost uses the same successor height as the interpreter, even off the 24-level schedule.
    simpa only [List.length_range,Nat.mul_comm,S5.parentCost] using h

def tree (H : Compression) (m : Message) (s : Late.SaltTape) := levels H 24 (leafLayer H m s)
def treeExceptM (m : Message) (s : Late.SaltTape) (hidden : Index) (digest : Late.Digest) : OracleComp World Late.Levels := do
  let leaves ← (List.finRange LENGTH).mapM fun i=>if i=hidden then (pure digest : OracleComp World Late.Digest) else Late.leafM Late.hash (i.val.testBit 0) (s i) (m i)
  S5.levelsM Late.hash 24 leaves

attribute [local irreducible] List.finRange S5.parentCost S5.levelsM

theorem run_tree (o : Oracle) (m : Message) (s : Late.SaltTape) {α : Type} (k : Late.Levels→OracleComp World α) :
    fixedOracleRun o (S5.treeM Late.hash m s >>= k)=fixedOracleRun o (k (tree o.compression m s)) := by
  unfold S5.treeM tree leafLayer
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
  have last (r : List Late.Digest) : PublicQueryBound (S5.levelsM Late.hash 24 r) (S5.parentCost 24) := levels_bound 24 r
  have bound:=mapM_bound (List.finRange LENGTH) _ 4 each (S5.levelsM Late.hash 24) (S5.parentCost 24) (fun r _=>last r)
  rw [List.length_finRange] at bound
  exact bound.mono (by have:=S5.parentAllowance;omega)

theorem opening_hidden_salt (t : Late.Levels) (s : Late.SaltTape) (ps : Positions) (i : Index) (unopened : i∉ps) (x y : Late.Salt) :
    S5.opening t (Function.update s i x) ps=S5.opening t (Function.update s i y) ps := by
  apply S5.opening_congr;intro j hj
  have ne : j≠i:=fun eq=>unopened (eq ▸ hj)
  rw [Function.update_of_ne ne,Function.update_of_ne ne]
end CommitGolfCandidate.S5Hiding
