import CommitGolfCandidate.LateModel
import CommitGolfCandidate.QueryBudget

namespace CommitGolfCandidate.Late
open CommitGolf OracleComp

theorem hash_bound (x : Block) : PublicQueryBound (hash x) 1 :=
  ⟨show 1 ≤ 1 from le_rfl, fun _ => trivial⟩

theorem leaf_bound (odd : Bool) (s : Salt) (v : Entry) :
    PublicQueryBound (leafM hash odd s v) 4 :=
  public_query_bound_bind (hash_bound _) fun _ =>
    public_query_bound_bind (hash_bound _) fun _ =>
      public_query_bound_bind (hash_bound _) fun _ => hash_bound _

private theorem mapM_bound_cont {α β γ : Type} (xs : List α)
    (f : α → OracleComp World β) (q : Nat) (hf : ∀ x, PublicQueryBound (f x) q)
    (k : List β → OracleComp World γ) (n : Nat)
    (hk : ∀ ys, ys.length = xs.length → PublicQueryBound (k ys) n) :
    PublicQueryBound (xs.mapM f >>= k) (q*xs.length+n) := by
  induction xs generalizing k with
  | nil => simpa using hk [] rfl
  | cons x xs ih =>
    simp only [List.mapM_cons, bind_assoc, pure_bind, List.length_cons, Nat.mul_add,
      Nat.mul_one]
    have rest (y : β) := ih (fun ys => k (y::ys)) (fun ys h => hk (y::ys) (by simp [h]))
    convert public_query_bound_bind (hf x) rest using 1 <;> omega

private theorem parent_bound_cont {α : Type} (height : Nat) (xs : List Digest)
    (k : List Digest → OracleComp World α) (n : Nat)
    (hk : ∀ ps, ps.length = xs.length/2 → PublicQueryBound (k ps) n) :
    PublicQueryBound (parentsM hash height xs >>= k) (xs.length/2+n) := by
  match xs with
  | [] => simpa [parentsM] using hk [] rfl
  | [_] => simpa [parentsM] using hk [] (by simp)
  | l::r::tail =>
    simp only [parentsM, bind_assoc, pure_bind]
    have rest (p : Digest) := parent_bound_cont height tail (fun ps => k (cut height p::ps)) n
      (fun ps h => hk (cut height p::ps) (by simp only [List.length_cons, h]; omega))
    convert public_query_bound_bind (hash_bound (parentBlock l r)) rest using 1 <;>
      simp only [List.length_cons] <;> omega

private theorem levels_bound (d : Nat) (xs : List Digest) (size : xs.length = 2^d) :
    PublicQueryBound (levelsM hash d xs) (2^d-1) := by
  induction d generalizing xs with
  | zero => trivial
  | succ d ih =>
    simp only [levelsM]
    have pow : 0 < 2^d := by positivity
    have half : xs.length / 2 = 2^d := by rw [size, Nat.pow_succ]; omega
    have next (ps : List Digest) (hp : ps.length = xs.length/2) :
        PublicQueryBound (do let ls ← levelsM hash d ps; pure (xs::ls)) (2^d-1) := by
      simpa using public_query_bound_bind (ih ps (hp.trans half))
        (fun ls => (show PublicQueryBound (pure (xs::ls) : OracleComp World Levels) 0 from trivial))
    convert parent_bound_cont _ xs _ _ next using 1
    rw [half, Nat.pow_succ]
    omega

private theorem coins_free {α : Type} (c : ProbComp α) :
    PublicQueryBound (liftM c : OracleComp World α) 0 := by
  induction c using OracleComp.inductionOn with
  | pure x => rw [liftM_pure]; trivial
  | query_bind query k ih =>
    rw [liftM_bind]
    exact ⟨show 0 ≤ 0 from le_rfl, ih⟩

attribute [local irreducible] List.range

theorem sample_bound : PublicQueryBound sampleSalts 0 := by
  let xs := List.range (LENGTH/2)
  have bound := mapM_bound_cont xs (fun _ => drawPair) 0 (fun _ => coins_free ($ᵗ PairCoins : ProbComp PairCoins))
    (fun ws => (pure (fun i : Index => pairSalts (ws[i.val/2]?.getD 0) (i.val.testBit 0)) :
      OracleComp World SaltTape)) 0 (fun _ _ => trivial)
  simp only [Nat.zero_mul, Nat.add_zero] at bound
  exact bound

attribute [local irreducible] List.finRange PublicQueryBound

theorem tree_bound (m : Message) (s : SaltTape) :
    PublicQueryBound (treeM hash m s) (5*LENGTH-1) := by
  let f (i : Index) := leafM hash (i.val.testBit 0) (s i) (m i)
  have budget (ys : List Digest) (h : ys.length = (List.finRange LENGTH).length) :
      PublicQueryBound (levelsM hash LOG_LENGTH ys) (LENGTH-1) := by
    rw [List.length_finRange] at h
    exact levels_bound LOG_LENGTH ys h
  have result := mapM_bound_cont (List.finRange LENGTH) f 4
    (fun i => leaf_bound _ _ _) (levelsM hash LOG_LENGTH) (LENGTH-1) budget
  rw [List.length_finRange] at result
  have cost : 4*LENGTH + (LENGTH-1) = 5*LENGTH-1 := by decide
  rw [cost] at result
  exact result

theorem transcript_below (m : Message) (s : SaltTape) :
    PublicQueryBound (treeM hash m s) (2^47 - 1) :=
  @PublicQueryBound.mono _ (treeM hash m s) _ _ (tree_bound m s) (by decide)

theorem commit_bound (check : Checker) (m : Message) :
    PublicQueryBound ((scheme check).commit m) (5*LENGTH-1) := by
  apply @public_query_bound_bind _ _ sampleSalts _ 0 (5*LENGTH-1) sample_bound
  intro s
  apply @public_query_bound_bind _ _ (treeM hash m s) _ (5*LENGTH-1) 0 (tree_bound m s)
  intro tree
  unfold PublicQueryBound
  trivial

theorem opening_bound (check : Checker) (td : (scheme check).Trapdoor) (p : Positions) :
    PublicQueryBound ((scheme check).opening td p) 0 := by
  unfold PublicQueryBound
  trivial

end CommitGolfCandidate.Late
