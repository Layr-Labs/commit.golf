import CommitGolfCandidate.ChainedRecordedWitness

/-! Conflicting recorded openings expose a chained-final or pinned-leaf collision. -/
namespace CommitGolfCandidate.Chained
open CommitGolf OracleComp OracleSpec
open TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
set_option exponentiation.threshold 2100

abbrev Node := BitVec 238

def nodeDigest (w : Nat) (value : Output) : Node := BitVec.ofNat 238 (lowBits w value).toNat

theorem nodeDigest_injective {w : Nat} (bounded : w ≤ 238) {a b : Output}
    (same : nodeDigest w a = nodeDigest w b) : lowBits w a = lowBits w b := by
  have small (value : Output) : (lowBits w value).toNat < 2^238 :=
    (lowBits w value).isLt.trans_le (Nat.pow_le_pow_right (by decide) bounded)
  have equal := congrArg BitVec.toNat same
  simp only [nodeDigest,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (small a),Nat.mod_eq_of_lt (small b)] at equal
  exact BitVec.eq_of_toNat_eq equal

def pathSeed (node : Nat) (child sibling : Node) : Seed :=
  if node % 2 = 0 then sibling ++ child else child ++ sibling

theorem pathSeed_child {node : Nat} {a b sa sb : Node}
    (same : pathSeed node a sa = pathSeed node b sb) : a = b := by
  by_cases parity : node % 2 = 0
  · simp only [pathSeed,if_pos parity] at same
    have hit := congrArg (fun packed : Seed => packed.extractLsb' 0 238) same
    exact BitVec.extractLsb'_append_eq_right.symm.trans (hit.trans BitVec.extractLsb'_append_eq_right)
  · simp only [pathSeed,if_neg parity] at same
    have hit := congrArg (fun packed : Seed => packed.extractLsb' 238 238) same
    exact BitVec.extractLsb'_append_eq_left.symm.trans (hit.trans BitVec.extractLsb'_append_eq_left)

inductive RecordedPath (enc : Encoding) (calls width : Height → Nat) (rows : List PublicRow) :
    Nat → Nat → Nat → Node → Node → Prop where
  | done (node level : Nat) (digest : Node) : RecordedPath enc calls width rows node level 0 digest digest
  | step {node level remaining : Nat} {child sibling root : Node} {h : Height} {values : Nat → Output}
      (height : h.val = level)
      (chain : RecordedChain enc calls rows h (pathSeed node child sibling) values)
      (next : RecordedPath enc calls width rows (node/2) (level+1) remaining
        (nodeDigest (width h) (values (calls h-1))) root) :
      RecordedPath enc calls width rows node level (remaining+1) child root

theorem RecordedPath.mono {enc calls width earlier later node level remaining start root}
    (included : ∀ row ∈ earlier, row ∈ later)
    (path : RecordedPath enc calls width earlier node level remaining start root) :
    RecordedPath enc calls width later node level remaining start root := by
  induction path with
  | done node level digest => exact .done node level digest
  | step height chain _ ih => exact .step height (chain.mono included) ih

theorem RecordedPath.compare {enc calls width rows node level remaining a b root}
    (bounded : ∀ h, width h ≤ 238)
    (left : RecordedPath enc calls width rows node level remaining a root)
    (right : RecordedPath enc calls width rows node level remaining b root) :
    RecordedCollision enc calls width rows ∨ a = b := by
  induction remaining generalizing node level a b root with
  | zero =>
    cases left
    cases right
    exact Or.inr rfl
  | succ remaining ih =>
    cases left with
    | @step _ _ _ _ sa _ ha va heightA chainA tailA =>
      cases right with
      | @step _ _ _ _ sb _ hb vb heightB chainB tailB =>
        have heights : ha = hb := Fin.ext (heightA.trans heightB.symm)
        subst hb
        rcases ih tailA tailB with collision | sameParent
        · exact Or.inl collision
        by_cases sameInput : pathSeed node a sa = pathSeed node b sb
        · exact Or.inr (pathSeed_child sameInput)
        · exact Or.inl ⟨ha,_,_,va,vb,sameInput,chainA,chainB,nodeDigest_injective (bounded ha) sameParent⟩

structure RecordedOpening (enc : Encoding) (calls width : Height → Nat)
    (oracle : Oracle) (index : Index) (entry : Entry) (root : Node) (rows : List PublicRow) where
  nonce : TwoPermutationPrototype.Words 2
  first : PublicRow.permutation (pinnedFirstRow oracle.permutation (entryWords entry)).1
    (pinnedFirstRow oracle.permutation (entryWords entry)).2 ∈ rows
  second : PublicRow.permutation
    (pinnedSecondRow oracle.permutation index nonce (pinnedFirstRow oracle.permutation (entryWords entry)).2
      (entryWords entry)).1
    (pinnedSecondRow oracle.permutation index nonce (pinnedFirstRow oracle.permutation (entryWords entry)).2
      (entryWords entry)).2 ∈ rows
  path : RecordedPath enc calls width rows (LENGTH+index.val) 0 LOG_LENGTH
    (nodeDigest 238 (outputDigest (pinnedSecondRow oracle.permutation index nonce
      (pinnedFirstRow oracle.permutation (entryWords entry)).2 (entryWords entry)).2)) root

theorem recorded_openings_conflict {enc calls width} (bounded : ∀ h, width h ≤ 238)
    (oracle : Oracle) (index : Index) (root : Node) (a b : Entry) (different : a ≠ b)
    (earlier later : List PublicRow) (left : RecordedOpening enc calls width oracle index a root earlier)
    (right : RecordedOpening enc calls width oracle index b root later) :
    RecordedFailure enc calls width (earlier++later) := by
  have pa := left.path.mono (fun _ present => List.mem_append_left later present)
  have pb := right.path.mono (fun _ present => List.mem_append_right earlier present)
  rcases pa.compare bounded pb with collision | sameLeaf
  · exact Or.inr collision
  · left
    refine ⟨oracle.permutation,index,left.nonce,right.nonce,entryWords a,entryWords b,
      List.mem_append_left later left.first,List.mem_append_right earlier right.first,
      List.mem_append_left later left.second,List.mem_append_right earlier right.second,?_,
      fun equal => different (entry_words_injective equal)⟩
    have same := congrArg BitVec.toNat (nodeDigest_injective (by decide : 238 ≤ 238) sameLeaf)
    unfold leafDigestW truncDigestW
    apply congrArg (BitVec.ofNat 256)
    simpa [lowBits,BitVec.extractLsb'] using same

end CommitGolfCandidate.Chained
