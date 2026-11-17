import CommitGolfCandidate.HidingTree
import CommitGolfCandidate.OpeningOutput
import CommitGolfCandidate.CompressionSampling
import CommitGolfCandidate.QueryBudget
import CommitGolfCandidate.NonceEncoding
import CommitGolfCandidate.S3LeafProbe
import CommitGolf.Hiding

/-! Machine-independent base of the stage-3 hiding argument: the reference
transcript of the salted tree (permutation leaves, compression parents), the
reference game, and fixed-oracle run lemmas. Nothing here depends on the commit
image, so the statistical argument builds without the machine refinement. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv OracleComp OracleSpec OracleComp.DeferredSampling

theorem fixed_oracle_run_bind (oracle : Oracle) {α β : Type}
    (computation : OracleComp World α) (next : α → OracleComp World β) :
    fixedOracleRun oracle (computation >>= next) =
      (fixedOracleRun oracle computation >>= fun value => fixedOracleRun oracle (next value)) := by
  simp only [fixedOracleRun, oracle_run_bind, map_bind, map_pure, bind_map_left]
  simp only [map_eq_bind_pure_comp]
  apply bind_congr
  intro first
  cases first
  apply bind_congr
  intro second
  cases second
  rfl

theorem fixed_oracle_run_map (oracle : Oracle) {α β : Type}
    (f : α → β) (computation : OracleComp World α) :
    fixedOracleRun oracle (f <$> computation) = f <$> fixedOracleRun oracle computation := by
  simp only [fixedOracleRun, oracle_run_map, Functor.map_map]

theorem fixed_oracle_run_coins (oracle : Oracle) {α : Type} (coins : ProbComp α) :
    fixedOracleRun oracle (liftM coins : OracleComp World α) = coins := by
  rw [fixedOracleRun, oracle_run_coins, Functor.map_map]
  exact id_map coins

/-- Every result of a fixed-oracle run is a syntactically possible result. -/
theorem fixed_oracle_run_support (oracle : Oracle) {α : Type} (computation : OracleComp World α) :
    support (fixedOracleRun oracle computation) ⊆ support computation := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro result reached
    rw [fixed_oracle_run_pure] at reached
    simpa using reached
  | query_bind query next ih =>
    intro result reached
    cases query with
    | inl coins =>
      have reached' : result ∈ support ((liftM (unifSpec.query coins) : ProbComp _) >>=
          fun answer => fixedOracleRun oracle (next answer)) :=
        Eq.mp (congrArg (fun run => result ∈ support run)
          (fixed_oracle_run_private oracle coins next)) reached
      obtain ⟨answer, _, inner⟩ := (mem_support_bind_iff _ _ _).mp reached'
      exact (mem_support_bind_iff _ _ _).mpr ⟨answer, mem_support_query _ _, ih answer inner⟩
    | inr asked =>
      have reached' : result ∈ support (fixedOracleRun oracle (next (oracle.answer (m := Id) asked))) :=
        Eq.mp (congrArg (fun run => result ∈ support run)
          (fixed_oracle_run_public oracle asked next)) reached
      exact (mem_support_bind_iff _ _ _).mpr
        ⟨oracle.answer (m := Id) asked, mem_support_query _ _, ih _ reached'⟩

/-- Oracle program for a compression chain, used only in the security proof. -/
def chainBlocks : List Digest → Digest → OracleComp World Digest
  | [], state => pure state
  | block :: rest, state => do
      let answer ← (liftM (World.query (.inr (.inl (block ++ state)))) : OracleComp World Digest)
      chainBlocks rest answer

theorem chain_blocks_bound (blocks : List Digest) (state : Digest) :
    PublicQueryBound (chainBlocks blocks state) blocks.length := by
  induction blocks generalizing state with
  | nil => trivial
  | cons block rest ih =>
    change 1 ≤ rest.length+1 ∧ ∀ answer,
      PublicQueryBound (chainBlocks rest answer) (rest.length+1-1)
    exact ⟨by omega, fun answer => by simpa only [Nat.add_sub_cancel] using ih answer⟩

theorem fixed_chain_blocks (oracle : Oracle) (blocks : List Digest) (state : Digest)
    {α : Type} (next : Digest → OracleComp World α) :
    fixedOracleRun oracle (chainBlocks blocks state >>= next) =
      fixedOracleRun oracle (next (blocks.foldl
        (fun state block => combine oracle.compression state block) state)) := by
  induction blocks generalizing state with
  | nil => rfl
  | cons block rest ih =>
    simp only [chainBlocks, bind_assoc, List.foldl_cons]
    erw [fixed_oracle_run_public]
    exact ih (oracle.compression (block ++ state))

/-- The stage-3 leaf program (two forward permutation queries) under a fixed oracle. -/
theorem fixed_s3_hash_leaf (oracle : Oracle) (salt : Digest) (value : Entry) :
    fixedOracleRun oracle (s3HashLeaf salt value) =
      pure (s3LeafDigest oracle.permutation salt value) := by
  rw [fixedOracleRun, s3_hash_leaf_run, map_pure]

theorem s3_hash_leaf_public_bound (salt : Digest) (value : Entry) :
    PublicQueryBound (s3HashLeaf salt value) 2 :=
  public_query_bound_of_total (s3_hash_leaf_bound salt value)

/-- An opening record contains its leaf's salt followed by its 24 siblings.
`part = 0` selects the salt; parts 1 through 24 select siblings. -/
def referenceOpeningDigest (heap : Nat → Digest) (salt : Index → Digest)
    (positions : Positions) (ordinal part : Nat) : Digest :=
  let index : Index := ⟨openingIndex positions ordinal, opening_index_bound positions ordinal⟩
  if part = 0 then salt index
  else heap (((LENGTH+index.val)/2^(part-1)) ^^^ 1)

/-- Exact little-endian proof bytes, in the ABI's sorted position order. -/
def referenceOpening (heap : Nat → Digest) (salt : Index → Digest)
    (positions : Positions) : Proof :=
  (List.range (800*positions.card)).map fun offset =>
    (referenceOpeningDigest heap salt positions (offset/800) ((offset%800)/32)).extractLsb'
      (8*(offset%32)) 8

theorem reference_opening_length (heap : Nat → Digest) (salt : Index → Digest)
    (positions : Positions) : (referenceOpening heap salt positions).length = 800*positions.card := by
  simp only [referenceOpening, List.length_map, List.length_range]

/-- Public transcript of the mathematical salted tree for one fixed salt vector. -/
def referenceTranscript (compress : Compression) (permutation : Perm) (message : Message)
    (salt : Index → Digest) (positions : Positions) : Commitment × Proof :=
  let heap := saltedHeap compress permutation message salt
  (heap 1, referenceOpening heap salt positions)

/-- The reference game retains both oracle-adaptive adversary stages; only honest
machine execution is replaced by its proved transcript formula. -/
def referenceHiding {AdversaryState Output : Type} {openingSize : Nat}
    (oracle : Oracle) (adversary : Hiding.HidingAdversary AdversaryState Output openingSize)
    (selectSecond : Bool) : ProbComp Output := do
  let challenge ← fixedOracleRun oracle adversary.choose
  let message := if selectSecond then challenge.message₁ else challenge.message₀
  let salt ← $ᵗ (Index → Nonce192)
  let (root, proof) := referenceTranscript oracle.compression oracle.permutation message
    (expandNonceVector salt) challenge.positions
  fixedOracleRun oracle (adversary.observe challenge.aux root proof)

end CommitGolfCandidate
