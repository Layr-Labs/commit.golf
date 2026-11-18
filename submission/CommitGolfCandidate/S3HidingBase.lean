import CommitGolfCandidate.S6Opening
import CommitGolfCandidate.CompressionSampling
import CommitGolfCandidate.QueryBudget
import CommitGolfCandidate.S4Gen
import CommitGolf.Hiding

/-! Machine-independent base of the hiding argument: the reference transcript of
the tree (tagged permutation leaves, group nodes, truncated compression parents),
the reference games, and fixed-oracle run lemmas. Nothing here depends on the
commit image, so the statistical argument builds without the machine refinement. -/
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

/-- The reference game with uniform nonces. It retains both oracle-adaptive adversary
stages; only honest machine execution is replaced by its proved transcript formula. -/
def referenceHiding {AdversaryState Output : Type} {openingSize : Nat}
    (oracle : Oracle) (adversary : Hiding.HidingAdversary AdversaryState Output openingSize)
    (selectSecond : Bool) : ProbComp Output := do
  let challenge ← fixedOracleRun oracle adversary.choose
  let message := if selectSecond then challenge.message₁ else challenge.message₀
  let nonce ← $ᵗ (Index → Nonce128)
  let (root, proof) := referenceTranscript oracle.compression oracle.permutation message
    (expandTaggedVector nonce) challenge.positions
  fixedOracleRun oracle (adversary.observe challenge.aux root proof)

/-- The reference game the machine plays: the 16-byte nonces are generated from one uniform
32-byte seed by the permutation in counter mode (`s4GenNonce`, `S4Gen`) and tagged with the
leaf address (`expandTaggedVector`). Both adversary stages and the shared oracle are those of
`referenceHiding`. -/
def referenceHidingGen {AdversaryState Output : Type} {openingSize : Nat}
    (oracle : Oracle) (adversary : Hiding.HidingAdversary AdversaryState Output openingSize)
    (selectSecond : Bool) : ProbComp Output := do
  let challenge ← fixedOracleRun oracle adversary.choose
  let message := if selectSecond then challenge.message₁ else challenge.message₀
  let seed ← $ᵗ BitVec 256
  let (root, proof) := referenceTranscript oracle.compression oracle.permutation message
    (expandTaggedVector (s4GenNonce oracle.permutation seed)) challenge.positions
  fixedOracleRun oracle (adversary.observe challenge.aux root proof)

end CommitGolfCandidate
