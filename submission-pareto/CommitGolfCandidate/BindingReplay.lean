import CommitGolfCandidate.Binding
import CommitGolfCandidate.CheckHonest
import CommitGolfCandidate.InputOrder
import CommitGolfCandidate.S3LeafProbe
import CommitGolfCandidate.S6Tree

/-! Replay authentication paths through the actual public oracle interface.
The reduction pays for every compression call; it never reads the compression
function directly or assumes a free verification oracle. Every internal node is
the compression reply with its top two bytes cleared (`s6Compress`), so the path
replay clears them too. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp OracleSpec

/-- The two check inputs in the binding game, with their actual supplied bytes. -/
def claimLeft (claim : Scheme.Claim) : CheckInput :=
  ⟨claim.root, claim.positions₀, claim.values₀, claim.proof₀⟩

def claimRight (claim : Scheme.Claim) : CheckInput :=
  ⟨claim.root, claim.positions₁, claim.values₁, claim.proof₁⟩

/-- Replay a salted leaf chain and retain the inputs actually queried. -/
def replayChain : Digest → List Digest → OracleComp World (Digest × List (BitVec 512))
  | state, [] => pure (state, [])
  | state, block :: rest => do
      let input := block ++ state
      let next ← (liftM (World.query (.inr (.inl input))) : OracleComp World Digest)
      let (root, inputs) ← replayChain next rest
      return (root, input :: inputs)

/-- Replay a bottom-up authentication path, retaining its compression inputs.
Each parent is the reply with its top two bytes cleared. -/
def replayPath : Digest → List (Bool × Digest) → OracleComp World (Digest × List (BitVec 512))
  | node, [] => pure (node, [])
  | node, (right, sibling) :: rest => do
      let input := if right then node ++ sibling else sibling ++ node
      let reply ← (liftM (World.query (.inr (.inl input))) : OracleComp World Digest)
      let (root, inputs) ← replayPath (s6Trunc reply) rest
      return (root, input :: inputs)

theorem replay_chain_run (oracle : Oracle) (state : Digest) (blocks : List Digest) :
    oracle.run (replayChain state blocks) =
      pure ((blocks.foldl (combine oracle.compression) state,
        chainInputs oracle.compression state blocks), blocks.length) := by
  induction blocks generalizing state with
  | nil => exact oracle_run_pure _ _
  | cons block rest ih =>
    simp only [replayChain]
    erw [oracle_run_public_bind oracle (.inl (block ++ state))]
    erw [oracle_run_bind, ih]
    simp only [pure_bind, oracle_run_pure]
    simp [Oracle.answer, chainInputs, combine, Nat.add_comm]
    exact ⟨rfl, rfl⟩

theorem replay_path_run (oracle : Oracle) (node : Digest) (path : List (Bool × Digest)) :
    oracle.run (replayPath node path) =
      pure ((climb (s6Compress oracle.compression) node path,
        pathInputs (s6Compress oracle.compression) node path), path.length) := by
  induction path generalizing node with
  | nil => exact oracle_run_pure _ _
  | cons head rest ih =>
    rcases head with ⟨right, sibling⟩
    simp only [replayPath]
    erw [oracle_run_public_bind oracle (.inl (if right then node ++ sibling else sibling ++ node))]
    erw [oracle_run_bind, ih]
    simp only [pure_bind, oracle_run_pure]
    cases right <;> simp [Oracle.answer, pathInputs, climb, combine, s6Compress, Nat.add_comm] <;>
      exact ⟨rfl, rfl⟩

/-- A collision is between distinct queried inputs, not merely a repeated query. -/
def HasCompressionCollision (compress : Compression) (inputs : List (BitVec 512)) : Prop :=
  ∃ input ∈ inputs, ∃ input' ∈ inputs, input ≠ input' ∧ compress input = compress input'

/-- The replay bounds hold structurally for every possible sequence of replies,
not only for replies consistent with a fixed oracle table. -/
theorem replay_chain_query_bound (state : Digest) (blocks : List Digest) :
    IsTotalQueryBound (replayChain state blocks) blocks.length := by
  induction blocks generalizing state with
  | nil => trivial
  | cons block rest ih =>
    simp only [replayChain, bind_pure_comp]
    change IsTotalQueryBound ((liftM (World.query (.inr (.inl (block ++ state)))) :
      OracleComp World Digest) >>= _) (rest.length + 1)
    erw [isTotalQueryBound_query_bind_iff]
    refine ⟨by omega, fun next => ?_⟩
    simpa only [Nat.add_sub_cancel, IsTotalQueryBound, isQueryBound_map_iff] using ih next

theorem replay_path_query_bound (node : Digest) (path : List (Bool × Digest)) :
    IsTotalQueryBound (replayPath node path) path.length := by
  induction path generalizing node with
  | nil => trivial
  | cons head rest ih =>
    rcases head with ⟨right, sibling⟩
    simp only [replayPath, bind_pure_comp]
    change IsTotalQueryBound ((liftM (World.query (.inr (.inl
      (if right then node ++ sibling else sibling ++ node)))) : OracleComp World Digest) >>= _)
      (rest.length + 1)
    erw [isTotalQueryBound_query_bind_iff]
    refine ⟨by omega, fun next => ?_⟩
    simpa only [Nat.add_sub_cancel, IsTotalQueryBound, isQueryBound_map_iff] using
      ih (s6Trunc next)

end CommitGolfCandidate
