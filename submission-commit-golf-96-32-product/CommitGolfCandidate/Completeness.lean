import CommitGolfCandidate.HonestRecords
import CommitGolfCandidate.CheckHonest
import CommitGolfCandidate.CheckInputSound
import CommitGolfCandidate.InputOrder

/-! Perfect completeness for the scheme derived from the submitted machine images. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

attribute [local irreducible] checkEvaluation openingInitializedState openingPositionState openingExitState

set_option maxRecDepth 200000

/-- The actual checker accepts the bytes produced by opening any correctly
constructed commitment state, for every requested position set: the transmitted cap
hashes to the commitment, and every record climbs 17 levels to its cap node. -/
theorem honest_check_accepts (oracle : Oracle) (message : Message)
    (committed : MachineState) (correct : CommittedState oracle message committed)
    (positions : Positions) :
    let root := readBuffer committed submission.layout.commitment 32
    let trapdoor := readBuffer committed submission.layout.trapdoor submission.sizes.trapdoor
    (oracle.eval (submission.scheme.check root positions (message.restrict positions)
      (submission.readProof (openingResult trapdoor positions)))).1 = true := by
  let root := readBuffer committed submission.layout.commitment 32
  let trapdoor := readBuffer committed submission.layout.trapdoor submission.sizes.trapdoor
  let input : CheckInput :=
    ⟨root, positions, message.restrict positions, submission.readProof (openingResult trapdoor positions)⟩
  let opened := (openingResult trapdoor positions).state
  have cardinal : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
  have small : positions.card ≤ 16777216 := cardinal
  -- every proof digest the checker reads is the one opening wrote
  have copied24 (offset : Nat) (inside : offset+24 ≤ 4096+568*positions.card) :
      readBuffer (submission.initialState .check input) (submission.layout.proof+offset) 24 =
        readBuffer opened (submission.layout.proof+offset) 24 := by
    unfold readBuffer
    apply congrArg (BitVec.ofNat 192)
    apply Finset.sum_congr rfl
    intro j hj
    rw [Nat.add_assoc, check_opening_proof_byte trapdoor positions root (message.restrict positions) (offset+j)
      (by have := Finset.mem_range.mp hj; omega)]
  have copied (offset : Nat) (inside : offset+32 ≤ 4096+568*positions.card) :
      readBuffer (submission.initialState .check input) (submission.layout.proof+offset) 32 =
        readBuffer opened (submission.layout.proof+offset) 32 :=
    check_opening_proof_digest trapdoor positions root (message.restrict positions) offset inside
  have capCopied (node : Nat) (inside : node < 128) :
      recordCap input node = heapCap committed 4294971424 node := by
    unfold recordCap
    rw [copied (32*node) (by omega)]
    exact opening_proof_cap committed positions node inside
  apply check_input_complete oracle input (opening_proof_length trapdoor positions)
  · intro _
    change capRoot oracle.compression (recordCap input) = root
    rw [show root = capRoot oracle.compression (heapCap committed 4294971424) from correct.1]
    apply cap_congr
    intro node below
    exact capCopied node (by change node < 2*64 at below; omega)
  · intro ordinal present
    have present' : ordinal < positions.card := present
    let index : Index := ⟨openingIndex positions ordinal, opening_index_bound positions ordinal⟩
    have indexBound : index.val < 16777216 := index.isLt
    have record := opening_proof_authenticates oracle message committed correct positions ordinal present
    have value : recordValue input ordinal = message index := by
      unfold recordValue
      rw [dif_pos present]
      exact congrArg message (Fin.ext (sorted_value_index positions ordinal present))
    have salt : recordSalt input ordinal =
        saltState (readBuffer opened (submission.layout.proof+4096+568*ordinal) 24) := by
      unfold recordSalt
      have := copied24 (4096+568*ordinal) (by omega)
      simp only [Nat.add_assoc] at this ⊢
      rw [this]
    have path : recordPath (recordIndex input ordinal) (recordSibling input ordinal) =
        openingProofPath opened (submission.layout.proof+4096+568*ordinal) index.val := by
      unfold recordPath openingProofPath
      apply List.map_congr_left
      intro level member
      have inside := List.mem_range.mp member
      have := copied (4096+568*ordinal+24+32*level) (by change level < 17 at inside; omega)
      unfold recordSibling
      simp only [Nat.add_assoc] at this ⊢
      rw [this]
      rfl
    have cap : recordCap input ((recordIndex input ordinal).val / 2^PATH_LEVELS) =
        heapDigest committed 4294971424 (128 + index.val/2^PATH_LEVELS) := by
      have below : index.val / 2^PATH_LEVELS < 128 := by
        change index.val / 2^17 < 128; omega
      rw [show (recordIndex input ordinal).val = index.val from rfl, capCopied _ below]
      simp only [heapCap, if_pos below]
    unfold recordRoot
    rw [value, salt, path, cap]
    exact record

private theorem scheme_commit (program : Submission) (message : Message) :
    program.scheme.commit message = program.readCommit <$> program.run .commit message := rfl

private theorem supported_commit_accepts (oracle : Oracle) (message : Message)
    (result : (Commitment × submission.scheme.Trapdoor) × Nat)
    (reachable : result ∈ support (oracle.run (submission.scheme.commit message)))
    (positions : Positions) :
    (oracle.eval (submission.scheme.check result.1.1 positions (message.restrict positions)
      (submission.readProof (openingResult result.1.2 positions)))).1 = true := by
  rw [scheme_commit] at reachable
  change result ∈ support (oracle.run (submission.readCommit <$>
    submission.run .commit (message : Input submission.sizes .commit))) at reachable
  rw [oracle_run_map] at reachable
  simp only [support_map] at reachable
  obtain ⟨execution, reached, rfl⟩ := reachable
  exact honest_check_accepts oracle message execution.1.state
    (commit_run_matches oracle message execution reached) positions

/-- Perfect completeness of the submitted machine-derived scheme, for every fixed
oracle, message, and opening set, with probability one over the actual private coins. -/
theorem submission_completeness : submission.scheme.Completeness := by
  intro oracle message positions
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  simp only [Scheme.honest, mem_support_bind_iff] at reached
  obtain ⟨⟨⟨root, trapdoor⟩, commitCalls⟩, committed, rest⟩ := reached
  rw [opening_scheme_execution trapdoor positions, oracle_run_pure] at rest
  simp only [support_pure, Set.mem_singleton_iff] at rest
  obtain ⟨opened, rfl, rfl⟩ := rest
  exact supported_commit_accepts oracle message ((root, trapdoor), commitCalls) committed positions

end CommitGolfCandidate
