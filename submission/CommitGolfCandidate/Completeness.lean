import CommitGolfCandidate.HonestRecords
import CommitGolfCandidate.CheckHonest
import CommitGolfCandidate.InputOrder

/-! Perfect completeness for the scheme derived from the submitted machine images. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

private theorem initial_check_registers (program : Submission) (input : CheckInput) :
    (program.initialState .check input).getReg .x11 = BitVec.ofNat 64 program.layout.commitment ∧
    (program.initialState .check input).getReg .x13 = BitVec.ofNat 64 program.layout.indices ∧
    (program.initialState .check input).getReg .x14 = BitVec.ofNat 64 program.layout.values ∧
    (program.initialState .check input).getReg .x15 = BitVec.ofNat 64 program.layout.proof := by
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem ready_memory (state : MachineState) :
    (checkReadyState (checkLengthState state)).mem = state.mem := rfl

attribute [local irreducible] checkReadyState checkLengthState checkEvaluation

/-- The actual checker accepts the bytes produced by opening any correctly
constructed commitment state, for every requested position set. -/
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
  let initial := submission.initialState .check input
  let ready := checkReadyState (checkLengthState initial)
  let indices : Nat → Index := fun ordinal =>
    ⟨openingIndex positions ordinal, opening_index_bound positions ordinal⟩
  let heap : Nat → Digest := fun slot => readBuffer committed (4294971424+32*slot) 32
  let salts : Index → Digest := fun index => readBuffer committed (5368713248+32*index.val) 32
  have cardinal : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
  have small : positions.card ≤ 16777216 := cardinal
  have registers := check_ready_registers initial
  have loaded := initial_check_registers submission input
  have rootPointer : ready.getReg .x26 = BitVec.ofNat 64 4294971392 := registers.2.2.2.2.1.trans loaded.1
  have valuePointer : ready.getReg .x8 = BitVec.ofNat 64 6039801888 := registers.2.2.1.trans loaded.2.2.1
  have proofPointer : ready.getReg .x25 = BitVec.ofNat 64 10334769184 := registers.2.2.2.1.trans loaded.2.2.2
  have indexPointer : ready.getReg .x24 = BitVec.ofNat 64 5905584160 := registers.2.1.trans loaded.2.1
  have memory : ready.mem = initial.mem := ready_memory initial
  have rootData : readBuffer ready 4294971392 32 = heap 1 := by
    rw [read_buffer_memory_congr _ _ memory]
    exact (check_input_commitment input).trans correct.1
  have indexData (ordinal : Nat) (present : ordinal < positions.card) :
      ready.getMem (BitVec.ofNat 64 (5905584160+8*ordinal)) = BitVec.ofNat 64 (indices ordinal).val := by
    rw [show ready.getMem = initial.getMem from congrArg (fun mem address => mem address) memory]
    exact check_input_position input ordinal present
  have valueData (ordinal : Nat) (present : ordinal < positions.card) (block : Nat) (inside : block < 8) :
      readBuffer ready (6039801888+256*ordinal+32*block) 32 =
        (message (indices ordinal)).extractLsb' (256*block) 256 := by
    rw [read_buffer_memory_congr _ _ memory]
    have value := check_input_value_block input ordinal block present inside
    have indexSame :
        ((positions.attach.sort (fun i j => i.val ≤ j.val))[ordinal]'(by simpa using present)).val =
          indices ordinal := Fin.ext (sorted_value_index positions ordinal present)
    change readBuffer initial (6039801888+256*ordinal+32*block) 32 =
      (message (((positions.attach.sort (fun i j => i.val ≤ j.val))[ordinal]'(by simpa using present)).val)).extractLsb'
        (256*block) 256 at value
    rw [indexSame] at value
    exact value
  have saltData (ordinal : Nat) (present : ordinal < positions.card) :
      readBuffer ready (10334769184+800*ordinal) 32 = salts (indices ordinal) := by
    rw [read_buffer_memory_congr _ _ memory]
    have copied := check_opening_proof_digest trapdoor positions root (message.restrict positions)
      (800*ordinal) (by omega)
    exact copied.trans (opening_output_records committed positions ordinal present).1
  have pathData (ordinal : Nat) (present : ordinal < positions.card) (level : Nat) (inside : level < 24) :
      readBuffer ready (10334769184+800*ordinal+32+32*level) 32 =
        heap (((LENGTH+(indices ordinal).val)/2^level) ^^^ 1) := by
    rw [read_buffer_memory_congr _ _ memory]
    have copied := check_opening_proof_digest trapdoor positions root (message.restrict positions)
      (800*ordinal+32+32*level) (by omega)
    have record := (opening_output_records committed positions ordinal present).2 level inside
    have joined := copied.trans (by simpa only [Nat.add_assoc] using record)
    change readBuffer initial (10334769184+(800*ordinal+32+32*level)) 32 =
      heap (((LENGTH+(indices ordinal).val)/2^level) ^^^ 1) at joined
    simpa only [Nat.add_assoc] using joined
  have accepted := check_loop_honest oracle ready message heap salts indices
    4294971392 6039801888 10334769184 5905584160 positions.card
    registers.1 rootPointer valuePointer proofPointer indexPointer
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by omega) (by omega) (by omega)
    rootData indexData valueData saltData pathData correct.2.2 correct.2.1
  exact (scheme_check_acceptance oracle input).mpr ⟨opening_proof_length trapdoor positions, accepted⟩

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
  apply probEvent_eq_one_iff.mpr
  refine ⟨by simp, ?_⟩
  intro result reached
  simp only [Scheme.honest, mem_support_bind_iff] at reached
  obtain ⟨⟨⟨root, trapdoor⟩, commitCalls⟩, committed, rest⟩ := reached
  rw [opening_scheme_execution trapdoor positions, oracle_run_pure] at rest
  simp only [support_pure, Set.mem_singleton_iff] at rest
  obtain ⟨opened, rfl, rfl⟩ := rest
  exact supported_commit_accepts oracle message ((root, trapdoor), commitCalls) committed positions

end CommitGolfCandidate
