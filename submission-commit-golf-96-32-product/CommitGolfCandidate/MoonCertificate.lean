import CommitGolfCandidate.MoonCommitRef
import CommitGolfCandidate.MoonOpenRef
import CommitGolfCandidate.MoonCheckRef
import CommitGolfCandidate.MoonHiding

/-! Complete certificate assembly for the submitted RV64IM machine images and their derived
vector commitment scheme. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

/-! ### 1. Probability-One Event Helpers -/

private theorem evalDistEq_of_eq {α : Type} {a b : ProbComp α} (h : a = b) :
    EvalDistEq a b :=
  h ▸ EvalDistEq.refl a

private theorem prEvent_pure_eq_one {α : Type} (a : α) (p : α → Prop) (h : p a) :
    Pr{let x ← (pure a : ProbComp α)}[p x] = 1 := by
  classical
  rw [prEvent_pure]; simp [h]

private theorem prEvent_uniform_bind_pure_eq_one {α β : Type} [SampleableType α]
    (f : α → β) (p : β → Prop) (h : ∀ a, p (f a)) :
    Pr{let y ← (($ᵗ α) >>= fun a => pure (f a))}[p y] = 1 := by
  have h1 : Pr{let y ← (($ᵗ α) >>= fun a => pure (f a))}[p y] =
      Pr{let y ← (($ᵗ α) >>= fun _ => (pure () : ProbComp Unit))}[True] := by
    apply prEvent_bind_congr ($ᵗ α) (fun a => pure (f a)) (fun _ => pure ()) p (fun _ => True)
    intro a
    classical
    rw [prEvent_pure, prEvent_pure]; simp [h a]
  rw [h1]
  have h2 : (fun _ : Unit => True) <$> (($ᵗ α) >>= fun _ => (pure () : ProbComp Unit)) =
      (($ᵗ α) >>= fun _ => (pure True : ProbComp Prop)) := by
    simp only [map_bind, map_pure]
  change prEvent ((fun _ : Unit => True) <$> (($ᵗ α) >>= fun _ => (pure () : ProbComp Unit))) = 1
  rw [h2, prEvent_def, OracleComp.evalDist_bind_const]
  change prEvent (pure True : ProbComp Prop) = 1
  rw [prEvent_pure_prop]; simp

/-! ### 2. Exact Honest Machine & Derived Scheme Composition -/

private theorem honestMachine_run_exact (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (message : Message) (positions : Positions) :
    ∃ (resOf : (Fin (LENGTH / 2) → PairRand) → MachineResult),
      EvalDistEq (oracle.run (submission.honestMachine message positions))
        (($ᵗ (Fin (LENGTH / 2) → PairRand)) >>= fun rand =>
          pure (resOf rand, 78453292)) ∧
      ∀ rand,
        (resOf rand).success = true ∧
        (resOf rand).commitCycles = 850256070 ∧
        (positions.card = BATCH → (resOf rand).openingCycles ≤ 160000) := by
  obtain ⟨finalState, hcommit_run, _⟩ := commit_run_exact h768 oracle message
  let cExec (rand : Fin (LENGTH / 2) → PairRand) : Execution :=
    ⟨Riscv.Exit.success, finalState rand, 850256070, 78453292⟩
  let td (rand : Fin (LENGTH / 2) → PairRand) : BitVec (8 * submission.sizes.trapdoor) :=
    (submission.readCommit (cExec rand)).2
  have hopen_all : ∀ rand,
      ∃ oExec : Execution,
        oracle.run (submission.run .opening (td rand, positions)) = pure (oExec, 0) ∧
        oExec.exit = Riscv.Exit.success ∧
        oExec.oracleCalls = 0 ∧
        (oExec.state.getReg .x11).toNat ≤ submission.sizes.proof ∧
        (positions.card = BATCH → oExec.cycles ≤ 160000) :=
    fun rand => opening_run_deterministic oracle (td rand) positions
  let oExec (rand : Fin (LENGTH / 2) → PairRand) : Execution := Classical.choose (hopen_all rand)
  let resOf (rand : Fin (LENGTH / 2) → PairRand) : MachineResult := {
    success := (cExec rand).exit == Riscv.Exit.success && submission.openingSucceeded (oExec rand)
    commitCycles := (cExec rand).cycles
    openingCycles := (oExec rand).cycles
    proofBytes := (submission.readProof (oExec rand)).length
  }
  refine ⟨resOf, ?_, ?_⟩
  · unfold Submission.honestMachine
    rw [oracle_run_bind]
    refine (hcommit_run.bind_left _).trans ?_
    rw [bind_assoc]
    refine evalDistEq_of_eq ?_
    apply bind_congr; intro rand
    simp only [pure_bind]
    have hrun_inner : oracle.run (
        let (_, trapdoor) := submission.readCommit (cExec rand)
        do let opened ← submission.run .opening (trapdoor, positions)
           return {
             success := (cExec rand).exit == Riscv.Exit.success && submission.openingSucceeded opened
             commitCycles := (cExec rand).cycles
             openingCycles := opened.cycles
             proofBytes := (submission.readProof opened).length }) =
        pure (resOf rand, 0) := by
      have ho_run := (Classical.choose_spec (hopen_all rand)).1
      change oracle.run ((submission.run .opening (td rand, positions)) >>= fun opened => pure _) = _
      rw [oracle_run_bind, ho_run]
      simp only [pure_bind, oracle_run_pure, Nat.add_zero]
      rfl
    rw [hrun_inner]
    simp only [pure_bind, Nat.add_zero]
  · intro rand
    have hsp := Classical.choose_spec (hopen_all rand)
    refine ⟨?_, rfl, hsp.2.2.2.2⟩
    have hsuc : submission.openingSucceeded (oExec rand) = true := by
      unfold Submission.openingSucceeded
      rw [hsp.2.1, show (Riscv.Exit.success == Riscv.Exit.success) = true from rfl,
        Bool.true_and, decide_eq_true_eq]
      exact hsp.2.2.2.1
    simp only [resOf, cExec, hsuc]
    rfl

private noncomputable def honestResultOf (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (message : Message) (positions : Positions)
    (rand : Fin (LENGTH / 2) → PairRand) : Scheme.HonestResult :=
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  let salts := pairSalts rand
  let rt : Commitment := rootVal c96 message salts
  let pf : Proof := referenceProof (nodeVal c96 message salts) salts positions
  let ev := oracle.eval (submission.scheme.check rt positions (message.restrict positions) pf)
  { accepted := ev.1
    commitCalls := 78453292
    openCalls := 0
    checkCalls := ev.2
    proofBytes := pf.length }

private theorem scheme_honest_exact (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (message : Message) (positions : Positions) :
    EvalDistEq (submission.scheme.honest oracle message positions)
      (($ᵗ (Fin (LENGTH / 2) → PairRand)) >>= fun rand =>
        pure (honestResultOf h768 oracle message positions rand)) := by
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  obtain ⟨finalState, hcommit_run, hcommit_spec⟩ := commit_run_exact h768 oracle message
  unfold Scheme.honest
  have hcommit_scheme :
      EvalDistEq (oracle.run (submission.scheme.commit message))
        (($ᵗ (Fin (LENGTH / 2) → PairRand)) >>= fun rand =>
          pure ((submission.readCommit ⟨Riscv.Exit.success, finalState rand, 850256070, 78453292⟩ :
            Commitment × submission.scheme.Trapdoor), 78453292)) := by
    let rc : Execution × ℕ → (Commitment × submission.scheme.Trapdoor) × ℕ :=
      fun p => (submission.readCommit p.1, p.2)
    have hmap : oracle.run (submission.scheme.commit message) =
        rc <$> oracle.run (submission.run .commit message) := by
      simp only [Submission.scheme, oracle_run_map, rc]
    rw [hmap]
    refine (hcommit_run.map rc).trans ?_
    exact evalDistEq_of_eq ((map_bind _ _ _).trans (bind_congr fun _ => map_pure _ _))
  change EvalDistEq ((oracle.run (submission.scheme.commit message)) >>= _) _
  refine (hcommit_scheme.bind_left _).trans ?_
  refine evalDistEq_of_eq ?_
  refine (bind_assoc _ _ _).trans ?_
  apply bind_congr; intro rand
  refine (pure_bind _ _).trans ?_
  have hspec := hcommit_spec rand
  let cExec : Execution := ⟨Riscv.Exit.success, finalState rand, 850256070, 78453292⟩
  let salts := pairSalts rand
  let rt : Commitment := rootVal c96 message salts
  let td : submission.scheme.Trapdoor := (submission.readCommit cExec).2
  have hrc : (submission.readCommit cExec : Commitment × submission.scheme.Trapdoor) = (rt, td) :=
    Prod.ext hspec.1 rfl
  rw [hrc]
  dsimp only
  obtain ⟨oExec, ho_run, _, _, _, _⟩ := opening_run_deterministic oracle td positions
  have hpf := opening_honest_proof h768 oracle message salts td hspec.2 positions oExec ho_run
  have hopen_scheme : oracle.run (submission.scheme.opening td positions) =
      pure (referenceProof (nodeVal c96 message salts) salts positions, 0) := by
    simp only [Submission.scheme, oracle_run_map, ho_run, map_pure, hpf]; rfl
  rw [hopen_scheme, pure_bind]
  rfl

/-! ### 3. Machine Success, Termination, Completeness, Budgets, Proof Size, and Cycles -/

theorem submission_machine_success (h768 : COMPRESSION_INPUT_LENGTH = 768) :
    submission.MachineSuccess := by
  intro oracle message positions
  obtain ⟨resOf, hrun, hspec⟩ := honestMachine_run_exact h768 oracle message positions
  rw [hrun.prEvent_eq (fun result => result.1.success = true)]
  exact prEvent_uniform_bind_pure_eq_one
    (fun rand => (resOf rand, 78453292))
    (fun result => result.1.success = true)
    (fun rand => (hspec rand).1)

theorem submission_termination (h768 : COMPRESSION_INPUT_LENGTH = 768) :
    submission.Termination := by
  intro oracle program input
  cases program with
  | commit =>
    obtain ⟨finalState, hrun, _⟩ := commit_run_exact h768 oracle input
    rw [hrun.prEvent_eq (fun result => result.1.exit ≠ Riscv.Exit.unfinished)]
    let f : (Fin (LENGTH / 2) → PairRand) → Execution × ℕ :=
      fun rand => (({ exit := Riscv.Exit.success, state := finalState rand,
                      cycles := 850256070, oracleCalls := 78453292 } : Execution), 78453292)
    exact prEvent_uniform_bind_pure_eq_one f
      (fun result => result.1.exit ≠ Riscv.Exit.unfinished)
      (fun _ => by dsimp only [f]; decide)
  | opening =>
    rcases input with ⟨trapdoor, positions⟩
    obtain ⟨exec, hrun, hexit, _, _, _⟩ := opening_run_deterministic oracle trapdoor positions
    rw [hrun]
    exact prEvent_pure_eq_one (exec, 0)
      (fun result => result.1.exit ≠ Riscv.Exit.unfinished)
      (by rw [hexit]; decide)
  | check =>
    obtain ⟨exec, hrun, hexit, _⟩ := check_run_termination h768 oracle input
    rw [hrun]
    exact prEvent_pure_eq_one (exec, exec.oracleCalls)
      (fun result => result.1.exit ≠ Riscv.Exit.unfinished)
      hexit

theorem submission_completeness (h768 : COMPRESSION_INPUT_LENGTH = 768) :
    submission.scheme.Completeness := by
  intro oracle message positions
  rw [(scheme_honest_exact h768 oracle message positions).prEvent_eq
    (fun result => result.accepted = true)]
  exact prEvent_uniform_bind_pure_eq_one (honestResultOf h768 oracle message positions)
    (fun result => result.accepted = true)
    (fun rand => (check_honest_accepts h768 oracle message (pairSalts rand) positions).1)

theorem submission_honest_budgets (h768 : COMPRESSION_INPUT_LENGTH = 768) :
    submission.scheme.HonestBudgets := by
  intro oracle message positions
  rw [(scheme_honest_exact h768 oracle message positions).prEvent_eq
    (fun result =>
      result.commitCalls ≤ COMMIT_BUDGET ∧
      result.openCalls ≤ OPEN_BUDGET positions.card ∧
      result.checkCalls ≤ CHECK_BUDGET positions.card)]
  exact prEvent_uniform_bind_pure_eq_one (honestResultOf h768 oracle message positions)
    (fun result =>
      result.commitCalls ≤ COMMIT_BUDGET ∧
      result.openCalls ≤ OPEN_BUDGET positions.card ∧
      result.checkCalls ≤ CHECK_BUDGET positions.card)
    (fun rand => ⟨by unfold honestResultOf COMMIT_BUDGET LENGTH LOG_LENGTH; dsimp only; decide,
      Nat.zero_le _,
      (check_honest_accepts h768 oracle message (pairSalts rand) positions).2⟩)

theorem submission_proof_size (h768 : COMPRESSION_INPUT_LENGTH = 768) :
    submission.scheme.ProofSize 69365 := by
  intro oracle message positions hcard
  rw [(scheme_honest_exact h768 oracle message positions).prEvent_eq
    (fun result => result.proofBytes ≤ 69365)]
  exact prEvent_uniform_bind_pure_eq_one (honestResultOf h768 oracle message positions)
    (fun result => result.proofBytes ≤ 69365)
    (fun rand => referenceProof_length_128_le _ (pairSalts rand) positions hcard)

theorem submission_prover_cycles (h768 : COMPRESSION_INPUT_LENGTH = 768) :
    submission.ProverCycles 850256070 160000 := by
  intro oracle message positions hcard
  obtain ⟨resOf, hrun, hspec⟩ := honestMachine_run_exact h768 oracle message positions
  rw [hrun.prEvent_eq
    (fun result => result.1.commitCycles ≤ 850256070 ∧ result.1.openingCycles ≤ 160000)]
  exact prEvent_uniform_bind_pure_eq_one
    (fun rand => (resOf rand, 78453292))
    (fun result => result.1.commitCycles ≤ 850256070 ∧ result.1.openingCycles ≤ 160000)
    (fun rand => ⟨le_of_eq (hspec rand).2.1, (hspec rand).2.2 hcard⟩)

/-! ### 4. Adaptive Position Binding & Statistical Hiding -/

theorem submission_binding (h768 : COMPRESSION_INPUT_LENGTH = 768) :
    submission.scheme.Binding :=
  binding_of_check_sound h768 (check_sound h768)

theorem honest_transcript_refines (h768 : COMPRESSION_INPUT_LENGTH = 768) :
    HonestTranscriptRefines h768 := by
  intro oracle message positions
  unfold honestTranscript
  obtain ⟨trapdoorOf, hcommit_run, htd⟩ := commit_oracle_run_exact h768 oracle message
  rw [fixed_oracle_run_bind]
  refine (hcommit_run.bind_left _).trans ?_
  refine evalDistEq_of_eq ?_
  refine (bind_assoc _ _ _).trans ?_
  apply bind_congr; intro rand
  refine (pure_bind _ _).trans ?_
  dsimp only
  rw [fixed_oracle_run_bind]
  obtain ⟨oExec, ho_run, _, _, _, _⟩ := opening_run_deterministic oracle (trapdoorOf rand) positions
  have hpf := opening_honest_proof h768 oracle message (pairSalts rand)
    (trapdoorOf rand) (htd rand) positions oExec ho_run
  have hopen : fixedOracleRun oracle (submission.scheme.opening (trapdoorOf rand) positions) =
      pure (referenceProof (nodeVal (fun x => oracle.compression (x.cast h768.symm)) message
        (pairSalts rand)) (pairSalts rand) positions) := by
    simp only [fixedOracleRun, Submission.scheme, oracle_run_map, ho_run, map_pure, hpf]
  rw [hopen, pure_bind, fixed_oracle_run_pure]
  rfl

theorem submission_hiding (h768 : COMPRESSION_INPUT_LENGTH = 768) :
    submission.scheme.Hiding HIDING_ERROR :=
  hiding_of_refines h768 (honest_transcript_refines h768)

/-! ### 5. Complete Certificate -/

theorem moon_certificate (h768 : COMPRESSION_INPUT_LENGTH = 768) :
    CommitGolf.Certificate submission 69365 850256070 160000 where
  admission := submission_admission
  machineSuccess := submission_machine_success h768
  termination := submission_termination h768
  completeness := submission_completeness h768
  honestBudgets := submission_honest_budgets h768
  proofSize := submission_proof_size h768
  proverCycles := submission_prover_cycles h768
  binding := submission_binding h768
  hidingProperty := submission_hiding h768

end CommitGolfCandidate
