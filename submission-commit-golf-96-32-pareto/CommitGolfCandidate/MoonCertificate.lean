import CommitGolfCandidate.MoonCommitRef
import CommitGolfCandidate.MoonOpenRef
import CommitGolfCandidate.MoonCheckRef
import CommitGolfCandidate.MoonHiding

/-! Complete certificate assembly for the submitted RV64IM machine images and their derived
vector commitment scheme (`r = 0`, `c = 8` pure binary tree, uniform `238`-bit masking on
`L0..L23`, `121`-bit early-tagged independent salts, two-end 6-bit packed tail stream,
`66,672`-byte proof at `k = 128`). -/
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

private theorem splitSalts121_eq (packed : BitVec (128 * LENGTH)) :
    splitSalts121 packed = fun i : Index => (packed.extractLsb' (128 * i.val) 128).extractLsb' 0 121 :=
  rfl

/-! ### 2. Exact Honest Machine & Derived Scheme Composition -/

private theorem honestMachine_run_exact (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (message : Message) (positions : Positions) :
    ∃ (resOf : BitVec (128 * LENGTH) → MachineResult),
      EvalDistEq (oracle.run (submission.honestMachine message positions))
        (($ᵗ BitVec (128 * LENGTH)) >>= fun packed =>
          pure (resOf packed, 83886079)) ∧
      ∀ packed,
        (resOf packed).success = true ∧
        (resOf packed).commitCycles = 1075446281 ∧
        (positions.card = BATCH → (resOf packed).openingCycles ≤ 136000) := by
  obtain ⟨finalState, hcommit_run, _⟩ := commit_run_exact h768 oracle message
  let cExec (packed : BitVec (128 * LENGTH)) : Execution :=
    ⟨Riscv.Exit.success, finalState packed, 1075446281, 83886079⟩
  let td (packed : BitVec (128 * LENGTH)) : BitVec (8 * submission.sizes.trapdoor) :=
    (submission.readCommit (cExec packed)).2
  have hopen_all : ∀ packed,
      ∃ oExec : Execution,
        oracle.run (submission.run .opening (td packed, positions)) = pure (oExec, 0) ∧
        oExec.exit = Riscv.Exit.success ∧
        oExec.oracleCalls = 0 ∧
        (oExec.state.getReg .x11).toNat ≤ submission.sizes.proof ∧
        (positions.card = BATCH → oExec.cycles ≤ 136000) :=
    fun packed => opening_run_deterministic oracle (td packed) positions
  let oExec (packed : BitVec (128 * LENGTH)) : Execution := Classical.choose (hopen_all packed)
  let resOf (packed : BitVec (128 * LENGTH)) : MachineResult := {
    success := (cExec packed).exit == Riscv.Exit.success && submission.openingSucceeded (oExec packed)
    commitCycles := (cExec packed).cycles
    openingCycles := (oExec packed).cycles
    proofBytes := (submission.readProof (oExec packed)).length
  }
  refine ⟨resOf, ?_, ?_⟩
  · unfold Submission.honestMachine
    rw [oracle_run_bind]
    refine (hcommit_run.bind_left _).trans ?_
    rw [bind_assoc]
    refine evalDistEq_of_eq ?_
    apply bind_congr; intro packed
    simp only [pure_bind]
    have hrun_inner : oracle.run (
        let (_, trapdoor) := submission.readCommit (cExec packed)
        do let opened ← submission.run .opening (trapdoor, positions)
           return {
             success := (cExec packed).exit == Riscv.Exit.success && submission.openingSucceeded opened
             commitCycles := (cExec packed).cycles
             openingCycles := opened.cycles
             proofBytes := (submission.readProof opened).length }) =
        pure (resOf packed, 0) := by
      have ho_run := (Classical.choose_spec (hopen_all packed)).1
      change oracle.run ((submission.run .opening (td packed, positions)) >>= fun opened => pure _) = _
      rw [oracle_run_bind, ho_run]
      simp only [pure_bind, oracle_run_pure, Nat.add_zero]
      rfl
    rw [hrun_inner]
    simp only [pure_bind, Nat.add_zero]
  · intro packed
    have hsp := Classical.choose_spec (hopen_all packed)
    refine ⟨?_, rfl, hsp.2.2.2.2⟩
    have hsuc : submission.openingSucceeded (oExec packed) = true := by
      unfold Submission.openingSucceeded
      rw [hsp.2.1, show (Riscv.Exit.success == Riscv.Exit.success) = true from rfl,
        Bool.true_and, decide_eq_true_eq]
      exact hsp.2.2.2.1
    simp only [resOf, cExec, hsuc]
    rfl

private noncomputable def honestResultOf (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (message : Message) (positions : Positions)
    (packed : BitVec (128 * LENGTH)) : Scheme.HonestResult :=
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  let salts := splitSalts121 packed
  let rt : Commitment := rootVal c96 message salts
  let pf : Proof := referenceProof (nodeVal c96 message salts) salts positions
  let ev := oracle.eval (submission.scheme.check rt positions (message.restrict positions) pf)
  { accepted := ev.1
    commitCalls := 83886079
    openCalls := 0
    checkCalls := ev.2
    proofBytes := pf.length }

private theorem scheme_honest_exact (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (message : Message) (positions : Positions) :
    EvalDistEq (submission.scheme.honest oracle message positions)
      (($ᵗ BitVec (128 * LENGTH)) >>= fun packed =>
        pure (honestResultOf h768 oracle message positions packed)) := by
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  obtain ⟨finalState, hcommit_run, hcommit_spec⟩ := commit_run_exact h768 oracle message
  unfold Scheme.honest
  have hcommit_scheme :
      EvalDistEq (oracle.run (submission.scheme.commit message))
        (($ᵗ BitVec (128 * LENGTH)) >>= fun packed =>
          pure ((submission.readCommit ⟨Riscv.Exit.success, finalState packed, 1075446281, 83886079⟩ :
            Commitment × submission.scheme.Trapdoor), 83886079)) := by
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
  apply bind_congr; intro packed
  refine (pure_bind _ _).trans ?_
  have hspec := hcommit_spec packed
  let cExec : Execution := ⟨Riscv.Exit.success, finalState packed, 1075446281, 83886079⟩
  let salts := splitSalts121 packed
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
    (fun packed => (resOf packed, 83886079))
    (fun result => result.1.success = true)
    (fun packed => (hspec packed).1)

theorem submission_termination (h768 : COMPRESSION_INPUT_LENGTH = 768) :
    submission.Termination := by
  intro oracle program input
  cases program with
  | commit =>
    exact commit_termination h768 oracle input
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
    (fun packed => (check_honest_accepts h768 oracle message (splitSalts121 packed) positions).1)

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
    (fun packed => ⟨by unfold honestResultOf COMMIT_BUDGET LENGTH LOG_LENGTH; dsimp only; decide,
      Nat.zero_le _,
      (check_honest_accepts h768 oracle message (splitSalts121 packed) positions).2⟩)

theorem submission_proof_size (h768 : COMPRESSION_INPUT_LENGTH = 768) :
    submission.scheme.ProofSize 66672 := by
  intro oracle message positions hcard
  rw [(scheme_honest_exact h768 oracle message positions).prEvent_eq
    (fun result => result.proofBytes ≤ 66672)]
  exact prEvent_uniform_bind_pure_eq_one (honestResultOf h768 oracle message positions)
    (fun result => result.proofBytes ≤ 66672)
    (fun packed => referenceProof_length_128_le _ (splitSalts121 packed) positions hcard)

theorem submission_prover_cycles (h768 : COMPRESSION_INPUT_LENGTH = 768) :
    submission.ProverCycles 1075446281 136000 := by
  intro oracle message positions hcard
  obtain ⟨resOf, hrun, hspec⟩ := honestMachine_run_exact h768 oracle message positions
  rw [hrun.prEvent_eq
    (fun result => result.1.commitCycles ≤ 1075446281 ∧ result.1.openingCycles ≤ 136000)]
  exact prEvent_uniform_bind_pure_eq_one
    (fun packed => (resOf packed, 83886079))
    (fun result => result.1.commitCycles ≤ 1075446281 ∧ result.1.openingCycles ≤ 136000)
    (fun packed => ⟨le_of_eq (hspec packed).2.1, (hspec packed).2.2 hcard⟩)

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
  apply bind_congr; intro packed
  refine (pure_bind _ _).trans ?_
  dsimp only
  rw [fixed_oracle_run_bind]
  obtain ⟨oExec, ho_run, _, _, _, _⟩ := opening_run_deterministic oracle (trapdoorOf packed) positions
  have hpf := opening_honest_proof h768 oracle message (splitSalts121 packed)
    (trapdoorOf packed) (htd packed) positions oExec ho_run
  have hopen : fixedOracleRun oracle (submission.scheme.opening (trapdoorOf packed) positions) =
      pure (referenceProof (nodeVal (fun x => oracle.compression (x.cast h768.symm)) message
        (splitSalts121 packed)) (splitSalts121 packed) positions) := by
    simp only [fixedOracleRun, Submission.scheme, oracle_run_map, ho_run, map_pure, hpf]
  rw [hopen, pure_bind, fixed_oracle_run_pure]
  rfl

theorem submission_hiding (h768 : COMPRESSION_INPUT_LENGTH = 768) :
    submission.scheme.Hiding HIDING_ERROR :=
  hiding_of_refines h768 (honest_transcript_refines h768)

/-! ### 5. Complete Certificate -/

theorem moon_certificate (h768 : COMPRESSION_INPUT_LENGTH = 768) :
    CommitGolf.Certificate submission 66672 1075446281 136000 where
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
