import CommitGolfCandidate.MoonCommitQueue
import CommitGolfCandidate.CompressionSampling

/-! Complete `commit` execution composition for the pure 3-ary FIFO queue tree:
proves `commit_run_exact` (`814,006,332` cycles, `75,497,472` compression calls, exact `rootVal`
and `CommittedTrapdoor`), `commit_oracle_run_exact`, and `commit_termination`. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

private theorem commit_det_run_combine (oracle : Oracle) (s0 s1 sfin : MachineState)
    (hr1 : DetRun oracle (submission.image .commit) s0 201588752 s1 671350800 67108864)
    (hrun23 : ∀ extra,
      oracle.run (execute (submission.image .commit) (25198610 + extra) s1 true) =
        pure (⟨.success, sfin, 83918866, 8388608⟩, 8388608)) :
    oracle.run (execute (submission.image .commit) (submission.steps .commit - 16793626) s0 true) =
      pure (⟨.success, sfin, 755269666, 75497472⟩, 75497472) := by
  have hsc : submission.steps .commit = 4294967296 := by decide
  have hrem : submission.steps .commit - 16793626 =
      201588752 + (25198610 + (submission.steps .commit - 243580988)) := by omega
  rw [hrem, hr1 (25198610 + (submission.steps .commit - 243580988)),
    hrun23 (submission.steps .commit - 243580988), map_pure]
  have heq : (({ exit := Riscv.Exit.success, state := sfin,
                 cycles := 83918866, oracleCalls := 8388608 } : Execution).charge 671350800 67108864,
               67108864 + 8388608) =
      (({ exit := Riscv.Exit.success, state := sfin,
          cycles := 755269666, oracleCalls := 75497472 } : Execution), 75497472) := by
    unfold Execution.charge; dsimp only
  rw [heq]

private theorem commit_det_td_build (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (c : Compression) (message : Message) (salts : Index → Salt192)
    (s1 sfin : MachineState)
    (hnodes_fin : ∀ v < TREE_NODES,
      readBuffer sfin (C_TD + 32 * v) 32 =
        nodeVal (fun x => c (x.cast h768.symm)) message salts v)
    (hsalt1 : ∀ i : Index, readBuffer s1 (C_TD + saltOff i) 24 = salts i)
    (hpres_fin : ∀ q : Nat, q < 2 ^ 64 →
      (C_ROW ≤ q ∨ (C_CMT + 32 ≤ q ∧ q < C_TD + 536870912)) →
      sfin.getByte (BitVec.ofNat 64 q) = s1.getByte (BitVec.ofNat 64 q)) :
    CommittedTrapdoor h768 c message salts (readBuffer sfin C_TD submission.sizes.trapdoor) := by
  have hC_TD : C_TD = 4294971424 := rfl
  have hC_ROW : C_ROW = 5100277792 := rfl
  have hTN : TREE_NODES = 25165824 := treeNodes_eq
  have hro : rowOff = 805306368 := rowOff_eq
  have htd_bytes : trapdoorBytes = 2348810240 := trapdoorBytes_eq
  have htd_sz : submission.sizes.trapdoor = trapdoorBytes := by
    rw [submission_sizes, trapdoorBytes_eq]
  constructor
  · intro v hv
    have hbd : 32 * v + 32 ≤ submission.sizes.trapdoor := by rw [htd_sz, htd_bytes]; rw [hTN] at hv; omega
    have hsl : BitVec.extractLsb' (8 * (32 * v)) 256 (readBuffer sfin C_TD submission.sizes.trapdoor) =
        readBuffer sfin (C_TD + 32 * v) 32 :=
      read_buffer_slice sfin C_TD submission.sizes.trapdoor (32 * v) 32 hbd
    rw [hsl]
    exact hnodes_fin v hv
  · intro i
    have hso_ge : rowOff ≤ saltOff i := by unfold saltOff; split_ifs <;> omega
    have hso_bd : saltOff i + 24 ≤ submission.sizes.trapdoor := by
      rw [htd_sz]; exact saltOff_add_24_le i
    have hsl : BitVec.extractLsb' (8 * saltOff i) 192 (readBuffer sfin C_TD submission.sizes.trapdoor) =
        readBuffer sfin (C_TD + saltOff i) 24 :=
      read_buffer_slice sfin C_TD submission.sizes.trapdoor (saltOff i) 24 hso_bd
    rw [hsl]
    have hpres_salt : readBuffer sfin (C_TD + saltOff i) 24 = readBuffer s1 (C_TD + saltOff i) 24 :=
      readBuffer_congr _ _ _ _ (fun j hj => hpres_fin (C_TD + saltOff i + j)
        (by rw [htd_sz, htd_bytes] at hso_bd; omega) (Or.inl (by omega)))
    rw [hpres_salt]
    exact hsalt1 i

/-- Deterministic composition of Phases 1, 2, and 3 (`words 1051..4160`) starting from Phase 0's
post-state `s0`: `226,787,362` steps (`201,588,752 + 25,198,610`), `755,269,666` cycles
(`671,350,800 + 83,918,866`), `75,497,472` compression calls (`67,108,864 + 8,388,608`). -/
private theorem commit_det_phases (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (message : Message) (s0 : MachineState)
    (rand : Fin (LENGTH / 2) → PairRand)
    (hinv0 :
      s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 1051) ∧
      s0.getReg .x2 = BitVec.ofNat 64 C_DB ∧
      s0.getReg .x5 = 0#64 ∧
      s0.getReg .x8 = BitVec.ofNat 64 C_MSG ∧
      s0.getReg .x9 = BitVec.ofNat 64 C_TD ∧
      s0.getReg .x10 = BitVec.ofNat 64 (C_MSG - 256) ∧
      s0.getReg .x11 = 96#64 ∧
      s0.getReg .x13 = 0#64 ∧
      s0.getReg .x18 = BitVec.ofNat 64 C_ROW ∧
      s0.getReg .x19 = BitVec.ofNat 64 (C_MSG + 2 ^ 32 - 256) ∧
      s0.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
      (∀ j : Fin (LENGTH / 2),
        readBuffer s0 (C_ROW + 184 * j.val + 72) 24 = pairSaltEven (rand j) ∧
        readBuffer s0 (C_ROW + 184 * j.val + 88) 24 = pairSaltOdd (rand j)) ∧
      (∀ q : Nat, q < 2 ^ 64 →
        (∀ j < LENGTH / 2, q < C_ROW + 184 * j + 72 ∨ C_ROW + 184 * j + 112 ≤ q) →
        s0.getByte (BitVec.ofNat 64 q) = (submission.initialState .commit message).getByte (BitVec.ofNat 64 q))) :
    ∃ sfin : MachineState,
      oracle.run (execute (submission.image .commit) (submission.steps .commit - 16793626) s0 true) =
        pure (⟨.success, sfin, 755269666, 75497472⟩, 75497472) ∧
      readBuffer sfin C_CMT 32 =
        rootVal (fun x => oracle.compression (x.cast h768.symm)) message (pairSalts rand) ∧
      CommittedTrapdoor h768 oracle.compression message (pairSalts rand)
        (readBuffer sfin C_TD submission.sizes.trapdoor) := by
  have hC_MSG : C_MSG = 4096 := rfl
  have hC_CMT : C_CMT = 4294971392 := rfl
  have hC_TD : C_TD = 4294971424 := rfl
  have hC_ROW : C_ROW = 5100277792 := rfl
  have hC_DB : C_DB = 68719476736 := rfl
  have hLEN : LENGTH = 16777216 := rfl
  have hHLEN : LENGTH / 2 = 8388608 := by decide
  have hRN : ROOT_NODE = 25165823 := rootNode_eq
  obtain ⟨hpc0, hx2_0, hx5_0, hx8_0, hx9_0, hx10_0, hx11_0, hx13_0, hx18_0, hx19_0, hx26_0,
    hsalt0, hpres0⟩ := hinv0
  have hmsg0 : ∀ (i : Index) (j : Nat), j < 256 →
      s0.getByte (BitVec.ofNat 64 (C_MSG + 256 * i.val + j)) = (message i).extractLsb' (8 * j) 8 := by
    intro i j hj
    have hi := i.isLt
    rw [hpres0 (C_MSG + 256 * i.val + j) (by omega) (fun _ _ => by omega)]
    exact commit_initial_msg_byte message i j hj
  have hgap0 : ∀ j : Fin (LENGTH / 2),
      readBuffer s0 (C_ROW + 184 * j.val + 64) 8 = 0 ∧
      readBuffer s0 (C_ROW + 184 * j.val + 112) 8 = 0 := by
    intro j; have hj := j.isLt
    constructor
    · apply readBuffer_zero_of_bytes; intro b hb
      rw [hpres0 (C_ROW + 184 * j.val + 64 + b) (by omega) (fun j' _ => by
        by_cases heq : j' = j.val
        · subst heq; omega
        · omega)]
      exact commit_initial_zero_byte message _ (by omega)
    · apply readBuffer_zero_of_bytes; intro b hb
      rw [hpres0 (C_ROW + 184 * j.val + 112 + b) (by omega) (fun j' _ => by
        by_cases heq : j' = j.val
        · subst heq; omega
        · omega)]
      exact commit_initial_zero_byte message _ (by omega)
  obtain ⟨s1, hr1, hpc1, _, hx5_1, hx9_1, hx11_1, hx13_1, hx18_1, hx26_1, hl0_1, hsalt1, hpres1⟩ :=
    commit_phase1 h768 oracle message rand s0 hpc0 hx2_0 hx5_0 hx8_0 hx9_0 hx10_0 hx11_0 hx13_0
      hx18_0 hx19_0 hx26_0 hmsg0 hsalt0 hgap0
  have hzeroRoot1 : readBuffer s1 (C_TD + 32 * ROOT_NODE) 32 = 0 := by
    apply readBuffer_zero_of_bytes; intro b hb
    rw [hpres1 (C_TD + 32 * ROOT_NODE + b) (by omega) (Or.inl ⟨by omega, by omega⟩),
        hpres0 (C_TD + 32 * ROOT_NODE + b) (by omega) (fun _ _ => Or.inl (by omega))]
    exact commit_initial_zero_byte message _ (by omega)
  obtain ⟨sfin, hrun23, hcmt_fin, hnodes_fin, hpres_fin⟩ :=
    commit_phase2_3 h768 oracle message (pairSalts rand) s1 hpc1 hx5_1 hx9_1 hx11_1 hx13_1
      hx18_1 hx26_1 hl0_1 hzeroRoot1
  exact ⟨sfin,
    commit_det_run_combine oracle s0 s1 sfin hr1 hrun23,
    hcmt_fin,
    commit_det_td_build h768 oracle.compression message (pairSalts rand) s1 sfin hnodes_fin hsalt1 hpres_fin⟩

private theorem readBuffer_digest_eq (s : MachineState) (a : Nat) (v : Commitment)
    (h : readBuffer s a 32 = v) : readBuffer s a DIGEST_BYTES = v := by
  have hgen : ∀ (n : Nat) (hn : n = 32) (w : BitVec (8 * n)),
      readBuffer s a 32 = w.cast (by rw [hn]) → readBuffer s a n = w := by
    intro n hn; subst hn; intro w hw; exact hw
  exact hgen DIGEST_BYTES rfl v h

private theorem commit_run_eq_helper (oracle : Oracle) (message : Message)
    (post0 finalState : (Fin (LENGTH / 2) → PairRand) → MachineState)
    (hrun0 : oracle.run (execute (submission.image .commit) (16793626 + (submission.steps .commit - 16793626))
        (submission.initialState .commit message) true) =ᵈ
      (($ᵗ (Fin (LENGTH / 2) → PairRand)) >>= fun rand =>
        (fun p : Execution × Nat => (p.1.charge 58736666 0, p.2)) <$>
          oracle.run (execute (submission.image .commit) (submission.steps .commit - 16793626) (post0 rand) true)))
    (hs : ∀ rand, oracle.run (execute (submission.image .commit) (submission.steps .commit - 16793626) (post0 rand) true) =
      pure (⟨.success, finalState rand, 755269666, 75497472⟩, 75497472)) :
    oracle.run (submission.run .commit message) =ᵈ
      (($ᵗ (Fin (LENGTH / 2) → PairRand)) >>= fun rand =>
        pure (({ exit := Riscv.Exit.success, state := finalState rand,
                 cycles := 814006332, oracleCalls := 75497472 } : Execution), 75497472)) := by
  have hsteps_commit : submission.steps .commit = 16793626 + (submission.steps .commit - 16793626) := by
    have hge : 16793626 ≤ submission.steps .commit := by decide
    omega
  rw [submission_run_commit submission message, hsteps_commit]
  refine hrun0.trans ?_
  apply EvalDistEq.bind_right; intro rand
  rw [hs rand, map_pure]
  have heq : (({ exit := Riscv.Exit.success, state := finalState rand,
                 cycles := 755269666, oracleCalls := 75497472 } : Execution).charge 58736666 0, 75497472) =
      (({ exit := Riscv.Exit.success, state := finalState rand,
          cycles := 814006332, oracleCalls := 75497472 } : Execution), 75497472) := by
    unfold Execution.charge; dsimp only
  rw [heq]

private theorem commit_read_spec_helper (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (message : Message) (sfin : MachineState) (salts : Index → Salt192)
    (hcmt : readBuffer sfin C_CMT 32 = rootVal (fun x => oracle.compression (x.cast h768.symm)) message salts)
    (htd : CommittedTrapdoor h768 oracle.compression message salts (readBuffer sfin C_TD submission.sizes.trapdoor)) :
    let (cmt, td) := submission.readCommit ⟨.success, sfin, 814006332, 75497472⟩
    cmt = rootVal (fun x => oracle.compression (x.cast h768.symm)) message salts ∧
    CommittedTrapdoor h768 oracle.compression message salts td := by
  have hC_CMT_eq : submission.layout.commitment = C_CMT := rfl
  have hC_TD_eq : submission.layout.trapdoor = C_TD := rfl
  dsimp only
  unfold Submission.readCommit
  dsimp only
  rw [hC_CMT_eq, hC_TD_eq]
  exact ⟨readBuffer_digest_eq sfin C_CMT _ hcmt, htd⟩

/-- Full exact execution of `submission.run .commit message` for any fixed oracle and message:
always halts with `.success`, exactly `814,006,332` cycles and `75,497,472` compression calls,
writing `rootVal` to the commitment buffer and a valid `CommittedTrapdoor` to the trapdoor buffer. -/
theorem commit_run_exact (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (message : Message) :
    ∃ finalState : (Fin (LENGTH / 2) → PairRand) → MachineState,
      oracle.run (submission.run .commit message) =ᵈ
        (($ᵗ (Fin (LENGTH / 2) → PairRand)) >>= fun rand =>
          pure (({ exit := Riscv.Exit.success, state := finalState rand,
                   cycles := 814006332, oracleCalls := 75497472 } : Execution), 75497472)) ∧
      ∀ rand,
        let salts := pairSalts rand
        let (cmt, td) := submission.readCommit
          ⟨Riscv.Exit.success, finalState rand, 814006332, 75497472⟩
        cmt = rootVal (fun x => oracle.compression (x.cast h768.symm)) message salts ∧
        CommittedTrapdoor h768 oracle.compression message salts td := by
  obtain ⟨post0, hrun0, hinv0⟩ := commit_phase0 oracle message (submission.steps .commit - 16793626)
  have hdet : ∀ rand : Fin (LENGTH / 2) → PairRand,
      ∃ sfin : MachineState,
        oracle.run (execute (submission.image .commit) (submission.steps .commit - 16793626) (post0 rand) true) =
          pure (⟨.success, sfin, 755269666, 75497472⟩, 75497472) ∧
        readBuffer sfin C_CMT 32 =
          rootVal (fun x => oracle.compression (x.cast h768.symm)) message (pairSalts rand) ∧
        CommittedTrapdoor h768 oracle.compression message (pairSalts rand)
          (readBuffer sfin C_TD submission.sizes.trapdoor) :=
    fun rand => commit_det_phases h768 oracle message (post0 rand) rand (hinv0 rand)
  let finalState (rand : Fin (LENGTH / 2) → PairRand) : MachineState := Classical.choose (hdet rand)
  exact ⟨finalState,
    commit_run_eq_helper oracle message post0 finalState hrun0 (fun rand => (Classical.choose_spec (hdet rand)).1),
    fun rand => commit_read_spec_helper h768 oracle message (finalState rand) (pairSalts rand)
      (Classical.choose_spec (hdet rand)).2.1 (Classical.choose_spec (hdet rand)).2.2⟩

/-- Exact `fixedOracleRun` refinement of `submission.scheme.commit message` for `MoonHiding`. -/
theorem commit_oracle_run_exact (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (message : Message) :
    ∃ trapdoorOf : (Fin (LENGTH / 2) → PairRand) → BitVec (8 * submission.sizes.trapdoor),
      fixedOracleRun oracle (submission.scheme.commit message) =ᵈ
        (($ᵗ (Fin (LENGTH / 2) → PairRand)) >>= fun rand =>
          pure (rootVal (fun x => oracle.compression (x.cast h768.symm)) message
            (pairSalts rand), trapdoorOf rand)) ∧
      ∀ rand,
        CommittedTrapdoor h768 oracle.compression message (pairSalts rand) (trapdoorOf rand) := by
  obtain ⟨finalState, hrun, hspec⟩ := commit_run_exact h768 oracle message
  refine ⟨fun rand => (submission.readCommit ⟨.success, finalState rand, 814006332, 75497472⟩).2, ?_, ?_⟩
  · let f : Execution × Nat → Commitment × BitVec (8 * submission.sizes.trapdoor) :=
      fun p => submission.readCommit p.1
    have hmap : (fixedOracleRun oracle (submission.scheme.commit message) :
          ProbComp (Commitment × BitVec (8 * submission.sizes.trapdoor))) =
        f <$> oracle.run (submission.run .commit message) := by
      simp only [fixedOracleRun, Submission.scheme, oracle_run_map, Functor.map_map, f]
    have hstep : f <$> (($ᵗ (Fin (LENGTH / 2) → PairRand)) >>= fun rand =>
          pure (({ exit := Riscv.Exit.success, state := finalState rand,
                   cycles := 814006332, oracleCalls := 75497472 } : Execution), 75497472)) =
        (($ᵗ (Fin (LENGTH / 2) → PairRand)) >>= fun rand =>
          pure (rootVal (fun x => oracle.compression (x.cast h768.symm)) message (pairSalts rand),
                (submission.readCommit ⟨.success, finalState rand, 814006332, 75497472⟩).2)) := by
      rw [map_bind]
      apply bind_congr; intro rand
      rw [map_pure]
      exact congrArg pure (Prod.ext (hspec rand).1 rfl)
    exact hmap.symm ▸ (hstep ▸ (hrun.map f))
  · intro rand; exact (hspec rand).2

private theorem commit_prEvent_uniform_bind_pure_eq_one {α β : Type} [SampleableType α]
    (f : α → β) (p : β → Prop) (h : ∀ a, p (f a)) :
    Pr{let y ← (($ᵗ α) >>= fun a => pure (f a))}[p y] = 1 := by
  have h1 : Pr{let y ← (($ᵗ α) >>= fun a => pure (f a))}[p y] =
      Pr{let y ← (($ᵗ α) >>= fun _ => (pure () : ProbComp Unit))}[True] := by
    apply prEvent_bind_congr ($ᵗ α) (fun a => pure (f a)) (fun _ => pure ()) p (fun _ => True)
    intro a
    classical
    rw [prEvent_pure, prEvent_pure, ite_eq_left_of_eq_true _ _ (eq_true (h a)),
      ite_eq_left_of_eq_true _ _ (eq_true trivial)]
  rw [h1]
  have h2 : (fun _ : Unit => True) <$> (($ᵗ α) >>= fun _ => (pure () : ProbComp Unit)) =
      (($ᵗ α) >>= fun _ => (pure True : ProbComp Prop)) := by
    simp only [map_bind, map_pure]
  change prEvent ((fun _ : Unit => True) <$> (($ᵗ α) >>= fun _ => (pure () : ProbComp Unit))) = 1
  rw [h2, prEvent_def, OracleComp.evalDist_bind_const]
  change prEvent (pure True : ProbComp Prop) = 1
  rw [prEvent_pure_prop, ite_eq_left_of_eq_true _ _ (eq_true trivial)]

/-- `submission.run .commit` always terminates with probability 1 for every oracle and message. -/
theorem commit_termination (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (message : Message) :
    Pr{let result ← oracle.run (submission.run .commit message)}[
      result.1.exit ≠ Riscv.Exit.unfinished] = 1 := by
  obtain ⟨finalState, hrun, _⟩ := commit_run_exact h768 oracle message
  rw [hrun.prEvent_eq _]
  exact commit_prEvent_uniform_bind_pure_eq_one
    (fun rand => ((⟨.success, finalState rand, 814006332, 75497472⟩ : Execution), 75497472))
    (fun result => result.1.exit ≠ Riscv.Exit.unfinished)
    (fun _ => by dsimp only; decide)

end CommitGolfCandidate
