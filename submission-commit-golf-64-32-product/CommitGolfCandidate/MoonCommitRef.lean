import CommitGolfCandidate.MoonCommitBin
import CommitGolfCandidate.CompressionSampling

/-! Full composition of the 64-32 `commit` image (`commit_phase0`, `commit_phase1A`,
`commit_phase1B`, `commit_phase1C`, `commit_phase1D`, `commit_phase2`, `commit_phase3`,
`commit_phase4_and_root`, and `ECALL HALT(0)`), proving:
- `commit_run_exact` (`cycles = 1,276,210,876`, `oracleCalls = 83,886,079`)
- `commit_oracle_run_exact` (exact `fixedOracleRun` refinement to `rootVal` + `CommittedTrapdoor`)
- `commit_termination` (termination with probability 1). -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

private theorem commit_det_phases (h512 : COMPRESSION_INPUT_LENGTH = 512)
    (oracle : Oracle) (message : Message) (s0 : MachineState)
    (rand : Fin (LENGTH / 2) → PairRand)
    (hinv0 :
      s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 4122) ∧
      s0.getReg .x5 = 0#64 ∧
      s0.getReg .x8 = BitVec.ofNat 64 C_MSG ∧
      s0.getReg .x9 = BitVec.ofNat 64 C_TD ∧
      s0.getReg .x10 = BitVec.ofNat 64 (C_MSG - 64) ∧
      s0.getReg .x11 = 64#64 ∧
      s0.getReg .x13 = 0#64 ∧
      s0.getReg .x18 = BitVec.ofNat 64 C_ROW ∧
      s0.getReg .x19 = BitVec.ofNat 64 (C_MSG + 2 ^ 32 - 64) ∧
      s0.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
      (∀ j : Fin (LENGTH / 2),
        readBuffer s0 (C_ROW + 120 * j.val + 40) 24 = pairSaltEven (rand j) ∧
        readBuffer s0 (C_ROW + 120 * j.val + 56) 24 = pairSaltOdd (rand j)) ∧
      (∀ q : Nat, q < 2 ^ 64 →
        (∀ j < LENGTH / 2, q < C_ROW + 120 * j + 40 ∨ C_ROW + 120 * j + 80 ≤ q) →
        s0.getByte (BitVec.ofNat 64 q) = (submission.initialState .commit message).getByte (BitVec.ofNat 64 q))) :
    let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
    let p200 : Perm200 := fun x => oracle.permutation x
    ∃ sfin : MachineState,
      oracle.run (execute (submission.image .commit) (submission.steps .commit - 16785431) s0 true) =
        pure (⟨.success, sfin, 1217482405, 83886079⟩, 83886079) ∧
      readBuffer sfin C_CMT 32 = rootVal c64 p200 message (pairSalts rand) ∧
      CommittedTrapdoor h512 oracle.compression oracle.permutation message (pairSalts rand)
        (readBuffer sfin C_TD submission.sizes.trapdoor) := by
  have hLEN : LENGTH = 16777216 := rfl
  have hHLEN : LENGTH / 2 = 8388608 := by decide
  have hCM : C_MSG = 4096 := rfl
  have hCC : C_CMT = 4294971392 := rfl
  have hCT : C_TD = 4294971424 := rfl
  have hCR : C_ROW = 5368713248 := rfl
  have htd_sz : submission.sizes.trapdoor = trapdoorBytes := rfl
  have htb := trapdoorBytes_eq
  have hro := rowOff_eq
  have hrb := rowBytes_eq
  let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
  let p200 : Perm200 := fun x => oracle.permutation x
  obtain ⟨hpc0, hx5_0, hx8_0, hx9_0, hx10_0, hx11_0, hx13_0, hx18_0, hx19_0, hx26_0, hsalt0, hpres0⟩ := hinv0
  -- Phase 1A (`C0`)
  have hmsg0 : ∀ (i : Index) (j : Nat), j < 256 →
      s0.getByte (BitVec.ofNat 64 (C_MSG + 256 * i.val + j)) = (message i).extractLsb' (8 * j) 8 := by
    intro i j hj
    have hi := i.isLt
    rw [hpres0 (C_MSG + 256 * i.val + j) (by omega) (fun _ _ => by omega)]
    exact commit_initial_msg_byte message i j hj
  obtain ⟨s1A, hrun1A, hpc1A, hx5_1A, hx8_1A, hx9_1A, hx10_1A, hx11_1A, hx13_1A, hx18_1A, hx19_1A, hx26_1A,
      hmsgLo1A, hp1_1A, hpres1A⟩ :=
    commit_phase1A h512 oracle message s0 hpc0 hx5_0 hx8_0 hx9_0 hx10_0 hx11_0 hx13_0 hx18_0 hx19_0 hx26_0 hmsg0
  -- Phase 1B (`P1`)
  obtain ⟨s1B, hrun1B, hpc1B, hx5_1B, _, hx9_1B, hx10_1B, hx11_1B, hx12_1B, hx13_1B, hx18_1B, hx19_1B, hx26_1B,
      hc2_1B, hpres1B⟩ :=
    commit_phase1B h512 oracle message s1A hpc1A hx5_1A hx8_1A hx9_1A hx10_1A hx11_1A hx13_1A hx18_1A hx19_1A hx26_1A
      hmsgLo1A hp1_1A
  -- Phase 1C (`C2`)
  obtain ⟨s1C, hrun1C, hpc1C, hx5_1C, hx9_1C, hx10_1C, hx11_1C, hx12_1C, hx13_1C, _, hx19_1C, hx26_1C,
      hleafA1C, hpres1C⟩ :=
    commit_phase1C h512 oracle message s1B hpc1B hx5_1B hx9_1B hx10_1B hx11_1B hx12_1B hx13_1B hx18_1B hx19_1B hx26_1B
      hc2_1B
  -- Collect full row invariants at `s1C` for Phase 1D (`C3`)
  have hrow1C : ∀ p : Fin (LENGTH / 2),
      readBuffer s1C (C_ROW + 120 * p.val) 32 = leafA c64 p200 (message ⟨2 * p.val, by have := p.isLt; omega⟩) ∧
      readBuffer s1C (C_ROW + 120 * p.val + 88) 32 = leafA c64 p200 (message ⟨2 * p.val + 1, by have := p.isLt; omega⟩) ∧
      readBuffer s1C (C_ROW + 120 * p.val + 32) 8 = 0 ∧
      readBuffer s1C (C_ROW + 120 * p.val + 80) 8 = 0 ∧
      readBuffer s1C (C_ROW + 120 * p.val + 40) 24 = pairSaltEven (rand p) ∧
      readBuffer s1C (C_ROW + 120 * p.val + 56) 24 = pairSaltOdd (rand p) := by
    intro p; have hp := p.isLt
    obtain ⟨haE, haO⟩ := hleafA1C p
    obtain ⟨hsE, hsO⟩ := hsalt0 p
    refine ⟨haE, haO, ?_, ?_, ?_, ?_⟩
    · apply readBuffer_zero_of_bytes
      intro j hj
      rw [hpres1C _ (by omega) (fun p' _ => by
            by_cases hEq : p' = p.val
            · subst hEq; omega
            · omega),
          hpres1B _ (by omega) (by omega), hpres1A _ (by omega) (by omega),
          hpres0 _ (by omega) (fun p' _ => by
            by_cases hEq : p' = p.val
            · subst hEq; omega
            · omega)]
      exact commit_initial_zero_byte message _ (by omega)
    · apply readBuffer_zero_of_bytes
      intro j hj
      rw [hpres1C _ (by omega) (fun p' _ => by
            by_cases hEq : p' = p.val
            · subst hEq; omega
            · omega),
          hpres1B _ (by omega) (by omega), hpres1A _ (by omega) (by omega),
          hpres0 _ (by omega) (fun p' _ => by
            by_cases hEq : p' = p.val
            · subst hEq; omega
            · omega)]
      exact commit_initial_zero_byte message _ (by omega)
    · refine (readBuffer_congr s1C s0 _ 24 (fun j hj => ?_)).trans hsE
      rw [hpres1C _ (by omega) (fun p' _ => by
            by_cases hEq : p' = p.val
            · subst hEq; omega
            · omega),
          hpres1B _ (by omega) (by omega), hpres1A _ (by omega) (by omega)]
    · refine (readBuffer_congr s1C s0 _ 24 (fun j hj => ?_)).trans hsO
      rw [hpres1C _ (by omega) (fun p' _ => by
            by_cases hEq : p' = p.val
            · subst hEq; omega
            · omega),
          hpres1B _ (by omega) (by omega), hpres1A _ (by omega) (by omega)]
  -- Phase 1D (`C3`)
  obtain ⟨s1D, hrun1D, hpc1D, hx5_1D, hx9_1D, hx10_1D, hx11_1D, hx12_1D, hx13_1D, hx19_1D, hx26_1D,
      hL0_1D, hpres1D⟩ :=
    commit_phase1D h512 oracle message rand s1C hpc1C hx5_1C hx9_1C hx10_1C hx11_1C hx12_1C hx13_1C hx19_1C hx26_1C hrow1C
  -- Convert `L0` postcondition into unified `c_heapVal` invariant for `[2^24, 2^25)`
  have hheap1D : ∀ h', 2 ^ 24 ≤ h' → h' < 2 ^ 25 →
      readBuffer s1D (C_TD + 32 * h') 32 = c_heapVal c64 p200 message (pairSalts rand) h' := by
    intro h' h1 h2
    have hidx : h' - 2 ^ 24 < levelSize 0 := by rw [levelSize_0]; omega
    have hhi : h' = heapIdx 0 (h' - 2 ^ 24) := by unfold heapIdx levelSize; omega
    rw [hhi, c_heapVal_eq_nodeVal c64 p200 message (pairSalts rand) 0 (h' - 2 ^ 24) (by omega) hidx]
    exact hL0_1D (h' - 2 ^ 24) hidx
  -- Phase 2 (`L1`)
  obtain ⟨s2, hrun2, hpc2, hx5_2, hx9_2, hx10_2, hx11_2, hx12_2, hx13_2, hx19_2, hx26_2, hheap2, hpres2⟩ :=
    commit_phase2 h512 oracle message (pairSalts rand) s1D hpc1D hx5_1D hx9_1D hx10_1D hx11_1D hx12_1D hx13_1D
      hx19_1D hx26_1D hheap1D
  -- Phase 3 (`L2..L5`)
  obtain ⟨s3, hrun3, hpc3, hx5_3, hx9_3, hx10_3, hx11_3, hx12_3, hx13_3, hx19_3, hx26_3, hx27_3, hheap3, hpres3⟩ :=
    commit_phase3 h512 oracle message (pairSalts rand) s2 hpc2 hx5_2 hx9_2 hx10_2 hx11_2 hx12_2 hx13_2
      hx19_2 hx26_2 hheap2
  -- Phase 4 + Root + Copy + Halt Prep
  obtain ⟨sHalt, hrun4, hpcHalt, hx5Halt, hx10Halt, hrootHalt, hheapHalt, hpres4⟩ :=
    commit_phase4_and_root h512 oracle message (pairSalts rand) s3 hpc3 hx5_3 hx9_3 hx10_3 hx11_3 hx12_3 hx13_3
      hx19_3 hx26_3 hx27_3 hheap3
  -- Combine deterministic runs + final `ECALL HALT(0)`
  have hrun_all : DetRun oracle (submission.image .commit) s0 261181099 sHalt 1217482404 83886079 := by
    simpa only [
      show 50348040 + 50348041 + 50348044 + 50348040 + 25174018 + 31464965 + 3149951 = 261181099 by decide,
      show 167788552 + 536887305 + 167788556 + 167788552 + 83894274 + 86515205 + 6819960 = 1217482404 by decide,
      show 16777216 + 16777216 + 16777216 + 16777216 + 8388608 + 7864320 + 524287 = 83886079 by decide] using
      (((((hrun1A.trans hrun1B).trans hrun1C).trans hrun1D).trans hrun2).trans hrun3).trans hrun4
  have hst : submission.steps .commit = 4294967296 := rfl
  have hfuel : 261181099 + 1 ≤ submission.steps .commit - 16785431 := by rw [hst]; omega
  have hfinish : oracle.run (execute (submission.image .commit) (submission.steps .commit - 16785431) s0 true) =
      pure (⟨.success, sHalt, 1217482405, 83886079⟩, 83886079) :=
    hrun_all.finish
      (commit_fetch_commitTailInstr sHalt 43886 (by omega) (by omega) hpcHalt)
      hx5Halt hx10Halt _ hfuel
  refine ⟨sHalt, hfinish, hrootHalt, ?_, ?_⟩
  · -- All heap nodes `l ≤ 24, idx < levelSize l`
    intro l hl idx hidx
    have hh_pos : 1 ≤ heapIdx l idx := heapIdx_pos l idx
    have hh_lt : heapIdx l idx < 2 ^ 25 := heapIdx_lt l idx hl hidx
    have hoff_bd : 32 * heapIdx l idx + 32 ≤ submission.sizes.trapdoor := by
      rw [htd_sz]; omega
    show (readBuffer sHalt C_TD submission.sizes.trapdoor).extractLsb' (8 * (32 * heapIdx l idx)) (8 * 32) = _
    rw [read_buffer_slice sHalt C_TD submission.sizes.trapdoor (32 * heapIdx l idx) 32 hoff_bd]
    rw [hheapHalt (heapIdx l idx) hh_pos hh_lt]
    exact c_heapVal_eq_nodeVal c64 p200 message (pairSalts rand) l idx hl hidx
  · -- All leaf salts `i : Index`
    intro i
    have hi := i.isLt
    have hso_ge : rowOff ≤ saltOff i := by unfold saltOff; split_ifs <;> omega
    have hso_bd : saltOff i + 24 ≤ submission.sizes.trapdoor := by
      rw [htd_sz]; exact saltOff_add_24_le i
    show (readBuffer sHalt C_TD submission.sizes.trapdoor).extractLsb' (8 * saltOff i) (8 * 24) = _
    rw [read_buffer_slice sHalt C_TD submission.sizes.trapdoor (saltOff i) 24 hso_bd]
    have hpres_salt : readBuffer sHalt (C_TD + saltOff i) 24 = readBuffer s1C (C_TD + saltOff i) 24 := by
      rw [hpres4.readBuffer_eq (by omega) (by omega),
          hpres3.readBuffer_eq (by omega) (by omega),
          hpres2.readBuffer_eq (by omega) (by omega),
          hpres1D.readBuffer_eq (by omega) (by omega)]
    rw [hpres_salt]
    let p : Fin (LENGTH / 2) := ⟨i.val / 2, by omega⟩
    obtain ⟨_, _, _, _, hsE, hsO⟩ := hrow1C p
    unfold pairSalts saltOff PAIR_STRIDE
    have hpv : p.val = i.val / 2 := rfl
    by_cases hev : i.val % 2 = 0
    · simp only [hev, ite_true]
      have haddr : C_TD + (rowOff + 120 * (i.val / 2) + 40) = C_ROW + 120 * p.val + 40 := by
        rw [C_ROW_eq, hpv]; omega
      rw [haddr]; exact hsE
    · simp only [hev, ite_false]
      have haddr : C_TD + (rowOff + 120 * (i.val / 2) + 56) = C_ROW + 120 * p.val + 56 := by
        rw [C_ROW_eq, hpv]; omega
      rw [haddr]; exact hsO

private theorem c_readBuffer_digest_eq (s : MachineState) (a : Nat) (v : Commitment)
    (h : readBuffer s a 32 = v) : readBuffer s a DIGEST_BYTES = v := h

private theorem c_commit_steps_eq : submission.steps .commit = 4294967296 := rfl

private theorem c_commit_steps_split :
    submission.steps .commit = 16785431 + (submission.steps .commit - 16785431) := by
  have h := c_commit_steps_eq
  omega

private theorem c_charge_mk (ex : Exit) (st : MachineState) (cy1 cy2 ca1 ca2 : Nat) :
    ({ exit := ex, state := st, cycles := cy2, oracleCalls := ca2 } : Execution).charge cy1 ca1 =
      { exit := ex, state := st, cycles := cy1 + cy2, oracleCalls := ca1 + ca2 } := rfl

private theorem commit_run_eq_helper {α : Type} [SampleableType α]
    (oracle : Oracle) (img : Image) (totalSteps steps0 extra : Nat) (init : MachineState)
    (hsteps : totalSteps = steps0 + extra)
    (post0 finalState : α → MachineState)
    (hrun0 : oracle.run (execute img (steps0 + extra) init true) =ᵈ
      (($ᵗ α) >>= fun rand =>
        (fun p : Execution × Nat => (p.1.charge 58728471 0, p.2)) <$>
          oracle.run (execute img extra (post0 rand) true)))
    (hs : ∀ rand, oracle.run (execute img extra (post0 rand) true) =
      pure (⟨.success, finalState rand, 1217482405, 83886079⟩, 83886079)) :
    oracle.run (execute img totalSteps init true) =ᵈ
      (($ᵗ α) >>= fun rand =>
        pure (({ exit := Riscv.Exit.success, state := finalState rand,
                 cycles := 1276210876, oracleCalls := 83886079 } : Execution), 83886079)) := by
  rw [hsteps]
  refine hrun0.trans ?_
  apply EvalDistEq.bind_right; intro rand
  rw [hs rand, map_pure]
  have hcy : 58728471 + 1217482405 = 1276210876 := by omega
  have hca : 0 + 83886079 = 83886079 := by omega
  have heq : (({ exit := Riscv.Exit.success, state := finalState rand,
                 cycles := 1217482405, oracleCalls := 83886079 } : Execution).charge 58728471 0, 83886079) =
      (({ exit := Riscv.Exit.success, state := finalState rand,
          cycles := 1276210876, oracleCalls := 83886079 } : Execution), 83886079) := by
    rw [c_charge_mk, hcy, hca]
  rw [heq]

private theorem commit_read_spec_helper (h512 : COMPRESSION_INPUT_LENGTH = 512)
    (oracle : Oracle) (message : Message) (sfin : MachineState) (salts : Index → Salt192)
    (hcmt : readBuffer sfin C_CMT 32 =
      rootVal (fun x => oracle.compression (x.cast h512.symm)) oracle.permutation message salts)
    (htd : CommittedTrapdoor h512 oracle.compression oracle.permutation message salts
      (readBuffer sfin C_TD submission.sizes.trapdoor)) :
    let (cmt, td) := submission.readCommit ⟨.success, sfin, 1276210876, 83886079⟩
    cmt = rootVal (fun x => oracle.compression (x.cast h512.symm)) oracle.permutation message salts ∧
    CommittedTrapdoor h512 oracle.compression oracle.permutation message salts td := by
  have hC_CMT_eq : submission.layout.commitment = C_CMT := rfl
  have hC_TD_eq : submission.layout.trapdoor = C_TD := rfl
  dsimp only
  unfold Submission.readCommit
  dsimp only
  rw [hC_CMT_eq, hC_TD_eq]
  exact ⟨c_readBuffer_digest_eq sfin C_CMT _ hcmt, htd⟩

/-- Full exact execution of `submission.run .commit message` for any fixed oracle and message:
always halts with `.success`, exactly `1,276,210,876` cycles and `83,886,079` public calls
(`4 * 2^24 - 1` compressions + `2^24` permutations), writing `rootVal` to `C_CMT` and a valid
`CommittedTrapdoor` to `C_TD`. -/
theorem commit_run_exact (h512 : COMPRESSION_INPUT_LENGTH = 512)
    (oracle : Oracle) (message : Message) :
    ∃ finalState : (Fin (LENGTH / 2) → PairRand) → MachineState,
      oracle.run (submission.run .commit message) =ᵈ
        (($ᵗ (Fin (LENGTH / 2) → PairRand)) >>= fun rand =>
          pure (({ exit := Riscv.Exit.success, state := finalState rand,
                   cycles := 1276210876, oracleCalls := 83886079 } : Execution), 83886079)) ∧
      ∀ rand,
        let salts := pairSalts rand
        let (cmt, td) := submission.readCommit
          ⟨Riscv.Exit.success, finalState rand, 1276210876, 83886079⟩
        cmt = rootVal (fun x => oracle.compression (x.cast h512.symm)) oracle.permutation message salts ∧
        CommittedTrapdoor h512 oracle.compression oracle.permutation message salts td := by
  obtain ⟨post0, hrun0, hinv0⟩ := commit_phase0 oracle message (submission.steps .commit - 16785431)
  have hdet : ∀ rand : Fin (LENGTH / 2) → PairRand,
      ∃ sfin : MachineState,
        oracle.run (execute (submission.image .commit) (submission.steps .commit - 16785431) (post0 rand) true) =
          pure (⟨.success, sfin, 1217482405, 83886079⟩, 83886079) ∧
        readBuffer sfin C_CMT 32 =
          rootVal (fun x => oracle.compression (x.cast h512.symm)) oracle.permutation message (pairSalts rand) ∧
        CommittedTrapdoor h512 oracle.compression oracle.permutation message (pairSalts rand)
          (readBuffer sfin C_TD submission.sizes.trapdoor) :=
    fun rand => commit_det_phases h512 oracle message (post0 rand) rand (hinv0 rand)
  let finalState (rand : Fin (LENGTH / 2) → PairRand) : MachineState := Classical.choose (hdet rand)
  have hrun_exact : oracle.run (submission.run .commit message) =ᵈ
      (($ᵗ (Fin (LENGTH / 2) → PairRand)) >>= fun rand =>
        pure (({ exit := Riscv.Exit.success, state := finalState rand,
                 cycles := 1276210876, oracleCalls := 83886079 } : Execution), 83886079)) := by
    rw [c_submission_run_commit submission message]
    exact commit_run_eq_helper oracle (submission.image .commit) (submission.steps .commit)
      16785431 (submission.steps .commit - 16785431) (submission.initialState .commit message)
      c_commit_steps_split post0 finalState hrun0 (fun rand => (Classical.choose_spec (hdet rand)).1)
  exact ⟨finalState, hrun_exact,
    fun rand => commit_read_spec_helper h512 oracle message (finalState rand) (pairSalts rand)
      (Classical.choose_spec (hdet rand)).2.1 (Classical.choose_spec (hdet rand)).2.2⟩

/-- Exact `fixedOracleRun` refinement of `submission.scheme.commit message` for `MoonHiding`. -/
theorem commit_oracle_run_exact (h512 : COMPRESSION_INPUT_LENGTH = 512)
    (oracle : Oracle) (message : Message) :
    ∃ trapdoorOf : (Fin (LENGTH / 2) → PairRand) → BitVec (8 * submission.sizes.trapdoor),
      fixedOracleRun oracle (submission.scheme.commit message) =ᵈ
        (($ᵗ (Fin (LENGTH / 2) → PairRand)) >>= fun rand =>
          pure (rootVal (fun x => oracle.compression (x.cast h512.symm)) oracle.permutation message
            (pairSalts rand), trapdoorOf rand)) ∧
      ∀ rand,
        CommittedTrapdoor h512 oracle.compression oracle.permutation message (pairSalts rand) (trapdoorOf rand) := by
  obtain ⟨finalState, hrun, hspec⟩ := commit_run_exact h512 oracle message
  refine ⟨fun rand => (submission.readCommit ⟨.success, finalState rand, 1276210876, 83886079⟩).2, ?_, ?_⟩
  · let f : Execution × Nat → Commitment × BitVec (8 * submission.sizes.trapdoor) :=
      fun p => submission.readCommit p.1
    have hmap : (fixedOracleRun oracle (submission.scheme.commit message) :
          ProbComp (Commitment × BitVec (8 * submission.sizes.trapdoor))) =
        f <$> oracle.run (submission.run .commit message) := by
      simp only [fixedOracleRun, Submission.scheme, oracle_run_map, Functor.map_map, f]
    have hstep : f <$> (($ᵗ (Fin (LENGTH / 2) → PairRand)) >>= fun rand =>
          pure (({ exit := Riscv.Exit.success, state := finalState rand,
                   cycles := 1276210876, oracleCalls := 83886079 } : Execution), 83886079)) =
        (($ᵗ (Fin (LENGTH / 2) → PairRand)) >>= fun rand =>
          pure (rootVal (fun x => oracle.compression (x.cast h512.symm)) oracle.permutation message (pairSalts rand),
                (submission.readCommit ⟨.success, finalState rand, 1276210876, 83886079⟩).2)) := by
      rw [map_bind]
      apply bind_congr; intro rand
      rw [map_pure]
      exact congrArg pure (Prod.ext (hspec rand).1 rfl)
    exact hmap.symm ▸ (hstep ▸ (hrun.map f))
  · intro rand; exact (hspec rand).2

private theorem commit_prEvent_uniform_bind_pure_eq_one {α β : Type} [SampleableType α]
    (f : α → β) (p : β → Prop) (h : ∀ a, p (f a)) :
    Pr{let y ← (($ᵗ α) >>= fun a => pure (f a))}[p y] = 1 := by
  have heq : (fun y => p y) <$> (($ᵗ α) >>= fun a => pure (f a)) =
      (fun _ => True) <$> (($ᵗ α) >>= fun a => pure (f a)) := by
    simp only [map_bind, map_pure]
    apply bind_congr; intro a
    exact congrArg pure (propext ⟨fun _ => trivial, fun _ => h a⟩)
  change prEvent ((fun y => p y) <$> _) = 1
  rw [heq]
  exact OracleComp.prEvent_true_eq_one _

/-- `submission.run .commit` always terminates with probability 1 for every oracle and message. -/
theorem commit_termination (h512 : COMPRESSION_INPUT_LENGTH = 512)
    (oracle : Oracle) (message : Message) :
    Pr{let result ← oracle.run (submission.run .commit message)}[
      result.1.exit ≠ Riscv.Exit.unfinished] = 1 := by
  obtain ⟨finalState, hrun, _⟩ := commit_run_exact h512 oracle message
  rw [hrun.prEvent_eq _]
  exact commit_prEvent_uniform_bind_pure_eq_one
    (fun rand => ((⟨.success, finalState rand, 1276210876, 83886079⟩ : Execution), 83886079))
    (fun result => result.1.exit ≠ Riscv.Exit.unfinished)
    (fun _ => by dsimp only; decide)

end CommitGolfCandidate
