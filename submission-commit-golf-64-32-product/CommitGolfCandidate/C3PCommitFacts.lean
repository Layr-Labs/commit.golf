import CommitGolfCandidate.C3PCommitMeaning4
import CommitGolfCandidate.C3PParentFrame
import CommitGolfCandidate.TwoPermutationRootBytes
import CommitGolfCandidate.TwoPermutationHybridHeapFacts

/-! # The paired commit's end state

Under a fixed oracle and given draws, the commit ends in `commitEnd`: its commitment buffer holds the
honest root, every internal heap node slot the honest node, and the reply area every leaf's reply. -/
namespace TwoPermutationPrototype.RV64.C3P
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.RV64.C3Leaves (memoryView_congr c3_read_compression)
open CommitGolfCandidate (checkEvaluation check_evaluation_support fixedOracleRun fixed_oracle_run_map)
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option autoImplicit false

/-- The honest leaf digests of the paired leaf. -/
abbrev pLeaves (oracle : Oracle) (msg : Message) (salts : CompleteSaltTape) : DigestTape :=
  c3pFullLeafDigests oracle.compression (BiPermutation.equiv Block oracle.permutation) msg salts

/-- Leaf `j`'s permutation input. -/
def pInput (oracle : Oracle) (msg : Message) (salts : CompleteSaltTape) (j : Index) : Block :=
  c3pPermInput oracle.compression j (saltWords (salts j)) (messageWords msg j)

/-- The commit's final state for given draws. -/
def commitEnd (oracle : Oracle) (initial : MachineState) (wss : List (List (BitVec 256))) : MachineState :=
  rootPrefix (checkEvaluation oracle (hybridParentPhase (exitState (leafDet oracle wss 0 (firstState initial))))).1 10

/-- What the paired commit needs from a submission. -/
structure PairedCommitLayout (s : Submission) : Prop where
  image : s.image .commit = packedWideCommitImage
  fuel : 276964482 ≤ s.steps .commit
  message : s.layout.message = 4096
  commitment : s.layout.commitment = 4294971392
  trapdoor : s.layout.trapdoor = 4294971424

theorem paired_commit_entry (s : Submission) (lay : PairedCommitLayout s) (msg : Message) :
    CommitEntry (s.initialState .commit msg) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · change BitVec.ofNat 64 s.layout.message = _; rw [lay.message]; rfl
  · change BitVec.ofNat 64 s.layout.commitment = _; rw [lay.commitment]; rfl
  · change BitVec.ofNat 64 s.layout.trapdoor = _; rw [lay.trapdoor]; rfl

/-- The commit under a fixed oracle: the draws, then the readout of one end state. -/
theorem paired_commit_distribution (s : Submission) (lay : PairedCommitLayout s) (oracle : Oracle) (msg : Message) :
    fixedOracleRun oracle (s.scheme.commit msg) =
      ((List.range 8192).mapM (fun _ => (List.range 1024).mapM (fun _ => ($ᵗ BitVec 256 : ProbComp (BitVec 256)))) >>=
        fun wss => pure (s.readCommit ⟨.success, commitEnd oracle (s.initialState .commit msg) wss, 1266820219,
          83886079⟩)) := by
  change fixedOracleRun oracle (s.readCommit <$> s.run .commit msg) = _
  have run : s.run .commit msg = commitTraceP (s.initialState .commit msg) := by
    change execute (s.image .commit) (s.steps .commit) (s.initialState .commit msg) true = _
    rw [lay.image, show s.steps .commit = 276964482 + (s.steps .commit - 276964482) by have := lay.fuel; omega]
    exact paired_commit_execution _ (paired_commit_entry s lay msg) _
  rw [run, fixed_oracle_run_map, commit_fixed, map_bind]
  simp only [map_pure]
  rfl

/-- Words of a state agree after `rootPrefix` above the commitment buffer. -/
theorem root_word (F : MachineState) (x8 : F.getReg .x8 = 4294971392) (w : Nat) (above : 536871428 ≤ w)
    (bound : w + 8 < 2 ^ 33) : memoryView (rootPrefix F 10) w = memoryView F w := by
  have e := root_preserves_heap_buffer F x8 w 8 (by omega) (by omega) (by decide)
  rwa [read_word, read_word] at e

/-- **The commit's end state.** -/
theorem commit_end_facts (s : Submission) (lay : PairedCommitLayout s) (oracle : Oracle) (msg : Message)
    (wss : List (List (BitVec 256))) (len : wss.length = 8192) (lens : ∀ ws ∈ wss, ws.length = 1024) :
    let R := commitEnd oracle (s.initialState .commit msg) wss
    let salts := pairedSaltTape wss.flatten
    let heap := Hybrid.heap oracle.compression (pLeaves oracle msg salts)
    readBuffer R 4294971392 32 = heap 1 ∧
      (∀ n, 0 < n → n < LENGTH → readBuffer R (8 * treeWord n) 32 = heap n) ∧
      (∀ j (hj : j < 2 ^ 24), (window (memoryView R) (replyW + 25 * j) : Words 25) =
        replyWords (oracle.permutation (pInput oracle msg salts ⟨j, hj⟩))) := by
  intro R salts heap
  let initial := s.initialState .commit msg
  have entry := paired_commit_entry s lay msg
  let S := firstState initial
  obtain ⟨regs0, x21, x8, x9, x19⟩ := first_regs initial entry
  have inv0 : LoopRegs S 0 4294971392 4294971424 536870912 := ⟨regs0, x21, x8, x9, x19⟩
  let L := leafDet oracle wss 0 S
  have lend := (leaf_det oracle _ _ _ wss S len lens inv0).1
  let X := exitState L
  obtain ⟨pregs, ppc, p8⟩ := exit_regs L lend.x5 lend.stop lend.heap lend.stride
  have X8 : X.getReg .x8 = 4294971392 := p8.trans lend.out
  let F := (checkEvaluation oracle (hybridParentPhase X)).1
  have hit : F ∈ support (hybridParentPhase X) := check_evaluation_support oracle _
  obtain ⟨fregs, _, f8⟩ := hybrid_parent_phase_post X pregs ppc X8 hit
  have F8 : F.getReg .x8 = 4294971392 := f8.trans X8
  have F9 : F.getReg .x9 = 4294971424 := by rw [fregs.heap]; rfl
  have mS : ∀ j (hj : j < 2 ^ 24), (window (memoryView S) (512 + 32 * j) : Words 32) = messageWords msg ⟨j, hj⟩ := by
    intro j hj
    rw [first_state_mem]
    exact message_window s lay.message msg j hj
  -- every leaf's reply after the leaf phase
  have replies : ∀ j (hj : j < 2 ^ 24), (window (memoryView L) (replyW + 25 * j) : Words 25) =
      replyWords (oracle.permutation (pInput oracle msg salts ⟨j, hj⟩)) := by
    intro j hj
    rw [leaf_reply oracle _ _ _ wss S len lens inv0 j hj, mS j hj]
    rfl
  -- the heap from the reply-area pair inputs
  have nodes : ∀ n, 0 < n → n < LENGTH → nodeDigest F n = heap n := by
    apply hybrid_parent_content oracle X heap
    · exact fun n lo hi => Hybrid.raw_parent _ _ n (by change 8388607 < n at lo; omega) hi
    · exact fun n lo hi => Hybrid.masked_parent _ _ n lo (by change n ≤ 8388607 at hi; omega)
    · intro n lo hi
      change 8388607 < n at lo
      change n < 16777216 at hi
      have hk : 2 * (n - 2 ^ 23) + 1 < 2 ^ 24 := by omega
      have hk0 : 2 * (n - 2 ^ 23) < 2 ^ 24 := by omega
      unfold parentInputP
      rw [c3_read_compression, show pairWord n = replyW + 25 * (2 * (n - 2 ^ 23)) + 21 by unfold pairWord replyW; omega,
        exit_state_mem]
      rw [pair_parent_input (memoryView L) _ _ _ (replies (2 * (n - 2 ^ 23)) (by omega))
        (by rw [show replyW + 25 * (2 * (n - 2 ^ 23)) + 25 = replyW + 25 * (2 * (n - 2 ^ 23) + 1) by omega]
            exact replies _ hk)]
      have e0 : heap (2 * n) = c3pEvenDigest (oracle.permutation (pInput oracle msg salts ⟨2 * (n - 2 ^ 23), hk0⟩)) := by
        have := Hybrid.heap_leaf oracle.compression (pLeaves oracle msg salts) ⟨2 * (n - 2 ^ 23), hk0⟩
        rw [show LENGTH + 2 * (n - 2 ^ 23) = 2 * n by have hL : LENGTH = 16777216 := rfl; omega] at this
        show Hybrid.heap oracle.compression (pLeaves oracle msg salts) (2 * n) = _
        rw [this]
        simp only [pLeaves, c3pFullLeafDigests, c3pLeafDigest, c3pDigestWindow]
        rw [if_pos (show c3pEven ⟨2 * (n - 2 ^ 23), hk0⟩ by unfold c3pEven; simp only; omega)]
        rfl
      have e1 : heap (2 * n + 1) =
          outputDigest (oracle.permutation (pInput oracle msg salts ⟨2 * (n - 2 ^ 23) + 1, hk⟩)) := by
        have := Hybrid.heap_leaf oracle.compression (pLeaves oracle msg salts) ⟨2 * (n - 2 ^ 23) + 1, hk⟩
        rw [show LENGTH + (2 * (n - 2 ^ 23) + 1) = 2 * n + 1 by have hL : LENGTH = 16777216 := rfl; omega] at this
        show Hybrid.heap oracle.compression (pLeaves oracle msg salts) (2 * n + 1) = _
        rw [this]
        simp only [pLeaves, c3pFullLeafDigests, c3pLeafDigest, c3pDigestWindow]
        rw [if_neg (show ¬ c3pEven ⟨2 * (n - 2 ^ 23) + 1, hk⟩ by unfold c3pEven; simp only; omega)]
        rfl
      rw [e0, e1]
    · exact pregs
  refine ⟨?_, ?_, ?_⟩
  · rw [show R = rootPrefix F 10 from rfl, root_copy_output F F9 F8]
    exact nodes 1 (by decide) (by decide)
  · intro n lo hi
    rw [show R = rootPrefix F 10 from rfl,
      root_preserves_heap_buffer F F8 (treeWord n) 32 (by unfold treeWord; omega)
        (by unfold treeWord; change n < 16777216 at hi; omega) (by decide)]
    exact nodes n lo hi
  · intro j hj
    rw [← replies j hj]
    funext ⟨k, hk⟩
    simp only [window]
    have wb : replyW + 25 * j + k < 2 ^ 33 := by unfold replyW; omega
    rw [show R = rootPrefix F 10 from rfl, root_word F F8 _ (by unfold replyW; omega) (by unfold replyW; omega),
      parent_phase_frame X pregs ppc F hit _ wb (by unfold treeWord replyW; omega), exit_state_mem]

end TwoPermutationPrototype.RV64.C3P
