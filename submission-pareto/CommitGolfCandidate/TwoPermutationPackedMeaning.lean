import CommitGolfCandidate.NonceChainMemory
import CommitGolfCandidate.NonceChainRepresentation
import CommitGolfCandidate.TwoPermutationPinnedTranscript
import CommitGolfCandidate.TwoPermutationPackedCommit
import CommitGolfCandidate.MixedWidthParentMeaning
import CommitGolfCandidate.MixedWidthStopSetup
import CommitGolfCandidate.TwoPermutationOpeningTranscript
import CommitGolfCandidate.TwoPermutationSubmission
import CommitGolfCandidate.TwoPermutationRootBytes

namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open CommitGolfCandidate (checkEvaluation check_evaluation_support check_evaluation_pure
  check_evaluation_bind fixedOracleRun fixed_oracle_run_map oracle_run_bind oracle_run_pure
  splitBlocks split_blocks_bijective)
abbrev packedSubmission : Submission := Artifact.submission

def packedPublicTree (oracle : Oracle) (message : Message) (salts : CompleteSaltTape) : Nat → BitVec 256 :=
  mixedTranscriptHeap oracle.compression (pinnedFullLeafDigests (BiPermutation.equiv Block oracle.permutation) message salts)

open CommitGolfCandidate.Permutation.NonceChain (Key actualNonces)

set_option maxRecDepth 16384
set_option maxHeartbeats 1500000
attribute [local irreducible] checkEvaluation packed_wideCommitBody packed_wideCommitTrace FullWidth.parentGroups packedParentGroups rootPrefix

structure PackedLeafMeaning (leaves : PackedLeafExecution) where
  counted : ∀ oracle state, RunPublic oracle (leaves.trace state) 33554432
  content : ∀ (oracle : Oracle) (message : Message) (salts : CompleteSaltTape) (state : MachineState),
    Chain.BodyRegs state → Chain.BodyContent state message salts →
    let out := (checkEvaluation oracle (leaves.trace state)).1
    ParentContent (parentSetup out 5) (packedPublicTree oracle message salts) salts (2^24-1)

private theorem packed_wide_entry (message : Message) :
    CommitEntry (packedSubmission.initialState .commit message) := ⟨rfl,rfl,rfl,rfl⟩

theorem packed_wide_counted_body (leaves : PackedLeafExecution) (meaning : PackedLeafMeaning leaves)
    (oracle : Oracle) (ready : MachineState) :
    RunPublic oracle (packed_wideCommitBody leaves ready) 50331647 := by
  unfold packed_wideCommitBody
  apply run_bind_public _ _ _ 33554432 16777215 (meaning.counted ..)
  intro out
  exact run_bind_public _ _ _ (32768*448) (16513*127)
    (counted_full_width_groups ..) (fun _ =>
      run_bind_public _ _ _ (16513*127) 0 (counted_packed_groups ..) (fun _ => run_pure_public ..))

def wideSeedOutput (leaves : PackedLeafExecution) (oracle : Oracle) (initial : MachineState)
    (key : Key) : Execution :=
  ⟨.success,(checkEvaluation oracle (packed_wideCommitBody leaves (Chain.chainFinalReady oracle.permutation initial key))).1,
    604913082,51856895⟩

theorem wide_counted_trace (leaves : PackedLeafExecution) (meaning : PackedLeafMeaning leaves)
    (oracle : Oracle) (initial : MachineState) :
    oracle.run (packed_wideCommitTrace leaves initial) =
      (do let k ← $ᵗ Key
          return (wideSeedOutput leaves oracle initial k,51856895)) := by
  unfold packed_wideCommitTrace
  rw [CommitGolfCandidate.oracle_run_coins_bind]
  apply bind_congr
  intro k
  have expand : oracle.run (Chain.expansion initial k) =
      pure (Chain.evalChain oracle.permutation 0 (Chain.chainInitial initial k) Chain.nonceChainCount,Chain.nonceChainCount) :=
    Chain.chain_fixed_run ..
  rw [oracle_run_bind,expand,pure_bind]
  simp only
  rw [oracle_run_bind,show oracle.run (packed_wideCommitBody leaves _) = _ from packed_wide_counted_body leaves meaning oracle _,pure_bind]
  simp only [oracle_run_pure,pure_bind]
  rfl

private theorem wide_output_eq (leaves : PackedLeafExecution) (o : Oracle) (initial : MachineState) (k : Key) :
    wideSeedOutput leaves o initial k =
      ⟨.success,(checkEvaluation o (packed_wideCommitBody leaves (Chain.chainFinalReady o.permutation initial k))).1,604913082,51856895⟩ := rfl

private theorem execution_state (s : MachineState) : (⟨.success,s,604913082,51856895⟩ : Execution).state=s := rfl
attribute [local irreducible] wideSeedOutput Chain.chainFinalReady

private theorem evaluated_finish (oracle : Oracle) (p : OracleComp World MachineState)
    (f : MachineState → OracleComp World MachineState) (finish : MachineState → MachineState) :
    (checkEvaluation oracle (p >>= fun s => f s >>= fun t => pure (finish t))).1 =
      finish (checkEvaluation oracle (f (checkEvaluation oracle p).1)).1 := by
  simp only [check_evaluation_bind,check_evaluation_pure]

private theorem evaluated_three_finish (oracle : Oracle) (p : OracleComp World MachineState)
    (first second : MachineState → OracleComp World MachineState) (finish : MachineState → MachineState) :
    (checkEvaluation oracle (do
      let one ← p
      let two ← first one
      let three ← second two
      pure (finish three))).1 =
      finish (checkEvaluation oracle (second (checkEvaluation oracle
        (first (checkEvaluation oracle p).1)).1)).1 := by
  simp only [check_evaluation_bind,check_evaluation_pure]

private theorem wide_eval_body (oracle : Oracle) (p : OracleComp World MachineState) :
    (checkEvaluation oracle (do
        let out ← p
        let full ← FullWidth.parentGroups 184768 32768 2097151 448 (mixedStopSetup (parentSetup out 5))
        let parents ← packedParentGroups 577992 16513 127 full
        return rootPrefix parents 10)).1 =
      rootPrefix (checkEvaluation oracle (packedParentGroups 577992 16513 127
        (checkEvaluation oracle (FullWidth.parentGroups 184768 32768 2097151 448
          (mixedStopSetup (parentSetup (checkEvaluation oracle p).1 5)))).1)).1 10 :=
  evaluated_three_finish oracle p
    (fun out => FullWidth.parentGroups 184768 32768 2097151 448 (mixedStopSetup (parentSetup out 5)))
    (fun full => packedParentGroups 577992 16513 127 full)
    (fun parents => rootPrefix parents 10)

private theorem wide_seed_state (leaves : PackedLeafExecution) (oracle : Oracle)
    (initial : MachineState) (key : Key) :
    let state := Chain.chainFinalReady oracle.permutation initial key
    let out := (checkEvaluation oracle (leaves.trace state)).1
    let full := (checkEvaluation oracle (FullWidth.parentGroups 184768 32768 2097151 448
      (mixedStopSetup (parentSetup out 5)))).1
    let parents := (checkEvaluation oracle (packedParentGroups 577992 16513 127 full)).1
    (wideSeedOutput leaves oracle initial key).state = rootPrefix parents 10 := by
  have projection := congrArg Execution.state (wide_output_eq leaves oracle initial key)
  refine projection.trans ((execution_state _).trans ?_)
  unfold packed_wideCommitBody
  exact wide_eval_body oracle (leaves.trace (Chain.chainFinalReady oracle.permutation initial key))

private def serializationModel := Assembly.checkerReference commitImage

private theorem codecABI : CommitABI serializationModel where
  code := rfl
  message := rfl
  output := rfl
  trapdoor := rfl
  size := rfl
  fuel := by decide

private theorem packed_wide_serialized (parents : MachineState) (heap : Nat → BitVec 256)
    (salts : Index → BitVec 128) (result : Execution)
    (state : result.state=rootPrefix parents 10) (heapReg : parents.getReg .x9=4294971424)
    (outReg : parents.getReg .x8=4294971392) (content : ParentContent parents heap salts 0) :
    (packedSubmission.readCommit result).1=heap 1 ∧
    (∀ n, 0<n → n<2*LENGTH → (packedSubmission.readCommit result).2.extractLsb' (256*n) 256=heap n) ∧
    (∀ i : Index, (packedSubmission.readCommit result).2.extractLsb' (8*(80*LENGTH+16*i.val)) 128=salts i) := by
  have equality : packedSubmission.readCommit result = serializationModel.readCommit result := by
    simp only [Submission.readCommit, packedSubmission, Artifact.submission, serializationModel, Assembly.checkerReference]
  rw [equality]
  exact serialized_parent_results serializationModel codecABI parents heap salts result state heapReg outReg content

private theorem mixed_packed_sequence_keep_output (remaining count : Nat) (state : MachineState) {out : MachineState}
    (reached : out ∈ support (packedParentsTrace remaining count state)) :
    out.getReg .x8=state.getReg .x8 := by
  induction count generalizing state with
  | zero =>
    simp only [packedParentsTrace,support_pure,Set.mem_singleton_iff] at reached
    rw [reached]
  | succ count ih =>
    simp only [packedParentsTrace,mem_support_bind_iff] at reached
    obtain ⟨answer,_,tail⟩ := reached
    exact (ih _ tail).trans (packed_parent_keeps_register state _ answer .x8 (by decide) (by decide))

private theorem mixed_packed_groups_keep_output (base : Word) (span groups : Nat)
    (state : MachineState) {out : MachineState}
    (reached : out ∈ support (packedParentGroups base span groups state)) :
    out.getReg .x8=state.getReg .x8 := by
  induction groups generalizing state with
  | zero =>
    simp only [packedParentGroups,support_pure,Set.mem_singleton_iff] at reached
    rw [reached]
  | succ groups ih =>
    simp only [packedParentGroups,mem_support_bind_iff] at reached
    obtain ⟨body,path,tail⟩ := reached
    have later := ih _ tail
    rw [MachineState.getReg_setPC] at later
    exact later.trans (mixed_packed_sequence_keep_output _ _ _ (out := body) path)

private theorem mixed_content_memory (before after : MachineState) (heap : Nat → BitVec 256)
    (salts : CompleteSaltTape) (remaining : Nat) (same : after.mem=before.mem)
    (prior : ParentContent before heap salts remaining) : ParentContent after heap salts remaining := by
  constructor
  · intro node lo hi
    exact (CommitGolfCandidate.read_buffer_memory_congr after before same _ _).trans
      (prior.nodes node lo hi)
  · intro index
    exact (CommitGolfCandidate.read_buffer_memory_congr after before same _ _).trans
      (prior.nonces index)

private theorem mixed_parent_phase_facts (oracle : Oracle) (before : MachineState)
    (digests : DigestTape) (salts : CompleteSaltTape)
    (regs : ParentRegs before (2^24-1)) (pc : before.pc=184756)
    (prior : ParentContent before (mixedTranscriptHeap oracle.compression digests) salts (2^24-1))
    (output : before.getReg .x8=4294971392) :
    let start := mixedStopSetup before
    let full := (checkEvaluation oracle (FullWidth.parentGroups 184768 32768 2097151 448 start)).1
    let parents := (checkEvaluation oracle (packedParentGroups 577992 16513 127 full)).1
    ParentContent parents (mixedTranscriptHeap oracle.compression digests) salts 0 ∧
      ParentRegs parents 0 ∧ parents.getReg .x8=4294971392 := by
  let start := mixedStopSetup before
  let full := (checkEvaluation oracle (FullWidth.parentGroups 184768 32768 2097151 448 start)).1
  let parents := (checkEvaluation oracle (packedParentGroups 577992 16513 127 full)).1
  have startRegs : ParentRegs start (2^24-1) := mixed_stop_parent_regs before _ regs
  have startPC : start.pc=184768 := by
    rw [mixed_stop_pc,pc]
    rfl
  have startContent := mixed_content_memory before start _ salts _ (mixed_stop_memory before) prior
  have content : ParentContent parents (mixedTranscriptHeap oracle.compression digests) salts 0 :=
    mixed_parent_phases_content oracle start digests salts startContent startRegs startPC
  have fullPost : ParentRegs full 2097151 ∧
      (0 < 448 → full.pc=FullWidth.parentPC 184768 32768+8) :=
    FullWidth.groups_post 184768 32768 2097151 448 start
      (by decide) (fun _ => startPC) startRegs (out := full)
    (check_evaluation_support oracle (FullWidth.parentGroups 184768 32768 2097151 448 start))
  have fullPC : full.pc=577992 := fullPost.2 (by decide)
  have endRegs : ParentRegs parents 0 := (packed_groups_post 577992 16513 127 full (by decide)
    (fun _ => fullPC) fullPost.1 (out := parents)
    (check_evaluation_support oracle (packedParentGroups 577992 16513 127 full))).1
  have fullOutput : full.getReg .x8=start.getReg .x8 :=
    FullWidth.groups_keep_register 184768 32768 2097151 448 start full .x8 (by decide) (by decide)
      (check_evaluation_support oracle (FullWidth.parentGroups 184768 32768 2097151 448 start))
  have finalOutput : parents.getReg .x8=full.getReg .x8 :=
    mixed_packed_groups_keep_output 577992 16513 127 full (out := parents)
      (check_evaluation_support oracle (packedParentGroups 577992 16513 127 full))
  have finalOutputValue : parents.getReg .x8=4294971392 :=
    finalOutput.trans (fullOutput.trans ((mixed_stop_register before .x8 (by decide)).trans output))
  exact ⟨content,endRegs,finalOutputValue⟩

theorem wide_physical_results (leaves : PackedLeafExecution) (meaning : PackedLeafMeaning leaves)
    (oracle : Oracle) (message : Message) (key : Key) :
    let result := wideSeedOutput leaves oracle (packedSubmission.initialState .commit message) key
    let output := packedSubmission.readCommit result
    let salts := actualNonces oracle.permutation key
    let heap := packedPublicTree oracle message salts
    output.1=heap 1 ∧
    (∀ n, 0<n → n<2*LENGTH → output.2.extractLsb' (256*n) 256=heap n) ∧
    (∀ i : Index, output.2.extractLsb' (8*(80*LENGTH+16*i.val)) 128=salts i) := by
  let initial := packedSubmission.initialState .commit message
  let ready := Chain.chainFinalReady oracle.permutation initial key
  let out := (checkEvaluation oracle (leaves.trace ready)).1
  let before := parentSetup out 5
  let start := mixedStopSetup before
  let full := (checkEvaluation oracle (FullWidth.parentGroups 184768 32768 2097151 448 start)).1
  let parents := (checkEvaluation oracle (packedParentGroups 577992 16513 127 full)).1
  let salts := actualNonces oracle.permutation key
  let heap := packedPublicTree oracle message salts
  have frame := Chain.final_content oracle packedSubmission rfl (by rfl) message key (packed_wide_entry message)
  have initialContent := meaning.content oracle message salts ready frame.1 frame.2
  have finished := leaves.finished ready frame.1 out
    (check_evaluation_support oracle (leaves.trace ready))
  obtain ⟨regs,pc,keep⟩ := packed_wide_parent_setup_ready out finished.pc finished.selector finished.heap finished.stride finished.stop
  have facts := mixed_parent_phase_facts oracle before
    (pinnedFullLeafDigests (BiPermutation.equiv Block oracle.permutation) message salts) salts
    regs pc initialContent (keep.trans finished.output)
  exact packed_wide_serialized parents heap salts
    (wideSeedOutput leaves oracle initial key) (wide_seed_state leaves oracle initial key)
    facts.2.1.heap facts.2.2 facts.1

abbrev PackedCommitTranscript := PackedOpening.ChainRepresentation packedSubmission

noncomputable def packedVerifiedTranscript (leaves : PackedLeafExecution) (meaning : PackedLeafMeaning leaves) :
    PackedCommitTranscript where
  trapdoorOf o m k := (packedSubmission.readCommit (wideSeedOutput leaves o (packedSubmission.initialState .commit m) k)).2
  distribution o m := by
    let initial := packedSubmission.initialState .commit m
    change (fixedOracleRun o (packedSubmission.readCommit <$> packedSubmission.run .commit m)) =ᵈ _
    rw [packed_submission_wide_commit_run leaves packedSubmission packed_manifest_image.symm (by decide) m (packed_wide_entry m),fixed_oracle_run_map]
    unfold fixedOracleRun
    rw [wide_counted_trace leaves meaning]
    simp only [map_bind,map_pure]
    apply EvalDistEq.bind_right
    intro k
    have root := (wide_physical_results leaves meaning o m k).1
    rw [show packedSubmission.readCommit (wideSeedOutput leaves o initial k) =
        (packedPublicTree o m (actualNonces o.permutation k) 1,
         (packedSubmission.readCommit (wideSeedOutput leaves o initial k)).2) from Prod.ext root rfl]
    rfl
  nonce o m k i := (wide_physical_results leaves meaning o m k).2.2 i
  heap o m k n hp hl := (wide_physical_results leaves meaning o m k).2.1 n hp hl

end TwoPermutationPrototype.RV64
