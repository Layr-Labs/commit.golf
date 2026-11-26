import CommitGolfCandidate.NonceChainMemory
import CommitGolfCandidate.NonceChainRepresentation
import CommitGolfCandidate.TwoPermutationPinnedTranscript
import CommitGolfCandidate.TwoPermutationPackedCommit
import CommitGolfCandidate.TwoPermutationPackedParentMeaning
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
  transcriptHeap true oracle.compression (pinnedFullLeafDigests (BiPermutation.equiv Block oracle.permutation) message salts)

open CommitGolfCandidate.Permutation.NonceChain (Key actualNonces)

set_option maxRecDepth 16384
set_option maxHeartbeats 1500000
attribute [local irreducible] checkEvaluation packed_wideCommitBody packed_wideCommitTrace packedParentGroups rootPrefix

structure PackedLeafMeaning (leaves : PackedLeafExecution) where
  counted : ∀ oracle state, RunPublic oracle (leaves.trace state) 33554432
  content : ∀ (oracle : Oracle) (message : Message) (salts : CompleteSaltTape) (state : MachineState),
    Chain.BodyRegs state → Chain.BodyContent state message salts →
    let out := (checkEvaluation oracle (leaves.trace state)).1
    ParentContent (zeroEntry out) (packedPublicTree oracle message salts) salts (2^24-1)

private theorem packed_wide_entry (message : Message) :
    CommitEntry (packedSubmission.initialState .commit message) := ⟨rfl,rfl,rfl,rfl⟩

theorem packed_wide_counted_body (leaves : PackedLeafExecution) (meaning : PackedLeafMeaning leaves)
    (oracle : Oracle) (ready : MachineState) :
    RunPublic oracle (packed_wideCommitBody leaves ready) 50331647 := by
  unfold packed_wideCommitBody
  apply run_bind_public _ _ _ 33554432 16777215 (meaning.counted ..)
  intro out
  exact run_bind_public _ _ _ (28679*585) 0 (counted_packed_groups ..) (fun _ => run_pure_public ..)

def wideSeedOutput (leaves : PackedLeafExecution) (oracle : Oracle) (initial : MachineState)
    (key : Key) : Execution :=
  ⟨.success,(checkEvaluation oracle (packed_wideCommitBody leaves (Chain.chainFinalReady oracle.permutation initial key))).1,
    1528578519,51856895⟩

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
      ⟨.success,(checkEvaluation o (packed_wideCommitBody leaves (Chain.chainFinalReady o.permutation initial k))).1,1528578519,51856895⟩ := rfl

private theorem execution_state (s : MachineState) : (⟨.success,s,1528578519,51856895⟩ : Execution).state=s := rfl
attribute [local irreducible] wideSeedOutput Chain.chainFinalReady

private theorem evaluated_finish (oracle : Oracle) (p : OracleComp World MachineState)
    (f : MachineState → OracleComp World MachineState) (finish : MachineState → MachineState) :
    (checkEvaluation oracle (p >>= fun s => f s >>= fun t => pure (finish t))).1 =
      finish (checkEvaluation oracle (f (checkEvaluation oracle p).1)).1 := by
  simp only [check_evaluation_bind,check_evaluation_pure]

private theorem wide_eval_body (oracle : Oracle) (p : OracleComp World MachineState) :
    (checkEvaluation oracle (do
        let out ← p
        let parents ← packedParentGroups 248252 28679 585 (parentPrelude (zeroEntry out))
        return rootPrefix parents 10)).1 =
      rootPrefix (checkEvaluation oracle (packedParentGroups 248252 28679 585
        (parentPrelude (zeroEntry (checkEvaluation oracle p).1)))).1 10 :=
  evaluated_finish oracle p
    (fun out => packedParentGroups 248252 28679 585 (parentPrelude (zeroEntry out)))
    (fun parents => rootPrefix parents 10)

private theorem wide_seed_state (leaves : PackedLeafExecution) (oracle : Oracle)
    (initial : MachineState) (key : Key) :
    let state := Chain.chainFinalReady oracle.permutation initial key
    let out := (checkEvaluation oracle (leaves.trace state)).1
    let parents := (checkEvaluation oracle (packedParentGroups 248252 28679 585 (parentPrelude (zeroEntry out)))).1
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

private theorem content_prelude (s : MachineState) (heap : Nat → BitVec 256) (salts : Index → BitVec 128)
    (count : Nat) (prev : ParentContent s heap salts count) : ParentContent (parentPrelude s) heap salts count := by
  constructor
  · intro n lo hi
    rw [nodeDigest,CommitGolfCandidate.read_buffer_memory_congr _ s (parent_prelude_memory s)]
    exact prev.nodes n lo hi
  · intro i
    rw [nonceBuffer,CommitGolfCandidate.read_buffer_memory_congr _ s (parent_prelude_memory s)]
    exact prev.nonces i

theorem wide_physical_results (leaves : PackedLeafExecution) (meaning : PackedLeafMeaning leaves)
    (oracle : Oracle) (message : Message) (key : Key) :
    let result := wideSeedOutput leaves oracle (packedSubmission.initialState .commit message) key
    let output := packedSubmission.readCommit result
    let salts := maskedNonces oracle.permutation key
    let heap := packedPublicTree oracle message salts
    output.1=heap 1 ∧
    (∀ n, 0<n → n<2*LENGTH → output.2.extractLsb' (256*n) 256=heap n) ∧
    (∀ i : Index, output.2.extractLsb' (8*(80*LENGTH+16*i.val)) 128=salts i) := by
  let initial := packedSubmission.initialState .commit message
  let ready := Chain.chainFinalReady oracle.permutation initial key
  let out := (checkEvaluation oracle (leaves.trace ready)).1
  let start := zeroEntry out
  let parents := (checkEvaluation oracle (packedParentGroups 248252 28679 585 (parentPrelude start))).1
  let salts := maskedNonces oracle.permutation key
  let heap := packedPublicTree oracle message salts
  have tree (n : Nat) (positive : 0<n) (inner : n<LENGTH) :
      heap n=projectReply (oracle.compression (heap (2*n+1) ++ heap (2*n))) :=
    transcript_heap_parent true _ _ n positive inner
  have frame := Chain.final_content oracle packedSubmission rfl (by rfl) message key (packed_wide_entry message)
  have initialContent := meaning.content oracle message salts ready frame.1 frame.2
  have finished := leaves.finished ready frame.1 out
    (check_evaluation_support oracle (leaves.trace ready))
  obtain ⟨regs,pc,keep⟩ := zero_entry_ready out finished.pc finished.selector finished.heap finished.stride finished.stop
  have content : ParentContent parents heap salts 0 :=
    packed_parent_content oracle 248252 28679 585 (parentPrelude start) heap salts (by decide) tree
      (content_prelude _ _ _ _ initialContent) (parent_prelude_regs start _ regs) (parent_prelude_mask start)
  obtain ⟨endRegs,_,resultReg⟩ := packed_parent_phase_post start regs pc
    (check_evaluation_support oracle (packedParentGroups 248252 28679 585 (parentPrelude start)))
  have x8 : parents.getReg .x8=4294971392 := resultReg.trans (keep.trans finished.output)
  exact packed_wide_serialized parents heap salts
    (wideSeedOutput leaves oracle initial key) (wide_seed_state leaves oracle initial key)
    endRegs.heap x8 content

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
        (packedPublicTree o m (maskedNonces o.permutation k) 1,
         (packedSubmission.readCommit (wideSeedOutput leaves o initial k)).2) from Prod.ext root rfl]
    rfl
  nonce o m k i := (wide_physical_results leaves meaning o m k).2.2 i
  heap o m k n hp hl := (wide_physical_results leaves meaning o m k).2.1 n hp hl

end TwoPermutationPrototype.RV64
