import CommitGolfCandidate.OverlapCommitModel
import CommitGolfCandidate.TwoPermutationWideCommit
import CommitGolfCandidate.TwoPermutationSubmission
import CommitGolfCandidate.TwoPermutationWideParentMeaning
import CommitGolfCandidate.TwoPermutationRootBytes

namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open CommitGolfCandidate (checkEvaluation check_evaluation_support check_evaluation_pure
  check_evaluation_bind fixedOracleRun fixed_oracle_run_map oracle_run_bind oracle_run_pure
  splitBlocks split_blocks_bijective)


set_option maxRecDepth 16384
set_option maxHeartbeats 1500000
attribute [local irreducible] checkEvaluation wideCommitBody wideCommitTrace wideParentGroups rootPrefix

structure WideLeafMeaning (leaves : WideLeafExecution) where
  counted : ∀ oracle state, RunPublic oracle (leaves.trace state) 33554432
  content : ∀ (oracle : Oracle) (message : Message) (packed : BitVec (128*LENGTH)),
    let salts := splitBlocks 128 LENGTH packed
    let state := wideReadyState (Overlap.program.initialState .commit message) packed
    let out := (checkEvaluation oracle (leaves.trace state)).1
    ParentContent (parentSetup out 5) (Overlap.tree oracle message salts) salts (2^24-1)

private theorem wide_entry (message : Message) :
    CommitEntry (Overlap.program.initialState .commit message) := ⟨rfl,rfl,rfl,rfl⟩

theorem wide_counted_body (leaves : WideLeafExecution) (meaning : WideLeafMeaning leaves)
    (oracle : Oracle) (initial : MachineState) {bits : Nat} (packed : BitVec bits) :
    RunPublic oracle (wideCommitBody leaves initial packed) 50331647 := by
  unfold wideCommitBody
  apply run_bind_public _ _ _ 33554432 16777215 (meaning.counted ..)
  intro out
  exact run_bind_public _ _ _ (65793*255) 0 (counted_wide_parents ..) (fun _ => run_pure_public ..)

def widePackedOutput (leaves : WideLeafExecution) (oracle : Oracle) (initial : MachineState)
    {bits : Nat} (packed : BitVec bits) : Execution :=
  ⟨.success,(checkEvaluation oracle (wideCommitBody leaves initial packed)).1,638059030,50331647⟩

theorem wide_counted_trace (leaves : WideLeafExecution) (meaning : WideLeafMeaning leaves)
    (oracle : Oracle) (initial : MachineState) :
    oracle.run (wideCommitTrace leaves initial) =
      (do let packed ← $ᵗ BitVec (8*((initialPrefix initial 11).getReg .x11).toNat)
          return (widePackedOutput leaves oracle initial packed,50331647)) := by
  unfold wideCommitTrace
  rw [CommitGolfCandidate.oracle_run_coins_bind]
  apply bind_congr_of_forall_mem_support
  intro packed _
  rw [oracle_run_bind,show oracle.run (wideCommitBody leaves initial packed)=_ from
    wide_counted_body leaves meaning oracle initial packed,pure_bind]
  simp only [oracle_run_pure,pure_bind,Nat.add_zero]
  rfl

private theorem wide_output_eq (leaves : WideLeafExecution) (oracle : Oracle)
    (initial : MachineState) {bits : Nat} (packed : BitVec bits) :
    widePackedOutput leaves oracle initial packed =
      ⟨.success,(checkEvaluation oracle (wideCommitBody leaves initial packed)).1,638059030,50331647⟩ := rfl

private theorem execution_state (state : MachineState) :
    (⟨.success,state,638059030,50331647⟩ : Execution).state = state := rfl

attribute [local irreducible] widePackedOutput

private theorem evaluated_finish (oracle : Oracle) (p : OracleComp World MachineState)
    (f : MachineState → OracleComp World MachineState) (finish : MachineState → MachineState) :
    (checkEvaluation oracle (p >>= fun s => f s >>= fun t => pure (finish t))).1 =
      finish (checkEvaluation oracle (f (checkEvaluation oracle p).1)).1 := by
  simp only [check_evaluation_bind,check_evaluation_pure]

private theorem wide_eval_body (oracle : Oracle) (p : OracleComp World MachineState) :
    (checkEvaluation oracle (do
        let out ← p
        let parents ← wideParentGroups 18556 65793 255 (parentSetup out 5)
        return rootPrefix parents 10)).1 =
      rootPrefix (checkEvaluation oracle (wideParentGroups 18556 65793 255
        (parentSetup (checkEvaluation oracle p).1 5))).1 10 :=
  evaluated_finish oracle p
    (fun out => wideParentGroups 18556 65793 255 (parentSetup out 5))
    (fun parents => rootPrefix parents 10)

private theorem wide_packed_state (leaves : WideLeafExecution) (oracle : Oracle)
    (initial : MachineState) {bits : Nat} (packed : BitVec bits) :
    let state := wideReadyState initial packed
    let out := (checkEvaluation oracle (leaves.trace state)).1
    let parents := (checkEvaluation oracle (wideParentGroups 18556 65793 255 (parentSetup out 5))).1
    (widePackedOutput leaves oracle initial packed).state = rootPrefix parents 10 := by
  have projection := congrArg Execution.state (wide_output_eq leaves oracle initial packed)
  refine projection.trans ((execution_state _).trans ?_)
  unfold wideCommitBody
  exact wide_eval_body oracle (leaves.trace (wideReadyState initial packed))

private def serializationModel := Assembly.checkerReference commitImage

private theorem codecABI : CommitABI serializationModel where
  code := rfl
  message := rfl
  output := rfl
  trapdoor := rfl
  size := rfl
  fuel := by decide

private theorem wide_serialized (parents : MachineState) (heap : Nat → BitVec 256)
    (salts : Index → BitVec 128) (result : Execution)
    (state : result.state=rootPrefix parents 10) (heapReg : parents.getReg .x9=4294971424)
    (outReg : parents.getReg .x8=4294971392) (content : ParentContent parents heap salts 0) :
    (Overlap.program.readCommit result).1=heap 1 ∧
    (∀ n, 0<n → n<2*LENGTH → (Overlap.program.readCommit result).2.extractLsb' (256*n) 256=heap n) ∧
    (∀ i : Index, (Overlap.program.readCommit result).2.extractLsb' (8*(80*LENGTH+16*i.val)) 128=salts i) := by
  have equality : Overlap.program.readCommit result = serializationModel.readCommit result := by
    simp only [Submission.readCommit, Overlap.program, serializationModel, Assembly.checkerReference]
  rw [equality]
  exact serialized_parent_results serializationModel codecABI parents heap salts result state heapReg outReg content

theorem wide_physical_results (leaves : WideLeafExecution) (meaning : WideLeafMeaning leaves)
    (oracle : Oracle) (message : Message) (packed : BitVec (128*LENGTH)) :
    let result := widePackedOutput leaves oracle (Overlap.program.initialState .commit message) packed
    let output := Overlap.program.readCommit result
    let salts := splitBlocks 128 LENGTH packed
    let heap := Overlap.tree oracle message salts
    output.1=heap 1 ∧
    (∀ n, 0<n → n<2*LENGTH → output.2.extractLsb' (256*n) 256=heap n) ∧
    (∀ i : Index, output.2.extractLsb' (8*(80*LENGTH+16*i.val)) 128=salts i) := by
  let initial := Overlap.program.initialState .commit message
  let ready := wideReadyState initial packed
  let out := (checkEvaluation oracle (leaves.trace ready)).1
  let start := parentSetup out 5
  let parents := (checkEvaluation oracle (wideParentGroups 18556 65793 255 start)).1
  let salts := splitBlocks 128 LENGTH packed
  let heap := Overlap.tree oracle message salts
  have tree (n : Nat) (positive : 0<n) (inner : n<LENGTH) :
      heap n=oracle.compression (heap (2*n+1) ++ heap (2*n)) :=
    transcript_heap_parent false _ _ n positive inner
  have initialContent := meaning.content oracle message packed
  have content : ParentContent parents heap salts 0 :=
    wide_parent_content oracle 18556 65793 255 start heap salts (by decide) tree initialContent
  have finished := leaves.finished initial (wide_entry message) packed out
    (check_evaluation_support oracle (leaves.trace ready))
  obtain ⟨regs,pc,keep⟩ := wide_parent_setup_ready out finished.pc finished.selector finished.heap finished.stride finished.stop
  obtain ⟨endRegs,_,resultReg⟩ := wide_parent_phase_post start regs pc
    (check_evaluation_support oracle (wideParentGroups 18556 65793 255 start))
  have x8 : parents.getReg .x8=4294971392 := resultReg.trans (keep.trans finished.output)
  exact wide_serialized parents heap salts
    (widePackedOutput leaves oracle initial packed) (wide_packed_state leaves oracle initial packed)
    endRegs.heap x8 content

noncomputable def widePackSaltTape : CompleteSaltTape → BitVec (128*LENGTH) :=
  (Equiv.ofBijective (splitBlocks 128 LENGTH) (split_blocks_bijective 128 LENGTH (by decide))).symm

private theorem wide_split_pack (salts : CompleteSaltTape) :
    splitBlocks 128 LENGTH (widePackSaltTape salts)=salts :=
  (Equiv.ofBijective _ (split_blocks_bijective 128 LENGTH (by decide))).apply_symm_apply salts

private theorem wide_pack_split (packed : BitVec (128*LENGTH)) :
    widePackSaltTape (splitBlocks 128 LENGTH packed)=packed :=
  (Equiv.ofBijective _ (split_blocks_bijective 128 LENGTH (by decide))).symm_apply_apply packed

noncomputable def wideTrapdoor (leaves : WideLeafExecution) (oracle : Oracle)
    (message : Message) (salts : CompleteSaltTape) :
    BitVec (8*Overlap.program.sizes.trapdoor) :=
  (Overlap.program.readCommit (widePackedOutput leaves oracle
    (Overlap.program.initialState .commit message) (widePackSaltTape salts))).2

private theorem wide_normalize_draw {α : Type} (bits : Nat)
    (width : bits=128*LENGTH) (f : {n : Nat} → BitVec n → α) :
    (do let packed ← $ᵗ BitVec bits; pure (f packed) : ProbComp α) =
      (do let packed ← $ᵗ BitVec (128*LENGTH); pure (f packed)) := by subst bits; rfl

theorem wide_commit_distribution (leaves : WideLeafExecution) (meaning : WideLeafMeaning leaves)
    (oracle : Oracle) (message : Message) :
    fixedOracleRun oracle (Overlap.program.scheme.commit message) =
      (do let packed ← $ᵗ BitVec (128*LENGTH)
          let salts := splitBlocks 128 LENGTH packed
          pure (Overlap.tree oracle message salts 1,wideTrapdoor leaves oracle message salts)) := by
  let initial := Overlap.program.initialState .commit message
  have entry := wide_entry message
  have width : 8*((initialPrefix initial 11).getReg .x11).toNat=128*LENGTH := by
    rw [(setup_registers initial entry).size]; rfl
  change fixedOracleRun oracle (Overlap.program.readCommit <$> Overlap.program.run .commit message)=_
  rw [submission_wide_commit_run leaves Overlap.program rfl (by decide) message entry, fixed_oracle_run_map]
  unfold fixedOracleRun
  rw [wide_counted_trace leaves meaning]
  simp only [map_bind,map_pure]
  change (do let packed ← $ᵗ BitVec (8*((initialPrefix initial 11).getReg .x11).toNat)
             pure (Overlap.program.readCommit (widePackedOutput leaves oracle initial packed)))=_
  rw [wide_normalize_draw _ width (fun {_} packed =>
    Overlap.program.readCommit (widePackedOutput leaves oracle initial packed))]
  apply bind_congr_of_forall_mem_support
  intro packed _
  have physical := wide_physical_results leaves meaning oracle message packed
  dsimp only [wideTrapdoor]
  rw [wide_pack_split]
  exact congrArg pure (Prod.ext physical.1 rfl)

noncomputable def wideVerifiedTranscript (leaves : WideLeafExecution) (meaning : WideLeafMeaning leaves) :
    Overlap.CommitTranscript Overlap.program :=
  Overlap.CommitTranscript.ofPacked Overlap.program (wideTrapdoor leaves)
    (by
      intro oracle message
      rw [wide_commit_distribution leaves meaning] <;> rfl)
    (by
      intro oracle message salts i
      have eq := (wide_physical_results leaves meaning oracle message (widePackSaltTape salts)).2.2 i
      simpa only [Opening.trapdoorSalt,wideTrapdoor,wide_split_pack] using eq)
    (by
      intro oracle message salts n positive bound
      have eq := (wide_physical_results leaves meaning oracle message (widePackSaltTape salts)).2.1 n positive bound
      simpa only [Opening.trapdoorHeap,wideTrapdoor,wide_split_pack,Overlap.tree] using eq)

end TwoPermutationPrototype.RV64
