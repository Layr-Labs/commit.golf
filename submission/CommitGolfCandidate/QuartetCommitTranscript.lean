import CommitGolfCandidate.QuartetPhysical
import CommitGolfCandidate.QuartetRVTranscript
import CommitGolfCandidate.TwoPermutationHidingBridge

namespace TwoPermutationPrototype.QuartetCommit
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
set_option maxRecDepth 16384
set_option maxHeartbeats 1700000
local instance quartetCommitDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
attribute [local irreducible] checkEvaluation qReady QuartetLeaves.groups qGroups packedParentsTrace packedParentGroups rootPrefix packedOutput

theorem counted_body (oracle : Oracle) (initial : MachineState) {bits : Nat} (packed : BitVec bits) :
    RunPublic oracle (commitBody initial packed) 41943039 := by
  unfold commitBody
  apply run_bind_public _ _ _ 33554432 8388607 (QuartetLeaves.counted_groups ..); intro leaves
  apply run_bind_public _ _ _ 4194304 4194303 (q_groups_counted ..);intro quad
  apply run_bind_public _ _ _ 127 4194176 (counted_packed_parents ..);intro finalPre
  exact run_bind_public _ _ _ 4194176 0 (counted_packed_groups ..) (fun _ => run_pure_public ..)

attribute [local irreducible] commitBody

theorem counted_trace (oracle : Oracle) (initial : MachineState) :
    oracle.run (commitTrace initial) = (do let packed ← $ᵗ BitVec (8*((prePrefix initial 15).getReg .x11).toNat)
                                           return (packedOutput oracle initial packed,41943039)) := by
  unfold commitTrace;rw [oracle_run_coins_bind];apply bind_congr_of_forall_mem_support
  intro packed _
  rw [oracle_run_bind,show oracle.run (commitBody initial packed)=_ from counted_body oracle initial packed,pure_bind]
  simp only [oracle_run_pure,pure_bind,Nat.add_zero]
  unfold packedOutput;rfl

noncomputable def packTape : CompleteSaltTape → BitVec (128*LENGTH) :=
  (Equiv.ofBijective (splitBlocks 128 LENGTH) (split_blocks_bijective 128 LENGTH (by decide))).symm

theorem split_pack (salts : CompleteSaltTape) : splitBlocks 128 LENGTH (packTape salts)=salts :=
  (Equiv.ofBijective _ (split_blocks_bijective 128 LENGTH (by decide))).apply_symm_apply salts

theorem pack_split (packed : BitVec (128*LENGTH)) : packTape (splitBlocks 128 LENGTH packed)=packed :=
  (Equiv.ofBijective _ (split_blocks_bijective 128 LENGTH (by decide))).symm_apply_apply packed

noncomputable def commitTrapdoor (oracle : Oracle) (msg : Message) (salts : CompleteSaltTape) : BitVec (8*actual.sizes.trapdoor) :=
  (actual.readCommit (packedOutput oracle (actual.initialState .commit msg) (packTape salts))).2

private theorem normalize_draw {α : Type} (bits : Nat) (h : bits=128*LENGTH) (f : {n : Nat} → BitVec n → α) :
    (do let packed ← $ᵗ BitVec bits;pure (f packed) : ProbComp α) =
      (do let packed ← $ᵗ BitVec (128*LENGTH);pure (f packed)) := by subst bits;rfl

attribute [local irreducible] commitTrace physicalHeap prePrefix

private theorem selected_run {α : Type} (oracle : Oracle) (s : MachineState) (f : Execution → α) :
    fixedOracleRun oracle (f <$> commitTrace s) =
      (do let packed ← $ᵗ BitVec (8*((prePrefix s 15).getReg .x11).toNat); pure (f (packedOutput oracle s packed))) := by
  rw [fixed_oracle_run_map];unfold fixedOracleRun;rw [counted_trace]
  simp only [map_bind,map_pure]

private theorem selected_width {α : Type} (oracle : Oracle) (s : MachineState) (entry : CommitEntry s) (f : Execution → α) :
    fixedOracleRun oracle (f <$> commitTrace s) =
      (do let packed ← $ᵗ BitVec (128*LENGTH);pure (f (packedOutput oracle s packed))) := by
  have width : 8*((prePrefix s 15).getReg .x11).toNat=128*LENGTH := by rw [(seed_registers s entry).size];rfl
  exact (selected_run oracle s f).trans (normalize_draw _ width (fun {_} packed => f (packedOutput oracle s packed)))

private theorem physical_pair (oracle : Oracle) (msg : Message) (packed : BitVec (128*LENGTH)) :
    actual.readCommit (packedOutput oracle (actual.initialState .commit msg) packed) =
      (physicalHeap oracle msg (splitBlocks 128 LENGTH packed) 1,commitTrapdoor oracle msg (splitBlocks 128 LENGTH packed)) := by
  rw [commitTrapdoor,pack_split];exact Prod.ext (physical_results oracle msg packed).1 rfl

theorem fixed_coin_distribution (oracle : Oracle) (msg : Message) :
    fixedOracleRun oracle (actual.scheme.commit msg) =
      (do let packed ← $ᵗ BitVec (128*LENGTH)
          let salts:=splitBlocks 128 LENGTH packed
          pure (physicalHeap oracle msg salts 1,commitTrapdoor oracle msg salts)) := by
  let s:=actual.initialState .commit msg
  have entry : CommitEntry s := ⟨rfl,rfl,rfl,rfl⟩
  have equality:=congrArg (fun p : OracleComp World Execution => fixedOracleRun oracle (actual.readCommit <$> p)) (artifact_run msg)
  refine equality.trans ((selected_width oracle s entry actual.readCommit).trans ?_)
  apply bind_congr_of_forall_mem_support;intro packed _
  exact congrArg (fun pair => (pure pair : ProbComp (Commitment × BitVec (8*actual.sizes.trapdoor)))) (physical_pair oracle msg packed)

theorem tape_distribution (oracle : Oracle) (msg : Message) :
    fixedOracleRun oracle (actual.scheme.commit msg) =ᵈ
      (do let salts ← sampleCompleteSaltTape; pure (physicalHeap oracle msg salts 1,commitTrapdoor oracle msg salts)) := by
  rw [fixed_coin_distribution]
  exact packed_salt_tape_uniform (fun salts => pure (physicalHeap oracle msg salts 1,commitTrapdoor oracle msg salts))

theorem commit_really_refines : Sampling.Quartet.QuartetRefines actual.scheme Sampling.Quartet.builder := by
  apply QuartetRV.transcript_refines actual QuartetRV.manifest_abi commitTrapdoor
  · intro oracle msg
    simpa only [physicalHeap] using tape_distribution oracle msg
  · intro oracle msg salts i
    have val:=(physical_results oracle msg (packTape salts)).2.2.2 i
    simpa only [commitTrapdoor,split_pack] using val
  · intro oracle msg salts i
    have val:=(physical_results oracle msg (packTape salts)).2.2.1 i
    simpa only [commitTrapdoor,split_pack,originalLeaf,Sampling.Quartet.leafAt,dif_pos i.isLt] using val
  · intro oracle msg salts n lo hi
    have val:=(physical_results oracle msg (packTape salts)).2.1 n lo hi
    simpa only [commitTrapdoor,split_pack,physicalHeap] using val

theorem actual_hiding : actual.scheme.Hiding (fun _ budget => min 1 (((budget : ℝ)+1)/2^120)) :=
  Sampling.Quartet.concrete_hiding_of_refinement actual.scheme commit_really_refines

end TwoPermutationPrototype.QuartetCommit
