import CommitGolfCandidate.Layout2QuartetInput
namespace CommitGolfCandidate.Layout2.Quartet
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype TwoPermutationPrototype.RV64
set_option maxHeartbeats 1500000
set_option maxRecDepth 12000
attribute [local irreducible] Submission.initialState ArtifactEncoding.decode
theorem prepare_run (τ : Tables) (wf : WellFormed τ)
    (physical : ∀ j,j<85440 → GroupedOpening.pget K1Artifact.checkData j=tableByte τ j)
    (i : CheckInput) (fits : i.proof.length≤8959041024) (long : 534*i.positions.card ≤ i.proof.length) :
    let k:=i.positions.card
    let s:=candidate.initialState .check i
    ∃ t h c, h+34359803904≤2^41 ∧ Runs checkImage s t h c ∧ Normalized τ (candidate.initialState .check (prepared i)) t k := by
  dsimp only
  let s:=candidate.initialState .check i
  let v:=candidate.initialState .check (prepared i)
  let k:=i.positions.card
  have args:=initial_args i fits
  obtain ⟨m,h,cost,ran,pcM,wrote,kept⟩:=prefix_run s k _ (selectors i.positions) args (init_entry i).1 (init_entry i).2 (load_indices i) long
  have equiv:=prepared_memory i fits long wrote
  have argM : Input m k i.proof.length := ⟨(kept _ (by decide)).trans args.scratch,(kept _ (by decide)).trans args.output,
    (kept _ (by decide)).trans args.stack,(kept _ (by decide)).trans args.card,(kept _ (by decide)).trans args.length,args.count,fits⟩
  have tab : TablesAt τ m := by
    intro r lo hi
    have bound:=args.count
    have cfg:=tableConfig τ wf r proofBase lo hi (by unfold proofBase tableBase;omega) (by decide)
    exact (initial_tables τ wf physical i fits r lo hi).writes cfg wrote (by unfold proofBase tableBase;omega)
  have program : Program checkImage := concrete_program
  obtain ⟨t,rp,done⟩:=prologue program wf m k _ pcM argM long tab
    (fun j hj=>(equiv _ (by unfold scratchBase MEMORY_BYTES;omega)).trans (scratch_clean (prepared i) j hj))
  refine ⟨t,_,_,fuel k h args.count cost,ran.thenDo rp,done.start,?_,?_⟩
  · intro r
    rw [done.register]
    split <;> first | rfl | skip
    split <;> first | rfl | skip
    rename_i free
    rw [kept r free]
    exact same_args candidate i r
  · intro q fit
    rw [done.memory q fit]
    split
    · rename_i hit
      apply convertAt_congr wf k _ (by omega)
      intro j bj
      exact equiv _ (by have:=args.count;unfold proofBase MEMORY_BYTES;omega)
    · exact equiv q fit

end CommitGolfCandidate.Layout2.Quartet
