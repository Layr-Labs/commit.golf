import CommitGolfCandidate.Layout2QuartetInput
namespace CommitGolfCandidate.Layout2.Quartet
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype TwoPermutationPrototype.RV64
set_option maxHeartbeats 1500000
set_option maxRecDepth 12000
attribute [local irreducible] Submission.initialState ArtifactEncoding.decode
theorem prepare_from (τ : Tables) (wf : WellFormed τ)
    (physical : ∀ j,j<85440 → CommitGolfCandidate.Layout2Helpers.pget K1Artifact.checkData j=tableByte τ j)
    (i : CheckInput) (fits : i.proof.length≤8959041024) (long : 534*i.positions.card ≤ i.proof.length)
    (u : MachineState) (pcU : u.pc=pc 1001) (startKept : Kept temps (candidate.initialState .check i) u)
    (sameMem : ∀ q,q<MEMORY_BYTES → byte u q=byte (candidate.initialState .check i) q) :
    let k:=i.positions.card
    ∃ t h c, h≤9+65*k+prologueSteps k ∧ Runs checkImage u t h c ∧
      Normalized τ (candidate.initialState .check (prepared i)) t k := by
  dsimp only
  let s:=candidate.initialState .check i
  let k:=i.positions.card
  have args:=initial_args i fits
  have argU : Input u k i.proof.length := ⟨(startKept _ (by decide)).trans args.scratch,(startKept _ (by decide)).trans args.output,
    (startKept _ (by decide)).trans args.stack,(startKept _ (by decide)).trans args.card,
    (startKept _ (by decide)).trans args.length,args.count,fits⟩
  have idx : Indices u k (selectors i.positions) := by
    intro j hj
    let w:=1174405636+j
    have bound:=args.count
    have word:=bword (s:=u) (t:=s) w (by dsimp [w,MEMORY_BYTES];omega) (fun z hz=>sameMem _ (by dsimp [w,MEMORY_BYTES];omega))
    change u.getMem (addr (8*w))=s.getMem (addr (8*w)) at word
    rw [show 8*w=indicesBase+8*j by dsimp [w,indicesBase];omega] at word
    rw [word];exact load_indices i j hj
  obtain ⟨m,h,cost,ran,pcM,w0,k0⟩:=prefix_run u k _ (selectors i.positions) argU
    ((startKept _ (by decide)).trans (init_entry i).1) pcU idx long
  have kept:=startKept.trans k0
  have wrote : Writes s m proofBase (534*k) (payload s k (selectors i.positions)) := by
    intro q fit;rw [w0 q fit];split
    · rename_i hit
      have inside:=(index_facts false k (selectors i.positions) (q-proofBase)).1 (by omega)
      have memRoom : proofBase+534*k≤MEMORY_BYTES := by have:=args.count;dsimp only [proofBase,MEMORY_BYTES,k];omega
      exact sameMem _ (by omega)
    · exact sameMem q fit
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
  refine ⟨t,_,_,(by omega : h+prologueSteps k≤9+65*k+prologueSteps k),ran.thenDo rp,done.start,?_,?_⟩
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
