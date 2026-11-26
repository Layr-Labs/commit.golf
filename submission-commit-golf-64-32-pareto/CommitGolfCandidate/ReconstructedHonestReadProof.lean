import CommitGolfCandidate.ReconstructedReturn
import CommitGolfCandidate.ReconstructedOpeningRead
import CommitGolfCandidate.ReconstructedEncoding
import CommitGolfCandidate.ReconstructedHonestHeap

namespace CommitGolfCandidate.Reconstruction.HonestReadProof
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64 OpeningPut Wire

set_option maxRecDepth 16384
attribute [local irreducible] ArtifactEncoding.decode execute

/-- Exact fixed-oracle termination and ABI projection for already serialized
fields, for any preceding machine charges. -/
theorem fields (o : Oracle) (s : MachineState) (fs : List Field)
    (pc : s.pc=10660) (stack : s.getReg .x2=68719474016) (ret : s.getMem 68719476328=4176)
    (cursor : (s.getReg .x7).toNat=bits fs) (small : bits fs≤70000000000)
    (room : alignedBytes (bits fs)≤8355061248) (data : Serialized (memoryView s) (pack fs)) :
    ∃ final : MachineState,
      (∀ fuel, fixedOracleRun o (execute (Artifact.submission.image .opening) (23+fuel) s true)=
        pure (⟨.success,final,23,0⟩ : Execution)) ∧ final.mem=s.mem ∧
      ∀ c q, Artifact.submission.openingSucceeded ⟨.success,final,c,q⟩=true ∧
        Artifact.submission.readProof ⟨.success,final,c,q⟩=bytes fs := by
  obtain ⟨t,run,size,mem⟩ := Return.execute_return_memory s pc stack ret (cursor ▸ small)
  rw [cursor] at size
  refine ⟨t,fun fuel => ?_,mem,?_⟩
  · rw [run fuel,fixed_oracle_run_pure]
  · intro c q
    have view : memoryView t=memoryView s := by funext j; exact congrFun mem _
    refine ⟨?_,OpeningRead.proof _ fs rfl size room (view ▸ data)⟩
    change (true && decide ((t.getReg .x11).toNat≤8355061248))=true
    rw [size,decide_eq_true room]; rfl

theorem profile (o : Oracle) (s : MachineState) (tree : Encoding.Tree) (ps : Positions)
    (salts : TwoPermutationPrototype.Sampling.OpenedSalts ps)
    (pc : s.pc=10660) (stack : s.getReg .x2=68719474016) (ret : s.getMem 68719476328=4176)
    (cursor : (s.getReg .x7).toNat=bits (Encoding.fields tree ps salts))
    (data : Serialized (memoryView s) (pack (Encoding.fields tree ps salts))) :
    ∃ final : MachineState,
      (∀ fuel, fixedOracleRun o (execute (Artifact.submission.image .opening) (23+fuel) s true)=
        pure (⟨.success,final,23,0⟩ : Execution)) ∧ final.mem=s.mem ∧
      ∀ c q, Artifact.submission.openingSucceeded ⟨.success,final,c,q⟩=true ∧
        Artifact.submission.readProof ⟨.success,final,c,q⟩=bytes (Encoding.fields tree ps salts) := by
  let xs : List (Fin (2^24)) := ps.sort (·≤·)
  have len : (ps.sort (·≤·)).length=ps.card := Finset.length_sort _
  change xs.length=ps.card at len
  have bound : ps.card≤2^24 := by change ps.card≤LENGTH;simpa [Index] using Finset.card_le_univ ps
  have small := HonestHeap.cursor_all xs
  have room := (HonestHeap.all_fit xs (len ▸ bound)).2.1
  have width := Encoding.all_bits tree ps salts
  change bits (Encoding.fields tree ps salts)=Frontier.cursor xs at width
  exact fields o s _ pc stack ret cursor (by rw [width];omega) (width ▸ room) data

end CommitGolfCandidate.Reconstruction.HonestReadProof
