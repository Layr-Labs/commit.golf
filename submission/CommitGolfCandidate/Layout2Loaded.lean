import CommitGolfCandidate.Layout2Initial
import CommitGolfCandidate.Layout2Prologue
import CommitGolfCandidate.Layout2Table
import CommitGolfCandidate.TwoPermutationPackedHeaderAssembly
import CommitGolfCandidate.TwoPermutationCollectTable

namespace CommitGolfCandidate.Layout2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype TwoPermutationPrototype.RV64
open TwoPermutationPrototype.Checker (RecordInputFrame check_input_proof_byte check_scratch_word_zero check_mark_zero)
open TwoPermutationPrototype.Packed.Checker (HeaderEntry)
open TwoPermutationPrototype.GroupedOpening.Wide (byte_at)
set_option maxRecDepth 6000
attribute [local irreducible] ArtifactEncoding.decode
set_option maxHeartbeats 1600000
theorem initial_args (i : CheckInput) (fits : i.proof.length≤8959041024) :
    Input (candidate.initialState .check i) i.positions.card i.proof.length := by
  refine ⟨rfl,rfl,?_,rfl,rfl,?_,fits⟩
  · change addr (dataBase (candidate.image .check))=_
    rw [data_base]
  · exact Checker.checker_positions_bound i

theorem convertAt_congr {τ : Tables} (wf : WellFormed τ) (k j : Nat) (inside : j<534*k)
    {x y : Nat→Byte} (agree : ∀ q, q<534*k → x q=y q) :
    convertAt τ k x j=convertAt τ k y j := by
  let g:=j/2136;let r:=blockSize k g
  have lim : g≤k/4 := by dsimp [g];omega
  have endB : 2136*g+534*r≤534*k := by unfold r blockSize;split <;> omega
  have sz : 0<r ∧ r≤4 ∧ j%2136<534*r := by dsimp [r,blockSize,g];split <;> omega
  simp only [convertAt,if_pos inside]
  exact gather_congr wf sz.1 sz.2.1 sz.2.2 (fun q small=>agree _ (by omega))

theorem virtual_low {τ : Tables} (wf : WellFormed τ) (i : CheckInput) (fits : i.proof.length≤8959041024)
    (long : 534*i.positions.card≤ i.proof.length) (t : MachineState)
    (done : Normalized τ (candidate.initialState .check i) t i.positions.card)
    (q : Nat) (low : q<2^35) :
    byte t q=byte (QAssembly.submission.initialState .check (converted τ i)) q := by
  let s:=candidate.initialState .check i
  let k:=i.positions.card
  have small : q<MEMORY_BYTES := by unfold MEMORY_BYTES;omega
  have lowT : q<tableBase := by unfold tableBase;omega
  have read:=done.memory q small
  by_cases hit : proofBase≤q ∧ q<proofBase+i.proof.length
  · let j:=q-proofBase
    have e : q=proofBase+j := by dsimp [j];omega
    have jFit : j< i.proof.length := by dsimp [j];omega
    have valid : (converted τ i).proof.length≤QAssembly.submission.sizes.proof := by
      change (convert τ k i.proof).length≤8959041024;simpa using fits
    have fromProof (n : Nat) (hn : n< i.proof.length) : source s n=i.proof[n]?.getD 0 := by
      unfold source
      rw [below_table i _ (by unfold proofBase tableBase;omega)]
      exact (TwoPermutationPrototype.Checker.check_input_proof_byte i fits n hn).trans (by simp [hn])
    have loaded:=TwoPermutationPrototype.Checker.check_input_proof_byte (converted τ i) valid j (by simpa [converted] using jFit)
    have got : byte (QAssembly.submission.initialState .check (converted τ i)) q=
        convertAt τ k (fun n=>i.proof[n]?.getD 0) j := by
      refine (congrArg (byte (QAssembly.submission.initialState .check (converted τ i))) e).trans ?_
      simpa only [byte,converted,convert,List.getElem_ofFn,show QAssembly.submission.layout.proof=proofBase from rfl] using loaded
    rw [got,read]
    by_cases rec : j<534*k
    · rw [if_pos (by dsimp [k,j] at rec;omega)]
      exact convertAt_congr wf k j rec (fun n hn=>fromProof n (by omega))
    · rw [if_neg (by dsimp [j,k] at rec;omega)]
      rw [convertAt,if_neg rec]
      exact (congrArg (byte s) e).trans (fromProof j jFit)
  · have outside : q<proofBase ∨ proofBase+i.proof.length≤q := by omega
    rw [read,if_neg (by omega),below_table i q lowT]
    exact (other_proof i _ (convert_length _ _ _) q (by omega) outside).symm

theorem record_entry {τ : Tables} (wf : WellFormed τ) (i : CheckInput) (fits : i.proof.length≤8959041024)
    (long : 534*i.positions.card≤ i.proof.length) (t : MachineState) (done : Normalized τ (candidate.initialState .check i) t i.positions.card) :
    RecordInputFrame (converted τ i) 0 t ∧
      (∀ group < 512, Opening.machineMarks t group=0) := by
  have words (w : Nat) (small : w<2^32) : memoryView t w=memoryView (QAssembly.submission.initialState .check (converted τ i)) w :=
    bword w (by unfold MEMORY_BYTES;omega) (fun j hj=>virtual_low wf i fits long t done _ (by omega))
  refine ⟨fun w small _=>words w small,?_⟩
  intro group small
  have a:=words (512+group) (by omega)
  have old:=check_mark_zero (converted τ i) group small
  exact (Checker.checker_marks_as_word t group).trans (a.trans old)

def header_entry {τ i t} (done : Normalized τ (candidate.initialState .check i) t i.positions.card) :
    HeaderEntry (converted τ i) := by
  refine ⟨t,?_,done.start,?_,?_,?_,?_,?_,?_⟩
  · rw [done.register];rfl
  all_goals first | (rw [done.register];rfl) | (rw [done.register];simp [converted,temps];rfl)

end CommitGolfCandidate.Layout2
