import CommitGolfCandidate.CapBResult
import CommitGolfCandidate.Layout2CapStage
import CommitGolfCandidate.GroupOpenVirtual
import CommitGolfCandidate.GroupOpenHeaderSpec

/-! Layout 2 V2b with the one-byte search: Astra's cap-stage machine theorem (`CapB.cap_stage`, from word 6960 to the HALT) in the form the
opener's assembly uses (`Layout2CapStage.CapStage CapB.capRaw`). The record loop's `CapEntry` gives Astra's
`CapB.CapEntry` for the groups of the opened positions and the raw trapdoor heap; the honest relation
(`HonestCap CapB.capRaw`) is a separate premise. -/
namespace CommitGolfCandidate.Layout2CapStage
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype TwoPermutationPrototype.GroupedOpening

/-- With at least one opened position the cap root is marked (every cap group lies in `[256, 512)`). -/
theorem cap_root_marked (positions : Positions) (positive : 0 < positions.card) :
    Sampling.capIsMarked (Opening.groupsBefore positions positions.card) 1 8 = true := by
  have size : (Opening.groupsBefore positions positions.card).length = positions.card := by
    simp [Opening.groupsBefore]
  cases hg : Opening.groupsBefore positions positions.card with
  | nil => rw [hg] at size; simp at size; omega
  | cons g rest =>
    have member : g ∈ Opening.groupsBefore positions positions.card := by rw [hg]; simp
    unfold Opening.groupsBefore at member
    obtain ⟨index, _, value⟩ := List.mem_map.1 member
    have bound : index.val < 16777216 := index.isLt
    have high : g / 2^8 = 1 := by
      rw [← value]
      change (16777216+index.val)/65536/256 = 1
      omega
    simp only [Sampling.capIsMarked, List.any_eq_true, beq_iff_eq]
    exact ⟨g, by simp, high⟩

/-- Dword `i` of heap node `n < 512` in a state agreeing with the loaded input is dword `i` of the raw digest. -/
theorem heap_word (s : Submission) (layout : OpeningLayout s) (td : BitVec (8*s.sizes.trapdoor)) (p : Positions)
    (st : MachineState) (input : SameOpeningInput (s.initialState .opening (td,p)) st) (n i : Nat)
    (hn : n<512) (hi : i<4) :
    st.getMem (BitVec.ofNat 64 (trapdoorBase+32*n+8*i))=(td.extractLsb' (256*n) 256).extractLsb' (64*i) 64 := by
  have tb : trapdoorBase=4294971424 := rfl
  have pb : proofBase=13824430176 := rfl
  have tb8 : trapdoorBase%8=0 := by decide
  have inside : trapdoorBase+32*n+8*i<proofBase := by omega
  have tbytes : GroupedOpening.trapdoorBytes=5100273664 := by decide
  rw [input (trapdoorBase+32*n+8*i) (by omega) inside (by omega),
    ← word_at _ (trapdoorBase+32*n+8*i) (by omega), show trapdoorBase+32*n+8*i=trapdoorBase+(32*n+8*i) by omega,
    input_trapdoor_slice s layout td p (32*n+8*i) 8 (by omega),
    nested_slice (outer:=256*n) (width:=256) (start:=64*i) (len:=64) td (by omega),
    show 8*(32*n+8*i)=256*n+64*i by omega]

/-- The record loop's entry state is Astra's cap entry for the opened groups and the raw trapdoor heap. -/
theorem astra_entry (s : Submission) (layout : OpeningLayout s) (td : BitVec (8*s.sizes.trapdoor)) (p : Positions)
    (st : MachineState) (e : CapEntry (s.initialState .opening (td,p)) st p) :
    CapB.CapEntry (Opening.groupsBefore p p.card) (fun n => td.extractLsb' (256*n) 256) p.card st where
  pcAt := e.pc
  count := by change p.card ≤ LENGTH; simpa [Index] using Finset.card_le_univ p
  marked := cap_root_marked p e.nonempty
  marks := fun i hi => e.marked i hi
  x26 := e.marks
  x25 := e.heap.trans (by decide)
  x27 := e.leaves
  x23 := e.one
  x20 := e.begin.trans (by decide)
  x21 := e.dest.trans (congrArg (fun q => BitVec.ofNat 64 (q+534*p.card)) (show proofBase=CapB.proofBase by decide))
  source := fun n hn i hi => heap_word s layout td p st e.input n i hn hi

/-- Astra's cap stage, with the honest relation as a premise, is the opener's `CapStage`. -/
theorem cap_stage_of (honest : HonestCap CapB.capRaw) : CapStage CapB.capRaw where
  run := by
    intro s layout td p st _ e
    obtain ⟨t, steps, cycles, sb, cb, ran, len, kept, bytes⟩ := CapB.cap_stage (astra_entry s layout td p st e)
    have nodes : Opening.openingNodes p=Sampling.capFrontierNodes (Opening.groupsBefore p p.card) 1 8 := by
      unfold Opening.openingNodes; rw [if_neg (by have := e.nonempty; omega)]
    refine ⟨t, steps, cycles, by omega, cb, ran, by rw [nodes]; unfold dropped; exact len, ?_, ?_⟩
    · intro a lo hi; exact kept a lo hi
    · unfold frontierDigests; rw [nodes]; exact bytes
  length := fun ds => by rw [CapB.capRaw_length, Layout2.Cap.size_eq]; rfl
  honest := honest

end CommitGolfCandidate.Layout2CapStage
