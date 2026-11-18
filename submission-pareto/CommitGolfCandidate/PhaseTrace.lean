import CommitGolfCandidate.PhaseSite
import CommitGolfCandidate.GroupOpenRecordRun

namespace TwoPermutationPrototype.PhaseOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CommitGolfCandidate
open GroupedOpening
open Opening (sortedIndex)
set_option maxHeartbeats 2300000
set_option maxRecDepth 16000

theorem nonce_witness (s : MachineState) (i : Index) (o : Nat) (fit : o<LENGTH) (start : PrefixStart s i o) :
    FieldInputs .nonce (nonceSetup s) (nonceAddress i) (recordBase o) := by
  let t := nonceSetup s
  let v := copyState .nonce t
  have h := nonce_setup_post s
  have z := slot_post v
  obtain ⟨srcEven,dstEven,sep,room⟩ := all_nonce_copies_fit i o fit
  have field : FieldInputs .nonce t (nonceAddress i) (recordBase o) :=
    ⟨by rw [h.1,start.pc]; rfl,physical_nonce_source s i start.nonce start.index,
      by simpa [CopySite.destOffset] using (h.2.2.2.2 .x21 (by decide) (by decide)).trans start.output,
      sep,room,srcEven,dstEven⟩
  exact field

theorem quartet_witness (s : MachineState) (i : Index) (o : Nat) (j : Fin 3) (fit : o<LENGTH)
    (start : GroupCursor s i o j.val) : FieldInputs (.quartet j) (quartetHead j s)
    (leafAddress (i.val ^^^ (j.val+1))) (recordBase o+(16+32*j.val)) := by
  let t := quartetHead j s
  let src := leafAddress (i.val ^^^ (j.val+1))
  let dest := recordBase o+(16+32*j.val)
  have head := quartet_head_post j s
  have bounds := leaf_address_inside _ (sibling_in_message i j)
  have srcA : src%8=0 := bounds.1
  have before : src+32 ≤ nonceBase := bounds.2.2
  have room := all_record_ends_fit o fit
  have count := j.isLt
  have actualRoom : dest+32 ≤ MEMORY_BYTES := by unfold dest recordBase recordBytes at *; omega
  have baseAligned : proofBase%2=0 := by decide
  have endIx := indices_before_records
  have endSalt := nonces_end_at_indices
  have field : FieldInputs (.quartet j) t src dest := by
    refine ⟨?_,quartet_physical_source s i j start.group start.low,?_,?_,actualRoom,by change src%2=0; omega,?_⟩
    · rw [head.1,start.pc]
      change BitVec.ofNat 64 _ + BitVec.ofNat 64 16 = _
      rw [← BitVec.ofNat_add]
      congr 1
      simp [CopySite.start]; omega
    · rw [show t.getReg .x21=s.getReg .x21 from head.2.2.2 .x21 (by decide),start.output]
      rw [← BitVec.ofNat_add]
      change BitVec.ofNat 64 (recordBase o+16+32*j.val)=BitVec.ofNat 64 (recordBase o+(16+32*j.val))
      rw [Nat.add_assoc]
    · change src+32 ≤ dest
      unfold dest recordBase; omega
    · unfold dest recordBase recordBytes; omega
  exact field

theorem sibling_witness (state : MachineState) (index : Index) (ordinal : Nat) (bounded : ordinal < LENGTH)
    (level : Fin 14) (cursor : LowerCursor state index ordinal level.val) :
    FieldInputs (siblingSite level) (headPrefix state 3) (siblingAddress index level.val)
      (siblingDestination ordinal level.val) := by
  let site := siblingSite level
  let prepared := headPrefix state 3
  let copied := copyState site prepared
  let done := siblingBlock level state
  have head := sibling_head_post state
  have tail := sibling_tail_post copied level
  have ordinalFit := all_sibling_copies_fit index ordinal level.val bounded level.isLt
  have start : state.pc = BitVec.ofNat 64 (4096+4*siblingStart level) := by
    simpa only [lowerPC, dif_pos level.isLt, Fin.eta] using cursor.pc
  have before : prepared.pc = BitVec.ofNat 64 (4096+4*site.start) := by
    rw [head.1, start]
    change BitVec.ofNat 64 _+BitVec.ofNat 64 12 = _
    rw [← BitVec.ofNat_add, ← sibling_copy_start level]
    congr 1
  have field : FieldInputs site prepared (siblingAddress index level.val)
      (siblingDestination ordinal level.val) := by
    refine ⟨before, by simpa [site] using physical_sibling_source state index _ cursor.heap cursor.node,
      by simpa [site] using (head.2.2.2 .x21 (by decide)).trans cursor.dest, ?_, ?_, ordinalFit.1, ordinalFit.2.1⟩
    · simpa only [site, sibling_width_exact] using ordinalFit.2.2.1
    · simpa only [site, sibling_width_exact] using ordinalFit.2.2.2
  exact field

theorem prefix_ready (s : Submission) (layout : OpeningLayout s) (t : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (st : MachineState) (o : Nat) (present : o<positions.card)
    (atStart : RecordStart s t positions st o) : PrefixStart st (sortedIndex positions o present) o := by
  let i := sortedIndex positions o present
  have cardinal : positions.card≤LENGTH := by simpa [Index] using Finset.card_le_univ positions
  have io := indices_before_records
  have ia : trapdoorBase ≤ indicesBase+8*o := by unfold indicesBase; omega
  have ib : indicesBase+8*o<proofBase := by omega
  have ram : MEMORY_BYTES<2^64 := by decide
  have bounds := packed_proof_memory
  have access : accessValid (st.getReg .x8) 8 = true := by
    rw [atStart.index]
    apply Opening.aligned_access
    · have : indicesBase %8=0 := by decide
      omega
    · omega
  have index : st.getMem (st.getReg .x8)=BitVec.ofNat 64 i.val := by
    have align : (indicesBase+8*o)%8=0 := by
      have a : indicesBase%8=0 := by decide
      omega
    rw [atStart.index,atStart.input _ ia ib align]
    exact input_index s layout t positions o present
  have px : PrefixStart st i o :=
    ⟨atStart.pc,atStart.heap,atStart.slots,atStart.mult,atStart.nonce,atStart.leaves,atStart.dest,index,access⟩
  exact px

structure Rel (old actual : MachineState) : Prop where
  mem : old.mem=actual.mem
  reg : ∀ r : Reg, r≠.x31 → old.getReg r=actual.getReg r

theorem ordinary_memory (site : CopySite) (s : MachineState) (src dst : Nat)
   (field : FieldInputs site s src dst) :
    (copyState site s).mem=(ProjectedHalfword.copyLoopMemory false site.halfwords s (addr src) (addr dst)).mem := by
  apply QuartetCopy.copy_field_memory (fieldCode site)
  refine ⟨?_,field.sourceReg,?_,?_,field.targetFit,field.sourceEven,field.targetEven⟩
  · simpa [fieldCode] using field.pc
  · simpa [fieldCode] using field.targetReg
  · exact field.disjoint.trans (Nat.le_trans (Nat.le_add_right _ _) field.targetFit)

theorem field_refinement {im : Image} {p f} {v u : MachineState} {src dst : Nat}
    (aligned : FieldState im p f u src dst) (field : FieldInputs (oldSite f) v src dst) (rel : Rel v u) :
    PairRun im u (moveList (widths p f) u src dst) (2*(widths p f).length) ∧
    Rel (copyState (oldSite f) v) (moveList (widths p f) u src dst) := by
  refine ⟨field_run aligned,?_,?_⟩
  · rw [ordinary_memory _ _ _ _ field,field_memory aligned]
    exact ProjectedHalfword.copyLoopMemory_congr _ _ _ _ _ _ rel.mem
  · intro r safe
    rw [copy_register _ _ _ safe,moveList_register _ _ _ _ _ safe]
    exact rel.reg _ safe

theorem field_prepared {im : Image} {p f} {old actual : MachineState} {src dst : Nat}
    (reference : FieldInputs (oldSite f) old src dst) (same : Rel old actual)
    (pc : actual.pc=fieldAddress p f) (sourceAligned : src%8=0)
    (targetAligned : dst%8=(6*p.val+fieldOffset f)%8)
    (fetches : ∀ (pc : Nat) (op : Instr), fieldPC p f≤pc → pc<fieldPC p f+2*(widths p f).length →
      decodeAt pc=some op → ∀ v : MachineState, v.pc=addr (4096+4*pc) → fetch im v=some (.base op)) :
    FieldState im p f actual src dst := by
  obtain ⟨sr,dr,sz⟩:=old_matches f
  have safe : srcReg f≠.x31 := by unfold srcReg;split <;> decide
  refine ⟨pc,?_,?_,sourceAligned,targetAligned,?_,?_,fetches⟩
  · rw [←same.reg _ safe,←sr];exact reference.sourceReg
  · rw [←same.reg _ (by decide),←dr];exact reference.targetReg
  · rw [←sz];exact reference.disjoint
  · rw [←sz];exact reference.targetFit

#print axioms field_refinement
#print axioms prefix_ready
end TwoPermutationPrototype.PhaseOpening
