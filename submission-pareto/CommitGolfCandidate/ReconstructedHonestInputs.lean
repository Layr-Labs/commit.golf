import CommitGolf.Artifact
import CommitGolfCandidate.InputMemory
import CommitGolfCandidate.ReconstructedHonestCopy
import CommitGolfCandidate.ReconstructedHonestOpeningStart
import CommitGolfCandidate.ReconstructedProfile

namespace CommitGolfCandidate.Reconstruction.HonestInputs
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 16384
attribute [local irreducible] ArtifactEncoding.decode

abbrev Trapdoor := BitVec (8*Artifact.submission.sizes.trapdoor)
private abbrev image := Artifact.submission.image .opening

theorem data_base : dataBase image = 68719476336 := by
  change 16*((2^36 - (ArtifactEncoding.decode 8 Artifact.openingData).length)/16) = _
  rw [ArtifactEncoding.length_decode]; decide

def initial (trap : Trapdoor) (ps : Positions) := Artifact.submission.initialState .opening (trap,ps)
def body (trap : Trapdoor) (ps : Positions) := HonestCopy.ready false (initial trap ps)
def first (trap : Trapdoor) (ps : Positions) := HonestOpeningStart.entry (body trap ps)

private theorem card_bound (ps : Positions) : ps.card ≤ 2^24 := by
  change ps.card ≤ LENGTH
  simpa [Index] using Finset.card_le_univ ps

private theorem positive_word (ps : Positions) (h : 0 < ps.card) : BitVec.ofNat 64 ps.card ≠ 0 := by
  intro z
  have same := congrArg BitVec.toNat z
  have card := card_bound ps
  change ps.card % 2^64 = 0 at same
  rw [Nat.mod_eq_of_lt (by omega)] at same
  omega

private theorem loader_sp (trap : Trapdoor) (ps : Positions) :
    (initial trap ps).getReg .x2 = 68719476336 := by
  change BitVec.ofNat 64 (dataBase image) = _
  rw [data_base]; rfl

/-- The actual nonempty ABI input reaches the first record with its sorted
position count, index pointer, empty cursor, and saved return address. -/
theorem first_record (trap : Trapdoor) (ps : Positions) (positive : 0 < ps.card) (fuel : Nat) :
    let t := first trap ps
    execute image (398+fuel) (initial trap ps) true =
      (do let r ← execute image fuel t true; return r.charge 398 0) ∧
    t.pc = 4668 ∧ t.getReg .x7 = 0 ∧ t.getReg .x12 = BitVec.ofNat 64 ps.card ∧
    t.getReg .x11 = 5905584160 ∧ t.getReg .x2 = 68719474016 ∧ t.getMem 68719476328 = 4176 := by
  let s := initial trap ps
  have stack : s.getReg .x2 = 68719476336 := loader_sp trap ps
  obtain ⟨run,pc,ra,count,_,sp,_,_⟩ := HonestCopy.enter_body false s rfl (positive_word ps positive)
    stack (87+fuel) true
  obtain ⟨entryPC,entrySp,_,_,cursor,entryCount,_,_,ret⟩ := HonestOpeningStart.entry_registers (body trap ps)
  have ptr := (HonestOpeningStart.entry_constants (body trap ps)).1
  refine ⟨?_,entryPC,cursor,entryCount.trans count,ptr,entrySp,ret.trans ra⟩
  rw [show 398+fuel = 311+(87+fuel) by omega]
  change execute (HonestCopy.image false) (311+(87+fuel)) s true = _
  change execute (HonestCopy.image false) (311+(87+fuel)) s true = (do
    let r ← execute (HonestCopy.image false) (87+fuel) (body trap ps) true; return r.charge 311 0) at run
  have setup := HonestOpeningStart.execute_setup (body trap ps) pc (sp.trans stack) fuel true
  change execute (HonestCopy.image false) (87+fuel) (body trap ps) true = (do
    let r ← execute image fuel (first trap ps) true; return r.charge 87 0) at setup
  rw [run,setup]
  simp [Execution.charge,←Nat.add_assoc]

private theorem outside (trap : Trapdoor) (ps : Positions) (a : Nat)
    (range : a+8 ≤ 4294971424 ∨ 5905584160+8*ps.card ≤ a) :
    ∀ j < 8, (Artifact.submission.inputBuffers .opening (trap,ps)).find?
      (fun b => decide (b.address ≤ a+j ∧ a+j < b.address+b.length)) = none := by
  intro j hj
  have tree : Artifact.submission.layout.trapdoor = 4294971424 := rfl
  have size : Artifact.submission.sizes.trapdoor = 1610612736 := rfl
  have indices : Artifact.submission.layout.indices = 5905584160 := rfl
  simp only [Submission.inputBuffers,List.find?_cons,fixedBuffer,positionsBuffer,tree,size,indices,Finset.length_sort]
  simp only [show ¬(4294971424 ≤ a+j ∧ a+j < 4294971424+(8*1610612736+7)/8) by omega,
    show ¬(5905584160 ≤ a+j ∧ a+j < 5905584160+8*ps.card) by omega,decide_false,List.find?_nil]

/-- All hash-cap flags and untouched output proof words start at zero, even
when the input lists occupy the complete index buffer. -/
theorem initial_zero (trap : Trapdoor) (ps : Positions) (a : Nat)
    (range : a+8 ≤ 4294971424 ∨ 5905584160+8*ps.card ≤ a) (stack : a+8 ≤ 68719476336) :
    (initial trap ps).getMem (BitVec.ofNat 64 a) = 0 := by
  rw [initial,initial_input_word Artifact.submission .opening (trap,ps) a (by omega)]
  have bytes (j : Nat) (hj : j ∈ Finset.range 8) : inputByte Artifact.submission .opening (trap,ps) (a+j) = 0 := by
    have inside := Finset.mem_range.mp hj
    unfold inputByte
    rw [outside trap ps a range j inside]
    change (if dataBase image ≤ a+j then _ else 0) = 0
    rw [data_base,ite_eq_right (by omega)]
  have zero : (∑ j ∈ Finset.range 8, (inputByte Artifact.submission .opening (trap,ps) (a+j)).toNat * 2^(8*j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj; rw [bytes j hj]; simp
  rw [zero]; rfl

/-- A normal initial slot contains exactly its sorted little-endian ABI position. -/
theorem initial_index (trap : Trapdoor) (ps : Positions) (i : Nat) (hi : i < ps.card) :
    (initial trap ps).getMem (BitVec.ofNat 64 (5905584160+8*i)) =
      BitVec.ofNat 64 ((ps.sort (· ≤ ·))[i]'(by simpa using hi)).val := by
  have bound := card_bound ps
  rw [initial,initial_input_word Artifact.submission .opening (trap,ps) _ (by omega)]
  let value := (ps.sort (· ≤ ·))[i]'(by simpa using hi)
  have bytes (j : Nat) (hj : j < 8) : inputByte Artifact.submission .opening (trap,ps) (5905584160+8*i+j) =
      BitVec.ofNat 8 (value.val/2^(8*j)) := by
    have tree : Artifact.submission.layout.trapdoor=4294971424 := rfl
    have size : Artifact.submission.sizes.trapdoor=1610612736 := rfl
    have idx : Artifact.submission.layout.indices=5905584160 := rfl
    simp only [inputByte,Submission.inputBuffers,List.find?_cons,fixedBuffer,positionsBuffer,tree,size,idx,Finset.length_sort]
    simp only [show ¬(4294971424 ≤ 5905584160+8*i+j ∧ 5905584160+8*i+j < 4294971424+(8*1610612736+7)/8) by omega,
      show 5905584160 ≤ 5905584160+8*i+j ∧ 5905584160+8*i+j < 5905584160+8*ps.card by omega,
      decide_false,decide_true,and_self]
    rw [show (5905584160+8*i+j-5905584160)/8 = i by omega, show (5905584160+8*i+j-5905584160)%8=j by omega,
      List.getElem?_eq_getElem (by simpa using hi)]
  have swapped : (∑ j ∈ Finset.range 8, (inputByte Artifact.submission .opening (trap,ps) (5905584160+8*i+j)).toNat * 2^(8*j)) =
      ∑ j ∈ Finset.range 8, (BitVec.ofNat 8 (value.val/2^(8*j))).toNat*2^(8*j) := by
    apply Finset.sum_congr rfl
    intro j hj; rw [bytes j (Finset.mem_range.mp hj)]
  rw [swapped]
  change BitVec.ofNat 64 _ = BitVec.ofNat 64 value.val
  congr 1
  have small : value.val < 16777216 := value.isLt
  norm_num [Finset.sum_range_succ,BitVec.toNat_ofNat]
  omega

/-- Only the table destination and stack were written before the first record. -/
theorem first_frame (trap : Trapdoor) (ps : Positions) (nonempty : 0 < ps.card) (a : Nat)
    (lower : 2097552 ≤ a) (upper : a < 68719474016) :
    (first trap ps).getMem (BitVec.ofNat 64 a) = (initial trap ps).getMem (BitVec.ofNat 64 a) := by
  let s := initial trap ps
  have stack := loader_sp trap ps
  obtain ⟨_,_,_,_,_,_,_,frame⟩ := HonestCopy.enter_body false s rfl (positive_word ps nonempty) stack 0 true
  change (HonestOpeningStart.entry (body trap ps)).getMem _ = s.getMem _
  have small : (BitVec.ofNat 64 a).toNat = a := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have ub : (BitVec.ofNat 64 a).toNat < 68719474016 := by rwa [small]
  rw [HonestOpeningStart.entry_frame _ _ ub]
  apply frame
  intro j hj eq
  change j < 50 at hj
  have whereAt := congrArg BitVec.toNat eq
  change (BitVec.ofNat 64 a).toNat = (BitVec.ofNat 64 (2097152+8*j)).toNat at whereAt
  rw [small,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at whereAt
  omega

theorem first_index (trap : Trapdoor) (ps : Positions) (i : Nat) (present : i < ps.card) :
    (first trap ps).getMem (BitVec.ofNat 64 (5905584160+8*i)) =
      BitVec.ofNat 64 ((ps.sort (· ≤ ·))[i]'(by simpa using present)).val := by
  have card := card_bound ps
  rw [first_frame trap ps (by omega) _ (by omega) (by omega)]
  exact initial_index trap ps i present

theorem first_cap_zero (trap : Trapdoor) (ps : Positions) (nonempty : 0 < ps.card)
    (a : Nat) (lo : 4194304 ≤ a) (hi : a+8 ≤ 4260864) :
    (first trap ps).getMem (BitVec.ofNat 64 a) = 0 := by
  rw [first_frame trap ps nonempty _ (by omega) (by omega)]
  exact initial_zero trap ps a (Or.inl (by omega)) (by omega)

private def tableWord (j : Nat) := BitVec.ofNat 64 (∑ b ∈ Finset.range 8,
  (image.data[8*j+b]?.getD 0).toNat * 2^(8*b))

private theorem loader_table (trap : Trapdoor) (ps : Positions) (j : Nat) (hj : j < 50) :
    (initial trap ps).getMem (BitVec.ofNat 64 (68719476336+8*j)) = tableWord j := by
  rw [initial,initial_input_word Artifact.submission .opening (trap,ps) _ (by omega)]
  apply congrArg (BitVec.ofNat 64)
  apply Finset.sum_congr rfl
  intro b hb
  have small := Finset.mem_range.mp hb
  have card := card_bound ps
  unfold inputByte
  rw [outside trap ps _ (Or.inr (by omega)) b small]
  change (if dataBase image ≤ 68719476336+8*j+b then _ else (0 : Byte)).toNat * _ = _
  rw [data_base,ite_eq_left (by omega)]
  simp only [show 68719476336+8*j+b-68719476336 = 8*j+b by omega]

private theorem copied_table (trap : Trapdoor) (ps : Positions) (positive : 0 < ps.card)
    (j : Nat) (hj : j < 50) :
    (first trap ps).getMem (BitVec.ofNat 64 (2097152+8*j)) = tableWord j := by
  have copied := (HonestCopy.enter_body false (initial trap ps) rfl (positive_word ps positive)
    (loader_sp trap ps) 0 true).2.2.2.2.2.2.1 j hj
  change (body trap ps).getMem (BitVec.ofNat 64 (2097152+8*j)) =
    (initial trap ps).getMem (BitVec.ofNat 64 (68719476336+8*j)) at copied
  change (HonestOpeningStart.entry _).getMem _ = _
  rw [HonestOpeningStart.entry_frame _ _ (by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]; omega),copied]
  exact loader_table trap ps j hj

/-- The linked 25-entry width tables are installed at their real addresses and
agree entry-for-entry with the profile used by the bitstream and frontier proofs. -/
theorem first_tables (trap : Trapdoor) (ps : Positions) (positive : 0 < ps.card) (d : Fin 25) :
    (first trap ps).getMem (BitVec.ofNat 64 (2097152+8*d.val)) = BitVec.ofNat 64 (sameSize.lows[d.val]?.getD 0) ∧
    (first trap ps).getMem (BitVec.ofNat 64 (2097352+8*d.val)) = BitVec.ofNat 64 (sameSize.widths[d.val]?.getD 0) := by
  have contents : ∀ idx : Fin 25, tableWord idx.val = BitVec.ofNat 64 (sameSize.lows[idx.val]?.getD 0) ∧
      tableWord (25+idx.val) = BitVec.ofNat 64 (sameSize.widths[idx.val]?.getD 0) := by decide +kernel
  have bound := d.isLt
  rw [show 2097352+8*d.val = 2097152+8*(25+d.val) by omega,
    copied_table trap ps positive d.val (by omega),copied_table trap ps positive (25+d.val) (by omega)]
  exact contents d

end CommitGolfCandidate.Reconstruction.HonestInputs
