import CommitGolfCandidate.TwoPermutationPackedRecordLeafPrelude
import CommitGolfCandidate.TwoPermutationPackedRecordLeafCalls
import CommitGolfCandidate.TwoPermutationPackedRecordComposition
import CommitGolfCandidate.QuartetCheckBlock

namespace TwoPermutationPrototype.Packed.RecordLeaf
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling TwoPermutationPrototype.Packed.Checker
open TwoPermutationPrototype.Checker (beginRecord beginLower record_setup_post record_setup_register
  lower_setup_post lower_setup_register lower_setup_mem checkIndexWord checkSourceWord checker_positions_bound
  RecordInputFrame honestIndex record_input_index check_recorded_bind check_recorded_map)
set_option maxRecDepth 8192
set_option maxHeartbeats 1400000

private theorem addr_shift (i : Nat) : (BitVec.ofNat 64 i <<< 8) = BitVec.ofNat 64 (256*i) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 i * BitVec.ofNat 64 256 = _
  rw [←BitVec.ofNat_mul,Nat.mul_comm i]

theorem staged_reg (s : MachineState) (r : Reg) (keep : r ≠ .x31) :
    (staged s).getReg r = (beginRecord s 6).getReg r := copy_field_register _ _ _ keep

private theorem staged_saved (s : MachineState) (r : Reg) (h6 : r≠.x6) (h28 : r≠.x28)
    (h10 : r≠.x10) (h11 : r≠.x11) (h13 : r≠.x13) (h31 : r≠.x31) :
    (staged s).getReg r = s.getReg r :=
  (staged_reg s r h31).trans (record_setup_register s r h6 h28 h10 h11 h13)

theorem staged_scratch (s : MachineState) : (staged s).getReg .x4=s.getReg .x4 :=
  staged_saved s _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem loaded_index (input : CheckInput) (ordinal : Nat) (h : ordinal < input.positions.card)
    (s : MachineState) (cursor : RecordCursor input ordinal s) (framed : RecordInputFrame input ordinal s) :
    s.getMem (s.getReg .x8) = BitVec.ofNat 64 (honestIndex input.positions ordinal h).val.val := by
  rw [cursor.index]; exact record_input_index input ordinal h s framed

theorem leaf_ready (input : CheckInput) (ordinal : Nat) (h : ordinal < input.positions.card)
    (s : MachineState) (fits : ProofWithin input) (cursor : RecordCursor input ordinal s)
    (framed : RecordInputFrame input ordinal s) :
    LeafReady (staged s) (checkSourceWord ordinal) 1534 (honestIndex input.positions ordinal h).val := by
  have r := record_setup_post s
  have card := checker_positions_bound input
  have c := stage_ready input ordinal h s fits cursor
  refine ⟨copy_field_pc _ _ _ _ c,(staged_reg s .x10 (by decide)).trans (r.2.2.1.trans cursor.value),
    (staged_scratch s).trans cursor.nonceScratch,
    (staged_saved s .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans cursor.digest,?_,
    (staged_saved s .x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans cursor.selector,
    (staged_reg s .x11 (by decide)).trans r.2.2.2.1,(staged_reg s .x13 (by decide)).trans r.2.2.2.2.1,?_,?_⟩
  · rw [staged_reg _ _ (by decide),r.2.1,cursor.tag,loaded_index input ordinal h s cursor framed,addr_shift,firstTag]
    change BitVec.ofNat 64 4056+BitVec.ofNat 64 _=_
    rw [←BitVec.ofNat_add]
  all_goals unfold checkSourceWord; omega

def rawLeaf (oracle : Oracle) (ordinal : Nat) (index : Index) (s : MachineState) : MachineState × List PublicRow :=
  (checkEvaluation oracle (recordRows (leafQueries (staged s) (checkSourceWord ordinal) index))).1

/-- The leaf (record setup, nonce, two permutation calls) followed by the quartet block. -/
def block (oracle : Oracle) (ordinal : Nat) (index : Index) (s : MachineState) : RecordBlock :=
  let raw := rawLeaf oracle ordinal index s
  let q := quartetBlock oracle raw.1
  ⟨q.state,36+132,50+139,raw.2++q.rows⟩

theorem raw_digest_rows (oracle : Oracle) (ordinal : Nat) (index : Index) (s : MachineState) :
    let message := window (memoryView (staged s)) (checkSourceWord ordinal+5)
    let a := pinnedFirstRow oracle.permutation message
    let b := pinnedSecondRow oracle.permutation index (checkerNonce (staged s)) a.2 message
    (rawLeaf oracle ordinal index s).2=[.permutation a.1 a.2,.permutation b.1 b.2] ∧
      readBuffer (rawLeaf oracle ordinal index s).1 12288 32 = outputDigest b.2 := by
  simp only [rawLeaf,checker_leaf_rows]
  exact ⟨True.intro,checker_leaf_digest _ _ _ _⟩

theorem raw_view (oracle : Oracle) (input : CheckInput) (ordinal : Nat) (h : ordinal < input.positions.card)
    (s : MachineState) (fits : ProofWithin input) (cursor : RecordCursor input ordinal s)
    (framed : RecordInputFrame input ordinal s) :
    let raw := (rawLeaf oracle ordinal (honestIndex input.positions ordinal h).val s).1
    raw.pc=0x10e8 ∧ raw.getReg .x6=BitVec.ofNat 64 (honestIndex input.positions ordinal h).val.val ∧
      (∀ reg : Reg, reg≠.x6 → reg≠.x28 → reg≠.x10 → reg≠.x11 → reg≠.x13 → reg≠.x12 → reg≠.x31 →
        raw.getReg reg=s.getReg reg) ∧
      (∀ word < 2^33, (word<checkSourceWord ordinal ∨ checkSourceWord ordinal+26≤word) →
        (word<1534 ∨ 1576≤word) → memoryView raw word=memoryView s word) := by
  dsimp only [rawLeaf]
  rw [checker_leaf_rows]
  dsimp only
  have ready := leaf_ready input ordinal h s fits cursor framed
  refine ⟨checker_leaf_finished_pc ready _ _,?_,?_,?_⟩
  · exact (checker_leaf_preserved_register _ _ _ _ .x6 (by decide) (by decide) (by decide)).trans
      ((staged_reg s .x6 (by decide)).trans ((record_setup_post s).1.trans (loaded_index input ordinal h s cursor framed)))
  · intro reg h6 h28 h10 h11 h13 h12 h31
    exact (checker_leaf_preserved_register _ _ _ _ reg h10 h12 h31).trans
      (staged_saved s reg h6 h28 h10 h11 h13 h31)
  · intro word bound src scratch
    rw [checker_leaf_frame ready _ _ word bound src (by omega)]
    exact staged_word_frame input ordinal h s fits cursor word bound (by omega)

theorem raw_quartet_entry (oracle : Oracle) (input : CheckInput) (ordinal : Nat) (h : ordinal < input.positions.card)
    (s : MachineState) (fits : ProofWithin input) (cursor : RecordCursor input ordinal s)
    (framed : RecordInputFrame input ordinal s) :
    QuartetEntry ordinal (honestIndex input.positions ordinal h).val
      (rawLeaf oracle ordinal (honestIndex input.positions ordinal h).val s).1 := by
  obtain ⟨pc,position,kept,wordFrame⟩ := raw_view oracle input ordinal h s fits cursor framed
  have card := checker_positions_bound input
  have room := (packed_record_geometry input ordinal h fits).2.2.2.1
  have r := record_setup_post s
  have leafKeeps (reg : Reg) (a : reg ≠ .x10) (b : reg ≠ .x12) (c : reg ≠ .x31) :
      (rawLeaf oracle ordinal (honestIndex input.positions ordinal h).val s).1.getReg reg = (staged s).getReg reg := by
    simp only [rawLeaf,checker_leaf_rows]
    exact checker_leaf_preserved_register _ _ _ _ reg a b c
  refine ⟨pc,position,?_,?_,?_,?_,?_,?_,?_,?_,room⟩
  · exact (kept .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans cursor.proof
  · exact (kept .x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      cursor.challengeLength
  · exact (kept .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans cursor.digest
  · exact (kept .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans cursor.pair
  · exact (kept .x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans cursor.selector
  · exact (leafKeeps .x11 (by decide) (by decide) (by decide)).trans ((staged_reg s .x11 (by decide)).trans r.2.2.2.1)
  · exact (leafKeeps .x13 (by decide) (by decide) (by decide)).trans ((staged_reg s .x13 (by decide)).trans r.2.2.2.2.1)
  · intro w lo hi
    rw [wordFrame w (by omega) (Or.inl (by unfold checkSourceWord; omega)) (Or.inr (by omega)),
      framed w (by omega) (Or.inl (Or.inr ⟨lo, hi⟩))]
    exact Checker.check_scratch_word_zero input (8*w) (by omega)

end TwoPermutationPrototype.Packed.RecordLeaf
