-- Pair-heads copy of TwoPermutationPackedRecordLeafBlock (stack/check/work/mkcopy.py); edits below are marked PAIR.
import CommitGolfCandidate.PairCheckRecordLeafPrelude
import CommitGolfCandidate.PairCheckNamespaces
import CommitGolfCandidate.PairCheckRecordLeafCalls
import CommitGolfCandidate.PairCheckRecordLeafEvenSpec
import CommitGolfCandidate.PairCheckRecordComposition
import CommitGolfCandidate.PairCheckQBlock

namespace TwoPermutationPrototype.PairCk.Packed.RecordLeaf
open  TwoPermutationPrototype.Packed
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling TwoPermutationPrototype.Packed.Checker TwoPermutationPrototype.PairCk.Packed.Checker
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

@[local simp] private theorem block_mem_set_reg (s : MachineState) (r : Reg) (v : Word) :
    (s.setReg r v).mem = s.mem := by cases r <;> rfl

@[local simp] private theorem block_mem_set_pc (s : MachineState) (v : Word) :
    (s.setPC v).mem = s.mem := rfl

/-! ### PAIR: the leaf entry after the parity branch -/

/-- The state after record setup, nonce staging and the parity branch (words 22–45). -/
abbrev entry (s : MachineState) : MachineState := branched (staged s)

theorem entry_reg (s : MachineState) (r : Reg) (h31 : r ≠ .x31) : (entry s).getReg r = (staged s).getReg r :=
  branched_register _ r h31

theorem entry_memory (s : MachineState) : memoryView (entry s) = memoryView (staged s) := by
  funext w
  simp only [memoryView, MachineState.getMem, branched_mem]

theorem entry_nonce (s : MachineState) : checkerNonce (entry s) = checkerNonce (staged s) := by
  funext i
  simp only [checkerNonce, entry_reg s .x4 (by decide), MachineState.getMem, branched_mem]

/-- Registers shared by both leaf paths. -/
structure EntryRegs (state : MachineState) (src nonce : Nat) (index : Index) : Prop where
  source : state.getReg .x10 = wordAddress src
  proofPointer : state.getReg .x4 = wordAddress nonce
  destination : state.getReg .x23 = wordAddress 1536
  tag : state.getReg .x28 = firstTag index.val
  selector : state.getReg .x5 = 0
  size : state.getReg .x11 = 200
  primitive : state.getReg .x13 = 1

theorem staged_regs (input : CheckInput) (ordinal : Nat) (h : ordinal < input.positions.card)
    (s : MachineState) (cursor : RecordCursor input ordinal s) (framed : RecordInputFrame input ordinal s) :
    EntryRegs (staged s) (checkSourceWord ordinal) 1534 (honestIndex input.positions ordinal h).val := by
  have r := record_setup_post s
  refine ⟨(staged_reg s .x10 (by decide)).trans (r.2.2.1.trans cursor.value),
    (staged_scratch s).trans cursor.nonceScratch,
    (staged_saved s .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans cursor.digest,?_,
    (staged_saved s .x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans cursor.selector,
    (staged_reg s .x11 (by decide)).trans r.2.2.2.1,(staged_reg s .x13 (by decide)).trans r.2.2.2.2.1⟩
  rw [staged_reg _ _ (by decide),r.2.1,cursor.tag,loaded_index input ordinal h s cursor framed,addr_shift,firstTag]
  change BitVec.ofNat 64 4056+BitVec.ofNat 64 _=_
  rw [←BitVec.ofNat_add]

theorem entry_regs (input : CheckInput) (ordinal : Nat) (h : ordinal < input.positions.card)
    (s : MachineState) (cursor : RecordCursor input ordinal s) (framed : RecordInputFrame input ordinal s) :
    EntryRegs (entry s) (checkSourceWord ordinal) 1534 (honestIndex input.positions ordinal h).val := by
  have e := staged_regs input ordinal h s cursor framed
  exact ⟨(entry_reg s _ (by decide)).trans e.source,(entry_reg s _ (by decide)).trans e.proofPointer,
    (entry_reg s _ (by decide)).trans e.destination,(entry_reg s _ (by decide)).trans e.tag,
    (entry_reg s _ (by decide)).trans e.selector,(entry_reg s _ (by decide)).trans e.size,
    (entry_reg s _ (by decide)).trans e.primitive⟩

theorem staged_node (input : CheckInput) (ordinal : Nat) (h : ordinal < input.positions.card)
    (s : MachineState) (cursor : RecordCursor input ordinal s) (framed : RecordInputFrame input ordinal s) :
    (staged s).getReg .x6 = BitVec.ofNat 64 (honestIndex input.positions ordinal h).val.val :=
  (staged_reg s .x6 (by decide)).trans ((record_setup_post s).1.trans (loaded_index input ordinal h s cursor framed))

theorem entry_pc (input : CheckInput) (ordinal : Nat) (h : ordinal < input.positions.card)
    (s : MachineState) (fits : ProofWithin input) (cursor : RecordCursor input ordinal s)
    (framed : RecordInputFrame input ordinal s) :
    (entry s).pc = if (honestIndex input.positions ordinal h).val.val % 2 = 0
      then BitVec.ofNat 64 (4096+4*494) else 0x10b8 :=
  branched_pc (staged s) (copy_field_pc _ _ _ _ (stage_ready input ordinal h s fits cursor)) _
    (staged_node input ordinal h s cursor framed)

theorem leaf_ready (input : CheckInput) (ordinal : Nat) (h : ordinal < input.positions.card)
    (s : MachineState) (fits : ProofWithin input) (cursor : RecordCursor input ordinal s)
    (framed : RecordInputFrame input ordinal s) (odd : (honestIndex input.positions ordinal h).val.val % 2 = 1) :
    LeafReady (entry s) (checkSourceWord ordinal) 1534 (honestIndex input.positions ordinal h).val := by
  have e := entry_regs input ordinal h s cursor framed
  have card := checker_positions_bound input
  refine ⟨?_,e.source,e.proofPointer,e.destination,e.tag,e.selector,e.size,e.primitive,?_,?_⟩
  · rw [entry_pc input ordinal h s fits cursor framed, if_neg (by omega)]
  all_goals unfold checkSourceWord; omega

theorem even_ready (input : CheckInput) (ordinal : Nat) (h : ordinal < input.positions.card)
    (s : MachineState) (fits : ProofWithin input) (cursor : RecordCursor input ordinal s)
    (framed : RecordInputFrame input ordinal s) (isEven : (honestIndex input.positions ordinal h).val.val % 2 = 0) :
    EvenReady (entry s) (checkSourceWord ordinal) 1534 (honestIndex input.positions ordinal h).val := by
  have e := entry_regs input ordinal h s cursor framed
  have card := checker_positions_bound input
  refine ⟨?_,e.source,e.proofPointer,e.destination,e.tag,e.selector,e.size,e.primitive,by decide,?_,?_⟩
  · rw [entry_pc input ordinal h s fits cursor framed, if_pos isEven]
  all_goals unfold checkSourceWord; omega

/-! ### PAIR: both leaf paths behind one interface -/

def pairQueries (state : MachineState) (src : Nat) (index : Index) : OracleComp World MachineState :=
  if index.val % 2 = 0 then evenQueries state src index else leafQueries state src index

def pairFinal (state : MachineState) (src : Nat) (index : Index) (a b : Block) : MachineState :=
  if index.val % 2 = 0 then evenFinal state a b else secondReplyState state src a b

theorem even_leaf_rows (oracle : Oracle) (state : MachineState) (src : Nat) (index : Index) :
    let message := window (memoryView state) (src+5)
    let nonce := checkerNonce state
    let a := evenFirstRow oracle.permutation message
    let b := evenSecondRow oracle.permutation index nonce a.2 message
    checkEvaluation oracle (recordRows (evenQueries state src index)) =
      ((evenFinal state a.2 b.2,[.permutation a.1 a.2,.permutation b.1 b.2]),2) := by
  simp only [evenQueries,evenFirstRow,evenSecondRow,record_rows_query,check_evaluation_public_bind,
    check_evaluation_map,record_rows_pure,check_evaluation_pure]
  rfl

theorem pair_leaf_rows (oracle : Oracle) (state : MachineState) (src : Nat) (index : Index) :
    let message := window (memoryView state) (src+5)
    let nonce := checkerNonce state
    let a := pairFirstRow oracle.permutation index message
    let b := pairSecondRow oracle.permutation index nonce a.2 message
    checkEvaluation oracle (recordRows (pairQueries state src index)) =
      ((pairFinal state src index a.2 b.2,[.permutation a.1 a.2,.permutation b.1 b.2]),2) := by
  by_cases isEven : index.val % 2 = 0
  · simp only [pairQueries, pairFinal, pairFirstRow, pairSecondRow, if_pos isEven]
    exact even_leaf_rows oracle state src index
  · simp only [pairQueries, pairFinal, pairFirstRow, pairSecondRow, if_neg isEven]
    exact checker_leaf_rows oracle state src index

theorem jal_mem (t : MachineState) (imm : BitVec 21) : (execInstrBr t (.JAL .x0 imm)).mem = t.mem := rfl

theorem even_jump_mem (t : MachineState) : (execInstrBr t evenJump).mem = t.mem := jal_mem t _

theorem pair_leaf_digest (state : MachineState) (src : Nat) (index : Index) (a b : Block) :
    readBuffer (pairFinal state src index a b) 12288 32 = outputDigest b := by
  unfold pairFinal
  split
  · have mem : (evenFinal state a b).mem = (writeBits (evenMiddle (evenFirstState state a)) (wordAddress 1536) b).mem :=
      even_jump_mem _
    rw [read_buffer_memory_congr _ _ mem]
    simpa only [wordAddress,Nat.add_zero,Nat.mul_zero,outputDigest] using
      write_bits_digest (evenMiddle (evenFirstState state a)) 12288 0 b (by decide) (by decide)
  · exact checker_leaf_digest state src a b

theorem pair_final_register (even : EvenPathFacts) (state : MachineState) (src : Nat) (index : Index) (a b : Block)
    (reg : Reg) (h10 : reg ≠ .x10) (h12 : reg ≠ .x12) (h30 : reg ≠ .x30) (h31 : reg ≠ .x31) :
    (pairFinal state src index a b).getReg reg = state.getReg reg := by
  unfold pairFinal
  split
  · exact even.register state a b reg h10 h12 h30 h31
  · exact checker_leaf_preserved_register state src a b reg h10 h12 h31

def rawLeaf (oracle : Oracle) (ordinal : Nat) (index : Index) (s : MachineState) : MachineState × List PublicRow :=
  (checkEvaluation oracle (recordRows (pairQueries (entry s) (checkSourceWord ordinal) index))).1

/-- PAIR: steps from the parity branch (word 44) to the quartet block: 2 + (49 even | 12 odd). -/
def leafRunSteps (index : Index) : Nat := if index.val % 2 = 0 then 51 else 14
/-- PAIR: cycles of the same stretch: 2 + (63 even | 26 odd). -/
def leafRunCycles (index : Index) : Nat := if index.val % 2 = 0 then 65 else 28
/-- PAIR: leaf steps from word 22: record setup (6) and nonce staging (16), then the run. -/
def leafSteps (index : Index) : Nat := 22 + leafRunSteps index
def leafCycles (index : Index) : Nat := 22 + leafRunCycles index

/-- The leaf (record setup, nonce, parity branch, two permutation calls) followed by the quartet block. -/
def block (oracle : Oracle) (ordinal : Nat) (index : Index) (s : MachineState) : RecordBlock :=
  let raw := rawLeaf oracle ordinal index s
  let q := quartetBlock oracle raw.1
  ⟨q.state,leafSteps index+132,leafCycles index+139,raw.2++q.rows⟩

theorem raw_digest_rows (oracle : Oracle) (ordinal : Nat) (index : Index) (s : MachineState) :
    let message := window (memoryView (entry s)) (checkSourceWord ordinal+5)
    let a := pairFirstRow oracle.permutation index message
    let b := pairSecondRow oracle.permutation index (checkerNonce (entry s)) a.2 message
    (rawLeaf oracle ordinal index s).2=[.permutation a.1 a.2,.permutation b.1 b.2] ∧
      readBuffer (rawLeaf oracle ordinal index s).1 12288 32 = outputDigest b.2 := by
  simp only [rawLeaf,pair_leaf_rows]
  exact ⟨True.intro,pair_leaf_digest _ _ _ _ _⟩

theorem raw_view (even : EvenPathFacts) (oracle : Oracle) (input : CheckInput) (ordinal : Nat)
    (h : ordinal < input.positions.card)
    (s : MachineState) (fits : ProofWithin input) (cursor : RecordCursor input ordinal s)
    (framed : RecordInputFrame input ordinal s) :
    let raw := (rawLeaf oracle ordinal (honestIndex input.positions ordinal h).val s).1
    raw.pc=0x10e8 ∧ raw.getReg .x6=BitVec.ofNat 64 (honestIndex input.positions ordinal h).val.val ∧
      (∀ reg : Reg, reg≠.x6 → reg≠.x28 → reg≠.x10 → reg≠.x11 → reg≠.x13 → reg≠.x12 → reg≠.x31 → reg≠.x30 →
        raw.getReg reg=s.getReg reg) ∧
      (∀ word < 2^33, (word<checkSourceWord ordinal ∨ checkSourceWord ordinal+26≤word) →
        (word<1534 ∨ 1576≤word) → (word < 131053 ∨ 131097 ≤ word) → memoryView raw word=memoryView s word) := by
  dsimp only [rawLeaf]
  rw [pair_leaf_rows]
  dsimp only
  let item := (honestIndex input.positions ordinal h).val
  refine ⟨?_,?_,?_,?_⟩
  · unfold pairFinal
    split
    · next isEven => exact even.pc (even_ready input ordinal h s fits cursor framed isEven) _ _
    · next isOdd => exact checker_leaf_finished_pc (leaf_ready input ordinal h s fits cursor framed (by omega)) _ _
  · exact (pair_final_register even _ _ _ _ _ .x6 (by decide) (by decide) (by decide) (by decide)).trans
      ((entry_reg s .x6 (by decide)).trans (staged_node input ordinal h s cursor framed))
  · intro reg h6 h28 h10 h11 h13 h12 h31 h30
    exact (pair_final_register even _ _ _ _ _ reg h10 h12 h30 h31).trans
      ((entry_reg s reg h31).trans (staged_saved s reg h6 h28 h10 h11 h13 h31))
  · intro word bound src scratch window
    have stagedWord := staged_word_frame input ordinal h s fits cursor word bound (by omega)
    rw [← congrFun (entry_memory s) word] at stagedWord
    refine Eq.trans ?_ stagedWord
    unfold pairFinal
    split
    · next isEven =>
      exact even.frame (even_ready input ordinal h s fits cursor framed isEven) _ _ word bound (by omega) window
    · next isOdd =>
      exact checker_leaf_frame (leaf_ready input ordinal h s fits cursor framed (by omega)) _ _ word bound src (by omega)

theorem raw_quartet_entry (even : EvenPathFacts) (oracle : Oracle) (input : CheckInput) (ordinal : Nat)
    (h : ordinal < input.positions.card)
    (s : MachineState) (fits : ProofWithin input) (cursor : RecordCursor input ordinal s)
    (framed : RecordInputFrame input ordinal s) :
    QuartetEntry ordinal (honestIndex input.positions ordinal h).val
      (rawLeaf oracle ordinal (honestIndex input.positions ordinal h).val s).1 := by
  obtain ⟨pc,position,kept,wordFrame⟩ := raw_view even oracle input ordinal h s fits cursor framed
  have card := checker_positions_bound input
  have room := (packed_record_geometry input ordinal h fits).2.2.2.1
  have r := record_setup_post s
  have leafKeeps (reg : Reg) (a : reg ≠ .x10) (b : reg ≠ .x12) (c : reg ≠ .x31) (d : reg ≠ .x30) :
      (rawLeaf oracle ordinal (honestIndex input.positions ordinal h).val s).1.getReg reg = (staged s).getReg reg := by
    simp only [rawLeaf,pair_leaf_rows]
    exact (pair_final_register even _ _ _ _ _ reg a b d c).trans (entry_reg s reg c)
  refine ⟨pc,position,?_,?_,?_,?_,?_,?_,?_,?_,room⟩
  · exact (kept .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans cursor.proof
  · exact (kept .x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      cursor.challengeLength
  · exact (kept .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans cursor.digest
  · exact (kept .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans cursor.pair
  · exact (kept .x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans cursor.selector
  · exact (leafKeeps .x11 (by decide) (by decide) (by decide) (by decide)).trans ((staged_reg s .x11 (by decide)).trans r.2.2.2.1)
  · exact (leafKeeps .x13 (by decide) (by decide) (by decide) (by decide)).trans ((staged_reg s .x13 (by decide)).trans r.2.2.2.2.1)
  · intro w lo hi
    rw [wordFrame w (by omega) (Or.inl (by unfold checkSourceWord; omega)) (Or.inr (by omega)) (Or.inl (by omega)),
      framed w (by omega) (Or.inl (Or.inr ⟨lo, hi⟩))]
    exact Checker.check_scratch_word_zero input (8*w) (by omega)

end TwoPermutationPrototype.PairCk.Packed.RecordLeaf
