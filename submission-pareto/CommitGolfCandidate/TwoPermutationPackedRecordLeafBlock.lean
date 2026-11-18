import CommitGolfCandidate.TwoPermutationPackedRecordLeafPrelude
import CommitGolfCandidate.TwoPermutationPackedRecordLeafCalls
import CommitGolfCandidate.TwoPermutationPackedRecordComposition
import CommitGolfCandidate.QuartetCheckBlock
import CommitGolfCandidate.K1CheckARun

/-! # The K1 leaf of a record: dispatcher, salt-first or A leaf, as states and rows

`rawLeaf` is the state at the quartet block's entry (word 58, or words 565–566 moved to word 58)
with the two permutation rows of the leaf. Both leaf kinds share its interface: the rows are the
pinned first and second rows of the opened value with the salt words `rawNonce`, the digest at 12288
is the second reply's, registers outside the leaf's scratch registers and memory outside the
value record, the salt scratch, the A scratch `[9216, 9560)` and the reply are kept. -/
namespace TwoPermutationPrototype.Packed.RecordLeaf
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling TwoPermutationPrototype.Packed.Checker
open TwoPermutationPrototype.Checker (beginRecord beginLower record_setup_post record_setup_register
  lower_setup_post lower_setup_register lower_setup_mem checkIndexWord checkSourceWord checker_positions_bound
  RecordInputFrame honestIndex record_input_index record_input_value checker_value_data check_recorded_bind
  check_recorded_map)
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

/-! ### The dispatcher on a record -/

section
variable (input : CheckInput) (ordinal : Nat) (h : ordinal < input.positions.card) (s : MachineState)

include h in
theorem record_entry_pc (cursor : RecordCursor input ordinal s) : s.pc = 0x1058 :=
  cursor.pc.trans (ite_eq_right (by omega))

include h in
theorem record_index_access (cursor : RecordCursor input ordinal s) : accessValid (s.getReg .x8) 8 = true := by
  have card := checker_positions_bound input
  rw [cursor.index]; apply aligned_access; unfold checkIndexWord; omega

theorem record_rank (cursor : RecordCursor input ordinal s) (framed : RecordInputFrame input ordinal s) :
    (dispatched s).getReg .x7 = BitVec.ofNat 64 (machineRank (honestIndex input.positions ordinal h).val.val) :=
  dispatched_rank s _ (honestIndex input.positions ordinal h).val.isLt (loaded_index input ordinal h s cursor framed)
    (by rw [cursor.marks]; rfl)

theorem sf_rank (cursor : RecordCursor input ordinal s) (framed : RecordInputFrame input ordinal s)
    (sf : isAHead (honestIndex input.positions ordinal h).val = false) : (dispatched s).getReg .x7 ≠ 0 := by
  rw [record_rank input ordinal h s cursor framed]
  intro zero
  have small : machineRank (honestIndex input.positions ordinal h).val.val < 11 := by
    unfold machineRank; omega
  have value := congrArg BitVec.toNat zero
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at value
  have ahead := (machine_rank_ahead _).mp value
  rw [sf] at ahead
  exact Bool.false_ne_true ahead

theorem a_rank (cursor : RecordCursor input ordinal s) (framed : RecordInputFrame input ordinal s)
    (ahead : isAHead (honestIndex input.positions ordinal h).val = true) : (dispatched s).getReg .x7 = 0 := by
  rw [record_rank input ordinal h s cursor framed, (machine_rank_ahead _).mpr ahead]; rfl

theorem sf_cursor (cursor : RecordCursor input ordinal s) : RecordCursor input ordinal (sfPre s) := by
  have keep (r : Reg) (h7 : r ≠ .x7) (h29 : r ≠ .x29) (h6 : r ≠ .x6) : (sfPre s).getReg r = s.getReg r :=
    sf_pre_register s r h7 h29 h6
  exact ⟨(sf_pre_pc s).trans cursor.pc,
    (keep .x8 (by decide) (by decide) (by decide)).trans cursor.index,
    (keep .x19 (by decide) (by decide) (by decide)).trans cursor.value,
    (keep .x21 (by decide) (by decide) (by decide)).trans cursor.proof,
    (keep .x18 (by decide) (by decide) (by decide)).trans cursor.remaining,
    (keep .x3 (by decide) (by decide) (by decide)).trans cursor.tag,
    (keep .x9 (by decide) (by decide) (by decide)).trans cursor.commitment,
    (keep .x20 (by decide) (by decide) (by decide)).trans cursor.challengeLength,
    (keep .x22 (by decide) (by decide) (by decide)).trans cursor.proofEnd,
    (keep .x23 (by decide) (by decide) (by decide)).trans cursor.digest,
    (keep .x24 (by decide) (by decide) (by decide)).trans cursor.pair,
    (keep .x25 (by decide) (by decide) (by decide)).trans cursor.capRoots,
    (keep .x26 (by decide) (by decide) (by decide)).trans cursor.marks,
    (keep .x27 (by decide) (by decide) (by decide)).trans cursor.capCount,
    (keep .x5 (by decide) (by decide) (by decide)).trans cursor.selector,
    (keep .x4 (by decide) (by decide) (by decide)).trans cursor.nonceScratch⟩

theorem sf_framed (framed : RecordInputFrame input ordinal s) : RecordInputFrame input ordinal (sfPre s) := by
  intro w bounded used
  exact (congrFun (sf_pre_mem s) (wordAddress w)).trans (framed w bounded used)

end

theorem leaf_ready (input : CheckInput) (ordinal : Nat) (h : ordinal < input.positions.card)
    (s : MachineState) (fits : ProofWithin input) (cursor : RecordCursor input ordinal s)
    (framed : RecordInputFrame input ordinal s) (sf : isAHead (honestIndex input.positions ordinal h).val = false) :
    LeafReady (staged s) (checkSourceWord ordinal) 1534 (honestIndex input.positions ordinal h).val := by
  have r := record_setup_post s
  have card := checker_positions_bound input
  have c := stage_ready input ordinal h s fits cursor
  refine ⟨copy_field_pc _ _ _ _ c,(staged_reg s .x10 (by decide)).trans (r.2.2.1.trans cursor.value),
    (staged_scratch s).trans cursor.nonceScratch,
    (staged_saved s .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans cursor.digest,?_,
    (staged_saved s .x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans cursor.selector,
    (staged_reg s .x11 (by decide)).trans r.2.2.2.1,(staged_reg s .x13 (by decide)).trans r.2.2.2.2.1,?_,?_,sf⟩
  · rw [staged_reg _ _ (by decide),r.2.1,cursor.tag,loaded_index input ordinal h s cursor framed,addr_shift,firstTag]
    change BitVec.ofNat 64 4056+BitVec.ofNat 64 _=_
    rw [←BitVec.ofNat_add]
  all_goals unfold checkSourceWord; omega

theorem a_ready (input : CheckInput) (ordinal : Nat) (h : ordinal < input.positions.card)
    (s : MachineState) (fits : ProofWithin input) (cursor : RecordCursor input ordinal s)
    (framed : RecordInputFrame input ordinal s) (ahead : isAHead (honestIndex input.positions ordinal h).val = true) :
    AReady (aEntry s) (checkSourceWord ordinal) (checkProofByte ordinal) (honestIndex input.positions ordinal h).val := by
  have card := checker_positions_bound input
  obtain ⟨aligned, _, low, room, _⟩ := packed_record_geometry input ordinal h fits
  obtain ⟨epc, _, ex6, kept⟩ := a_entry_post s (record_entry_pc input ordinal h s cursor)
    (a_rank input ordinal h s cursor framed ahead)
  have keep (r : Reg) (h6 : r ≠ .x6) (h7 : r ≠ .x7) (h29 : r ≠ .x29) : (aEntry s).getReg r = s.getReg r :=
    kept r h6 h7 h29
  refine ⟨epc, (keep .x19 (by decide) (by decide) (by decide)).trans cursor.value,
    (keep .x21 (by decide) (by decide) (by decide)).trans cursor.proof,
    (keep .x4 (by decide) (by decide) (by decide)).trans cursor.nonceScratch,
    (keep .x23 (by decide) (by decide) (by decide)).trans cursor.digest,
    (keep .x5 (by decide) (by decide) (by decide)).trans cursor.selector,
    (keep .x3 (by decide) (by decide) (by decide)).trans cursor.tag,
    ex6.trans (loaded_index input ordinal h s cursor framed), ahead, ?_, ?_, by omega, by omega, aligned⟩
  all_goals unfold checkSourceWord; omega

/-! ### The leaf as states and rows -/

/-- The A leaf's oracle queries from word 500, ending at the state moved to word 58. -/
def aLeafQueries (e : MachineState) (src : Nat) (index : Index) : OracleComp World MachineState := do
  let message := window (memoryView e) (src+5)
  let first ← World.query (.inr (.inr (.inl (packBuffer (pinnedFirstInput index message)))))
  let second ← World.query (.inr (.inr (.inl (packBuffer
    (pinnedSecondInput index (checkerNonce (aStaged e)) (replyWords first) message)))))
  return (aSecondReply e first second).setPC 0x10e8

theorem a_leaf_rows (oracle : Oracle) (e : MachineState) (src : Nat) (index : Index) :
    let message := window (memoryView e) (src+5)
    let a := pinnedFirstRow oracle.permutation index message
    let b := pinnedSecondRow oracle.permutation index (checkerNonce (aStaged e)) a.2 message
    checkEvaluation oracle (recordRows (aLeafQueries e src index)) =
      (((aSecondReply e a.2 b.2).setPC 0x10e8,[.permutation a.1 a.2,.permutation b.1 b.2]),2) := by
  simp only [aLeafQueries,pinnedFirstRow,pinnedSecondRow,record_rows_query,check_evaluation_public_bind,
    check_evaluation_map,record_rows_pure,check_evaluation_pure]
  rfl

attribute [local irreducible] execute in
theorem execute_a_queries {e : MachineState} {src proof : Nat} {index : Index} (ready : AReady e src proof index)
    (fuel : Nat) :
    execute packedImage (65+(2+fuel)) e false = (do
      let t ← aLeafQueries e src index
      let r ← execute packedImage (2+fuel) t false
      return r.charge 79 2) := by
  have enter (a b : Block) : execute packedImage (2+fuel) (aSecondReply e a b) false =
      execute packedImage (2+fuel) ((aSecondReply e a b).setPC 0x10e8) false :=
    execute_a_enter _ (a_second_pc ready a b) fuel
  rw [execute_a_leaf ready (2+fuel)]
  simp only [enter, aLeafQueries, bind_assoc, pure_bind]

def rawLeaf (oracle : Oracle) (ordinal : Nat) (index : Index) (s : MachineState) : MachineState × List PublicRow :=
  if isAHead index then (checkEvaluation oracle (recordRows (aLeafQueries (aEntry s) (checkSourceWord ordinal) index))).1
  else (checkEvaluation oracle (recordRows (leafQueries (staged (sfPre s)) (checkSourceWord ordinal) index))).1

/-- The value words the leaf hashes, as the machine reads them. -/
def rawMessage (ordinal : Nat) (index : Index) (s : MachineState) : Words 32 :=
  if isAHead index then window (memoryView (aEntry s)) (checkSourceWord ordinal+5)
  else window (memoryView (staged (sfPre s))) (checkSourceWord ordinal+5)

/-- The salt words of the leaf's second window. -/
def rawNonce (index : Index) (s : MachineState) : Words 2 :=
  if isAHead index then checkerNonce (aStaged (aEntry s)) else checkerNonce (staged (sfPre s))

theorem raw_leaf_a (oracle : Oracle) (ordinal : Nat) (index : Index) (s : MachineState)
    (ahead : isAHead index = true) :
    rawLeaf oracle ordinal index s =
      (((aSecondReply (aEntry s)
          (pinnedFirstRow oracle.permutation index (window (memoryView (aEntry s)) (checkSourceWord ordinal+5))).2
          (pinnedSecondRow oracle.permutation index (checkerNonce (aStaged (aEntry s)))
            (pinnedFirstRow oracle.permutation index (window (memoryView (aEntry s)) (checkSourceWord ordinal+5))).2
            (window (memoryView (aEntry s)) (checkSourceWord ordinal+5))).2).setPC 0x10e8,
        [.permutation
          (pinnedFirstRow oracle.permutation index (window (memoryView (aEntry s)) (checkSourceWord ordinal+5))).1
          (pinnedFirstRow oracle.permutation index (window (memoryView (aEntry s)) (checkSourceWord ordinal+5))).2,
         .permutation
          (pinnedSecondRow oracle.permutation index (checkerNonce (aStaged (aEntry s)))
            (pinnedFirstRow oracle.permutation index (window (memoryView (aEntry s)) (checkSourceWord ordinal+5))).2
            (window (memoryView (aEntry s)) (checkSourceWord ordinal+5))).1
          (pinnedSecondRow oracle.permutation index (checkerNonce (aStaged (aEntry s)))
            (pinnedFirstRow oracle.permutation index (window (memoryView (aEntry s)) (checkSourceWord ordinal+5))).2
            (window (memoryView (aEntry s)) (checkSourceWord ordinal+5))).2])) := by
  unfold rawLeaf
  rw [if_pos ahead, a_leaf_rows]

theorem raw_leaf_sf (oracle : Oracle) (ordinal : Nat) (index : Index) (s : MachineState)
    (sf : isAHead index = false) :
    rawLeaf oracle ordinal index s =
      (checkEvaluation oracle (recordRows (leafQueries (staged (sfPre s)) (checkSourceWord ordinal) index))).1 := by
  unfold rawLeaf
  rw [if_neg (by simp [sf])]

def leafSteps (index : Index) : Nat := if isAHead index then 71 else 42
def leafCycles (index : Index) : Nat := if isAHead index then 91 else 62

/-- The leaf (dispatcher, salt, two permutation calls) followed by the quartet block. -/
def block (oracle : Oracle) (ordinal : Nat) (index : Index) (s : MachineState) : RecordBlock :=
  let raw := rawLeaf oracle ordinal index s
  let q := quartetBlock oracle raw.1
  ⟨q.state,leafSteps index+q.steps,leafCycles index+q.cycles,raw.2++q.rows⟩

theorem leaf_steps_le (index : Index) : leafSteps index ≤ 71 := by
  unfold leafSteps; split <;> omega

theorem read_buffer_set_pc (t : MachineState) (p : Word) (address count : Nat) :
    readBuffer (t.setPC p) address count = readBuffer t address count := read_buffer_memory_congr _ _ rfl _ _

theorem memory_view_set_pc (t : MachineState) (p : Word) (w : Nat) :
    memoryView (t.setPC p) w = memoryView t w := rfl

theorem raw_digest_rows (oracle : Oracle) (ordinal : Nat) (index : Index) (s : MachineState) :
    let message := rawMessage ordinal index s
    let a := pinnedFirstRow oracle.permutation index message
    let b := pinnedSecondRow oracle.permutation index (rawNonce index s) a.2 message
    (rawLeaf oracle ordinal index s).2=[.permutation a.1 a.2,.permutation b.1 b.2] ∧
      readBuffer (rawLeaf oracle ordinal index s).1 12288 32 = outputDigest b.2 := by
  by_cases ahead : isAHead index = true
  · rw [raw_leaf_a oracle ordinal index s ahead,
      show rawMessage ordinal index s = window (memoryView (aEntry s)) (checkSourceWord ordinal+5) from if_pos ahead,
      show rawNonce index s = checkerNonce (aStaged (aEntry s)) from if_pos ahead]
    refine ⟨rfl, ?_⟩
    rw [read_buffer_set_pc, a_second_digest]
  · have sf : isAHead index = false := by simpa using ahead
    rw [raw_leaf_sf oracle ordinal index s sf, checker_leaf_rows,
      show rawMessage ordinal index s = window (memoryView (staged (sfPre s))) (checkSourceWord ordinal+5)
        from if_neg ahead,
      show rawNonce index s = checkerNonce (staged (sfPre s)) from if_neg ahead]
    exact ⟨rfl, checker_leaf_digest _ _ _ _⟩

/-- Registers a leaf may change: the index, the rank and its modulus, the tag, the call registers
and the temporary. -/
def LeafKept (reg : Reg) : Prop :=
  reg≠.x6 ∧ reg≠.x7 ∧ reg≠.x29 ∧ reg≠.x28 ∧ reg≠.x10 ∧ reg≠.x11 ∧ reg≠.x13 ∧ reg≠.x12 ∧ reg≠.x31

instance (reg : Reg) : Decidable (LeafKept reg) := by unfold LeafKept; infer_instance

attribute [local irreducible] execute checkEvaluation

theorem a_raw_view (input : CheckInput) (ordinal : Nat) (h : ordinal < input.positions.card)
    (s : MachineState) (fits : ProofWithin input) (cursor : RecordCursor input ordinal s)
    (framed : RecordInputFrame input ordinal s) (ahead : isAHead (honestIndex input.positions ordinal h).val = true)
    (a b : Block) :
    let raw := (aSecondReply (aEntry s) a b).setPC 0x10e8
    raw.pc=0x10e8 ∧ raw.getReg .x6=BitVec.ofNat 64 (honestIndex input.positions ordinal h).val.val ∧
      (∀ reg : Reg, LeafKept reg → raw.getReg reg=s.getReg reg) ∧
      (∀ word < 2^33, (word<checkSourceWord ordinal ∨ checkSourceWord ordinal+26≤word) →
        (word<1152 ∨ 1576≤word) → memoryView raw word=memoryView s word) ∧
      raw.getReg .x11 = 200 ∧ raw.getReg .x13 = 1 := by
  have ready := a_ready input ordinal h s fits cursor framed ahead
  obtain ⟨_, emem, ex6, ekept⟩ := a_entry_post s (record_entry_pc input ordinal h s cursor)
    (a_rank input ordinal h s cursor framed ahead)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [MachineState.getReg_setPC, a_second_register _ _ .x6 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), ex6]
    exact loaded_index input ordinal h s cursor framed
  · intro reg ⟨h6, h7, h29, h28, h10, h11, h13, h12, h31⟩
    rw [MachineState.getReg_setPC, a_second_register _ _ reg h28 h10 h11 h13 h31 h12]
    exact ekept reg h6 h7 h29
  · intro word bound _ scratch
    rw [memory_view_set_pc, a_second_frame ready a b word bound (by omega)]
    exact congrFun emem (wordAddress word)
  · rw [MachineState.getReg_setPC]; exact a_second_x11 ready a b
  · rw [MachineState.getReg_setPC]; exact a_second_x13 ready a b

theorem raw_view (oracle : Oracle) (input : CheckInput) (ordinal : Nat) (h : ordinal < input.positions.card)
    (s : MachineState) (fits : ProofWithin input) (cursor : RecordCursor input ordinal s)
    (framed : RecordInputFrame input ordinal s) :
    let raw := (rawLeaf oracle ordinal (honestIndex input.positions ordinal h).val s).1
    raw.pc=0x10e8 ∧ raw.getReg .x6=BitVec.ofNat 64 (honestIndex input.positions ordinal h).val.val ∧
      (∀ reg : Reg, LeafKept reg → raw.getReg reg=s.getReg reg) ∧
      (∀ word < 2^33, (word<checkSourceWord ordinal ∨ checkSourceWord ordinal+26≤word) →
        (word<1152 ∨ 1576≤word) → memoryView raw word=memoryView s word) ∧
      raw.getReg .x11 = 200 ∧ raw.getReg .x13 = 1 := by
  let item := (honestIndex input.positions ordinal h).val
  by_cases ahead : isAHead item = true
  · dsimp only
    rw [raw_leaf_a oracle ordinal item s ahead]
    exact a_raw_view input ordinal h s fits cursor framed ahead _ _
  · have sf : isAHead item = false := by simpa using ahead
    have pre := sf_cursor input ordinal s cursor
    have preFramed := sf_framed input ordinal s framed
    have ready := leaf_ready input ordinal h (sfPre s) fits pre preFramed sf
    have r := record_setup_post (sfPre s)
    dsimp only
    rw [raw_leaf_sf oracle ordinal item s sf, checker_leaf_rows]
    refine ⟨checker_leaf_finished_pc ready _ _,?_,?_,?_,?_,?_⟩
    · exact (checker_leaf_preserved_register _ _ _ _ .x6 (by decide) (by decide) (by decide)).trans
        ((staged_reg _ .x6 (by decide)).trans (r.1.trans ((by
          rw [sf_pre_register s .x8 (by decide) (by decide) (by decide)]; rfl :
          (sfPre s).getMem ((sfPre s).getReg .x8) = s.getMem (s.getReg .x8)).trans
          (loaded_index input ordinal h s cursor framed))))
    · intro reg ⟨h6, h7, h29, h28, h10, h11, h13, h12, h31⟩
      exact (checker_leaf_preserved_register _ _ _ _ reg h10 h12 h31).trans
        ((staged_saved (sfPre s) reg h6 h28 h10 h11 h13 h31).trans (sf_pre_register s reg h7 h29 h6))
    · intro word bound src scratch
      rw [checker_leaf_frame ready _ _ word bound src (by omega)]
      exact (staged_word_frame input ordinal h (sfPre s) fits pre word bound (by omega)).trans
        (congrFun (sf_pre_mem s) (wordAddress word))
    · exact (checker_leaf_preserved_register _ _ _ _ .x11 (by decide) (by decide) (by decide)).trans
        ((staged_reg _ .x11 (by decide)).trans r.2.2.2.1)
    · exact (checker_leaf_preserved_register _ _ _ _ .x13 (by decide) (by decide) (by decide)).trans
        ((staged_reg _ .x13 (by decide)).trans r.2.2.2.2.1)

theorem raw_quartet_entry (oracle : Oracle) (input : CheckInput) (ordinal : Nat) (h : ordinal < input.positions.card)
    (s : MachineState) (fits : ProofWithin input) (cursor : RecordCursor input ordinal s)
    (framed : RecordInputFrame input ordinal s) :
    QuartetEntry ordinal (honestIndex input.positions ordinal h).val
      (rawLeaf oracle ordinal (honestIndex input.positions ordinal h).val s).1 := by
  obtain ⟨pc,position,kept,wordFrame,x11,x13⟩ := raw_view oracle input ordinal h s fits cursor framed
  have card := checker_positions_bound input
  have room := (packed_record_geometry input ordinal h fits).2.2.2.1
  have keep (reg : Reg) (k : LeafKept reg) := kept reg k
  refine ⟨pc,position,?_,?_,?_,?_,?_,x11,x13,?_,room⟩
  · exact (keep .x21 (by decide)).trans cursor.proof
  · exact (keep .x20 (by decide)).trans cursor.challengeLength
  · exact (keep .x23 (by decide)).trans cursor.digest
  · exact (keep .x24 (by decide)).trans cursor.pair
  · exact (keep .x5 (by decide)).trans cursor.selector
  · intro w lo hi
    rw [wordFrame w (by omega) (Or.inl (by unfold checkSourceWord; omega)) (Or.inr (by omega)),
      framed w (by omega) (Or.inl (Or.inr ⟨lo, hi⟩))]
    exact Checker.check_scratch_word_zero input (8*w) (by omega)

/-! ### The leaf's run -/

theorem query_run_rows (oracle : Oracle) (queries : OracleComp World MachineState) (fuel cycles calls : Nat)
    (start : MachineState) (rows : List PublicRow) (count : Nat)
    (evaluated : checkEvaluation oracle (recordRows queries) = ((start, rows), count)) :
    checkEvaluation oracle (recordRows (do
      let t ← queries
      let r ← execute packedImage fuel t false
      return r.charge cycles calls)) =
    let tail := checkEvaluation oracle (recordRows (execute packedImage fuel start false))
    ((tail.1.1.charge cycles calls, rows ++ tail.1.2), count + tail.2) := by
  rw [check_recorded_bind, evaluated]
  simp only [bind_pure_comp, check_recorded_map]

theorem raw_run (oracle : Oracle) (input : CheckInput) (ordinal : Nat) (h : ordinal < input.positions.card)
    (s : MachineState) (fits : ProofWithin input) (cursor : RecordCursor input ordinal s)
    (framed : RecordInputFrame input ordinal s) (fuel : Nat) :
    let item := (honestIndex input.positions ordinal h).val
    let raw := rawLeaf oracle ordinal item s
    let tail := checkEvaluation oracle (recordRows (execute packedImage (2+fuel) raw.1 false))
    checkEvaluation oracle (recordRows (execute packedImage (leafSteps item+(2+fuel)) s false)) =
      ((tail.1.1.charge (leafCycles item) 2, raw.2++tail.1.2), 2+tail.2) := by
  intro item raw tail
  have entryPC := record_entry_pc input ordinal h s cursor
  have access := record_index_access input ordinal h s cursor
  by_cases ahead : isAHead item = true
  · have ready := a_ready input ordinal h s fits cursor framed ahead
    have run : execute packedImage (leafSteps item+(2+fuel)) s false = (do
        let t ← aLeafQueries (aEntry s) (checkSourceWord ordinal) item
        let r ← execute packedImage (2+fuel) t false
        return r.charge 91 2) := by
      rw [show leafSteps item = 71 by simp [leafSteps, ahead], show 71+(2+fuel) = 6+(65+(2+fuel)) by omega,
        execute_a_dispatch s entryPC access (a_rank input ordinal h s cursor framed ahead),
        execute_a_queries ready fuel]
      simp only [bind_assoc, pure_bind]
      simp [Execution.charge, ← Nat.add_assoc]
      try rfl
    have rows := a_leaf_rows oracle (aEntry s) (checkSourceWord ordinal) item
    rw [run, query_run_rows oracle _ _ _ _ _ _ _ rows]
    simp only [tail, raw]
    rw [raw_leaf_a oracle ordinal item s ahead, show leafCycles item = 91 by simp [leafCycles, ahead]]
  · have sf : isAHead item = false := by simpa using ahead
    have pre := sf_cursor input ordinal s cursor
    have preFramed := sf_framed input ordinal s framed
    have ready := leaf_ready input ordinal h (sfPre s) fits pre preFramed sf
    have run : execute packedImage (leafSteps item+(2+fuel)) s false = (do
        let t ← leafQueries (staged (sfPre s)) (checkSourceWord ordinal) item
        let r ← execute packedImage (2+fuel) t false
        return r.charge 62 2) := by
      have nonce : execute packedImage (16+(14+(2+fuel))) (beginRecord (sfPre s) 6) false =
          (do let result ← execute packedImage (14+(2+fuel)) (staged (sfPre s)) false
              return result.charge 16 0) :=
        copy_field_execute (fieldCode .nonce) _ _ _ (stage_ready input ordinal h (sfPre s) fits pre) _ false
      rw [show leafSteps item = 42 by simp [leafSteps, sf], show 42+(2+fuel) = 12+(16+(14+(2+fuel))) by omega,
        execute_sf_setup s entryPC access (sf_rank input ordinal h s cursor framed sf), nonce,
        execute_checker_leaf ready]
      simp only [bind_assoc, pure_bind]
      simp [Execution.charge, ← Nat.add_assoc]
      try rfl
    have rows := checker_leaf_rows oracle (staged (sfPre s)) (checkSourceWord ordinal) item
    dsimp only at rows
    rw [run, query_run_rows oracle _ _ _ _ _ _ _ rows]
    simp only [tail, raw]
    rw [raw_leaf_sf oracle ordinal item s sf, rows, show leafCycles item = 62 by simp [leafCycles, sf]]

end TwoPermutationPrototype.Packed.RecordLeaf
