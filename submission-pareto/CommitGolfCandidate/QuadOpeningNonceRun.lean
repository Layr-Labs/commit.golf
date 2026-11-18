import CommitGolfCandidate.QuadOpeningLeafPart
import CommitGolfCandidate.QOpeningRecordStart

namespace TwoPermutationPrototype.QuadOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open QOpening (OpeningLayout SameOpeningInput sortedIndex trapdoorBase indicesBase nonceBase proofBase)

structure RecordStart (s : Submission) (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (state : MachineState) (ordinal : Nat) : Prop where
  pc : state.pc = 0x103c
  heap : state.getReg .x9 = BitVec.ofNat 64 trapdoorBase
  index : state.getReg .x8 = BitVec.ofNat 64 (indicesBase+8*ordinal)
  nonce : state.getReg .x22 = BitVec.ofNat 64 nonceBase
  dest : state.getReg .x21 = BitVec.ofNat 64 (recordBase ordinal)
  leaves : state.getReg .x19 = BitVec.ofNat 64 LENGTH
  groups : state.getReg .x24 = BitVec.ofNat 64 QOpening.groupBase
  input : SameOpeningInput (s.initialState .opening (trapdoor, positions)) state

def nonceCopy (state : MachineState) : MachineState :=
  nonceAdvance (copyState .nonce (nonceSetup state))

def nonceBlock (state : MachineState) : MachineState :=
  leafPart (nonceCopy state)

structure NonceTrace (state : MachineState) (index : Index) (ordinal : Nat) : Prop where
  run : RunsOpeningBlock state (nonceBlock state) 142
  next : LowerCursor (nonceBlock state) index ordinal 0
  nonce : ∀ byte < 16, (nonceBlock state).getByte (BitVec.ofNat 64 (recordBase ordinal+byte)) =
    state.getByte (BitVec.ofNat 64 (nonceAddress index+byte))
  leaf : ∀ j < 3, ∀ byte < 32,
    (nonceBlock state).getByte (BitVec.ofNat 64 (leafDestination ordinal j+byte)) =
      state.getByte (BitVec.ofNat 64 (leafAddress index j+byte))
  frame : ∀ address < 2^64, address < recordBase ordinal ∨ siblingDestination ordinal 0 ≤ address →
    (nonceBlock state).getByte (BitVec.ofNat 64 address) = state.getByte (BitVec.ofNat 64 address)
  register : ∀ reg, reg ≠ .x6 → reg ≠ .x7 → reg ≠ .x10 → reg ≠ .x11 → reg ≠ .x21 → reg ≠ .x30 →
    reg ≠ .x31 → (nonceBlock state).getReg reg = state.getReg reg
  input : ∀ address < proofBase,
    (nonceBlock state).getMem (BitVec.ofNat 64 address) = state.getMem (BitVec.ofNat 64 address)

private theorem nonce_copy_outside {before after : MachineState} {source dest size : Nat}
    (copy : ByteCopy before after source dest size) (address : Nat)
    (fit : address < 2^64) (endFit : dest+size ≤ 2^64)
    (outside : address < dest ∨ dest+size ≤ address) :
    after.getByte (BitVec.ofNat 64 address) = before.getByte (BitVec.ofNat 64 address) := by
  apply copy.frame
  intro i inside equal
  have same := QOpening.nat_address_injective fit (by omega) equal
  omega

theorem execute_ordinal_nonce (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions)
    (state : MachineState) (ordinal : Nat) (present : ordinal < positions.card)
    (ready : RecordStart s trapdoor positions state ordinal) :
    NonceTrace state (sortedIndex positions ordinal present) ordinal := by
  let index := sortedIndex positions ordinal present
  let prepared := nonceSetup state
  let copied := copyState .nonce prepared
  let middle := nonceCopy state
  have cardinal : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
  have below : indicesBase+8*ordinal < proofBase := by
    have geometry := QOpening.indices_before_records
    omega
  have above : trapdoorBase ≤ indicesBase+8*ordinal := by unfold indicesBase; omega
  have readIndex : state.getMem (state.getReg .x8) = BitVec.ofNat 64 index.val := by
    rw [ready.index, ready.input _ above below]
    exact QOpening.input_index s layout trapdoor positions ordinal present
  have inputSafe : accessValid (state.getReg .x8) 8 = true := by
    rw [ready.index]
    apply QOpening.aligned_access
    · have aligned : indicesBase % 8 = 0 := by decide
      omega
    · have ram := packed_proof_memory
      have slots := QOpening.indices_before_records
      omega
  have setup := nonce_setup_post state
  have advance := nonce_advance_post copied
  have landscape := all_nonce_copies_fit index ordinal (by omega)
  have field : FieldInputs .nonce prepared (nonceAddress index) (recordBase ordinal) :=
    ⟨by rw [setup.1, ready.pc]; rfl, physical_nonce_source state index ready.nonce readIndex,
      (setup.2.2.2.2 .x21 (by decide) (by decide)).trans ready.dest,
      landscape.2.2.1, landscape.2.2.2, landscape.1, landscape.2.1⟩
  have advancePC : copied.pc = 0x1088 := field.final_pc
  have kept (reg : Reg) (a : reg ≠ .x6) (b : reg ≠ .x7) (c : reg ≠ .x21) (d : reg ≠ .x31) :
      middle.getReg reg = state.getReg reg :=
    (advance.2.2.2 reg c).trans
      ((copy_register .nonce prepared reg d).trans (setup.2.2.2.2 reg a b))
  have startRun : RunsOpeningBlock state prepared 3 :=
    fun fuel coins => execute_nonce_setup state ready.pc inputSafe fuel coins
  have endRun : RunsOpeningBlock copied middle 1 :=
    fun fuel coins => execute_nonce_advance copied advancePC fuel coins
  have nonceBytes : ByteCopy state middle (nonceAddress index) (recordBase ordinal) 16 :=
    field.bytes.move setup.2.1.symm advance.2.1
  have middleInput : ∀ address < proofBase,
      middle.getMem (BitVec.ofNat 64 address) = state.getMem (BitVec.ofNat 64 address) := by
    intro address below
    have separate : proofBase ≤ recordBase ordinal := by unfold recordBase; omega
    have stable := field.words_before proofBase address below separate (by decide)
    have saved : middle.mem = copied.mem := advance.2.1
    have reads : prepared.mem = state.mem := setup.2.1
    change middle.getMem _ = _
    simpa only [MachineState.getMem, saved, reads] using stable
  have entry : LeafEntry middle index ordinal := by
    refine ⟨?_, (kept .x9 (by decide) (by decide) (by decide) (by decide)).trans ready.heap,
      (kept .x24 (by decide) (by decide) (by decide) (by decide)).trans ready.groups,
      (kept .x19 (by decide) (by decide) (by decide) (by decide)).trans ready.leaves, ?_, ?_⟩
    · change (nonceAdvance copied).pc = _
      rw [advance.1, advancePC]
      rfl
    · change (nonceAdvance copied).getReg .x6 = _
      rw [advance.2.2.2 .x6 (by decide), copy_register .nonce prepared .x6 (by decide),
        setup.2.2.2.1, readIndex]
    · change (nonceAdvance copied).getReg .x21 = _
      rw [advance.2.2.1, copy_register .nonce prepared .x21 (by decide),
        setup.2.2.2.2 .x21 (by decide) (by decide), ready.dest]
      exact (BitVec.ofNat_add (n := 64) (recordBase ordinal) 16).symm
  have leaves := execute_leaf_part middle index ordinal (by omega) entry
  have ram : MEMORY_BYTES < 2^64 := by decide
  have endFit : siblingDestination ordinal 0 = recordBase ordinal+112 := rfl
  have fitNonce := landscape.2.2.2
  refine ⟨(startRun.next field.run).next endRun |>.next leaves.run, leaves.next, ?_, ?_, ?_, ?_, ?_⟩
  · intro byte inside
    exact (leaves.frame _ (by omega) (Or.inl (by omega))).trans (nonceBytes.copied byte inside)
  · intro j valid byte inside
    have fit := all_leaf_copies_fit index ordinal j (by omega) valid
    have pr : proofBase ≤ recordBase ordinal := by unfold recordBase; omega
    exact (leaves.leaf j valid byte inside).trans
      (nonce_copy_outside nonceBytes _ (by omega) (by omega) (Or.inl (by omega)))
  · intro address fit outside
    rw [endFit] at outside
    exact (leaves.frame address fit (outside.imp (fun h => by omega) (fun h => by rw [endFit]; omega))).trans
      (nonce_copy_outside nonceBytes address fit (by omega) (outside.imp id (fun h => by omega)))
  · intro reg a b c d e f g
    exact (leaves.register reg a b c d e f g).trans (kept reg a b e g)
  · intro address below
    exact (leaves.input address below).trans (middleInput address below)

end TwoPermutationPrototype.QuadOpening
