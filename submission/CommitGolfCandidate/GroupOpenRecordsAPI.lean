import CommitGolfCandidate.GroupOpenRecordData
import CommitGolfCandidate.GroupOpenRecordTail
import CommitGolfCandidate.GroupOpenSetup
import CommitGolfCandidate.TwoPermutationOpeningRecordGroups

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open Opening (sortedIndex markBase
  RecordMarks groupsBefore machineMarks nat_address_injective)

structure RecordBoundary (s : Submission) (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (state : MachineState) (ordinal : Nat) : Prop where
  pc : state.pc = if ordinal = positions.card then 0x1a24 else 0x103c
  heap : state.getReg .x9 = BitVec.ofNat 64 trapdoorBase
  index : state.getReg .x8 = BitVec.ofNat 64 (indicesBase+8*ordinal)
  nonce : state.getReg .x22 = BitVec.ofNat 64 nonceBase
  dest : state.getReg .x21 = BitVec.ofNat 64 (recordBase ordinal)
  leaves : state.getReg .x19 = BitVec.ofNat 64 4194304
  slots : state.getReg .x24=BitVec.ofNat 64 groupSlots
  input : SameOpeningInput (s.initialState .opening (trapdoor, positions)) state
  left : state.getReg .x18 = BitVec.ofNat 64 (positions.card-ordinal)
  marks : state.getReg .x26 = BitVec.ofNat 64 markBase
  one : state.getReg .x23 = 1#64
  capHeap : state.getReg .x25 = BitVec.ofNat 64 trapdoorBase
  capLeaves : state.getReg .x27 = 256#64
  proofBegin : state.getReg .x20 = BitVec.ofNat 64 proofBase

theorem RecordBoundary.start {s : Submission} {trapdoor : BitVec (8*s.sizes.trapdoor)}
    {positions : Positions} {state : MachineState} {ordinal : Nat}
    (boundary : RecordBoundary s trapdoor positions state ordinal)
    (present : ordinal < positions.card) : RecordStart s trapdoor positions state ordinal :=
  ⟨by simpa only [ite_eq_right (show ordinal ≠ positions.card by omega)] using boundary.pc,
    boundary.heap, boundary.index, boundary.nonce, boundary.dest, boundary.leaves, boundary.slots, boundary.input⟩

/-- Cycles of record `ordinal` (the final record skips the loop jump): its four 32-byte and eleven 30-byte wide
copies depend on its alignment. -/
def recordCost (ordinal : Nat) (final : Bool) : Nat := (if final then 214 else 215)+recordExtra ordinal

def afterLatch (marked : MachineState) (final : Bool) : MachineState :=
  if final then marked else marked.setPC 0x103c

def runRecord (state : MachineState) (final : Bool) : MachineState :=
  afterLatch (recordTailPrefix (recordData state) 6) final

structure OneRecord (s : Submission) (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (before after : MachineState) (ordinal : Nat)
    (present : ordinal < positions.card) : Prop where
  run : RunsOpeningBlock before after (recordCost ordinal (decide (ordinal+1=positions.card)))
  next : RecordBoundary s trapdoor positions after (ordinal+1)
  marks : ∀ node < 512, machineMarks after node =
    if node = Sampling.capGroup (sortedIndex positions ordinal present) then 1 else machineMarks before node
  frame : ∀ address < MEMORY_BYTES, trapdoorBase ≤ address →
    address < recordBase ordinal ∨ recordBase (ordinal+1) ≤ address →
    after.getByte (BitVec.ofNat 64 address) = before.getByte (BitVec.ofNat 64 address)
  nonce : ∀ byte < 112, after.getByte (BitVec.ofNat 64 (recordBase ordinal+byte)) =
    before.getByte (BitVec.ofNat 64 (firstSource (sortedIndex positions ordinal present) byte))
  sibling : ∀ level < 14, ∀ byte < plainWidth level,
    after.getByte (BitVec.ofNat 64 (siblingDestination ordinal level+byte)) =
      before.getByte (BitVec.ofNat 64 (siblingAddress (sortedIndex positions ordinal present) level+byte))
  fold : ∀ k < 7, ∀ b < 2,
    after.getByte (BitVec.ofNat 64 (siblingDestination ordinal (6+k)+28+b)) =
      (foldValue (before.getHalfword (BitVec.ofNat 64 (siblingAddress (sortedIndex positions ordinal present) (6+k)+28)))
        ((before.getHalfword (BitVec.ofNat 64 (siblingAddress (sortedIndex positions ordinal present) 13+28))).zeroExtend 64
          >>> (2*k))).extractLsb' (8*b) 8

def recordsCost (size ordinal : Nat) : Nat → Nat
  | 0 => 0
  | count+1 => recordCost ordinal (decide (ordinal+1=size))+recordsCost size (ordinal+1) count

/-- Wide-copy cycles of records `0..n-1`. -/
def copySum : Nat → Nat
  | 0 => 0
  | n+1 => copySum n+recordExtra n

theorem records_cost_sum (size : Nat) : ∀ count ordinal, ordinal+count ≤ size →
    recordsCost size ordinal count+copySum ordinal+(if 0<count ∧ ordinal+count=size then 1 else 0) =
      215*count+copySum (ordinal+count) := by
  intro count
  induction count with
  | zero => intro ordinal _; simp [recordsCost]
  | succ count ih =>
    intro ordinal fit
    have rest := ih (ordinal+1) (by omega)
    have step : copySum (ordinal+1) = copySum ordinal+recordExtra ordinal := rfl
    rw [show ordinal+1+count = ordinal+(count+1) by omega] at rest
    simp only [recordsCost, recordCost]
    by_cases last : ordinal+1 = size
    · have empty : count = 0 := by omega
      subst empty
      subst last
      simp [recordsCost, copySum]
      omega
    · simp only [last, decide_false, Bool.false_eq_true, ite_false] at rest ⊢
      by_cases done : ordinal+(count+1) = size
      · have pos : 0 < count := by omega
        rw [if_pos ⟨pos, done⟩] at rest
        rw [if_pos ⟨by omega, done⟩]
        omega
      · rw [if_neg (fun h => done h.2)] at rest
        rw [if_neg (fun h => done h.2)]
        omega

theorem records_total (size : Nat) (positive : 0 < size) :
    recordsCost size 0 size = 215*size+copySum size-1 := by
  have h := records_cost_sum size size 0 (by omega)
  rw [if_pos ⟨positive, by omega⟩] at h
  simp only [copySum, Nat.zero_add, Nat.mul_zero, Nat.add_zero] at h
  omega

def runRecords (size ordinal : Nat) : Nat → MachineState → MachineState
  | 0, state => state
  | remaining+1, state =>
    runRecords size (ordinal+1) remaining (runRecord state (decide (ordinal+1=size)))

def CompletedRecords (s : Submission) (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions)
    (state : MachineState) (ordinal : Nat) : Prop :=
  ∀ prior (present : prior < positions.card), prior < ordinal →
    let index := sortedIndex positions prior present
    let loaded := s.initialState .opening (trapdoor, positions)
    (∀ byte < 112, state.getByte (BitVec.ofNat 64 (recordBase prior+byte)) =
      loaded.getByte (BitVec.ofNat 64 (firstSource index byte))) ∧
    (∀ level < 14, ∀ byte < plainWidth level,
      state.getByte (BitVec.ofNat 64 (siblingDestination prior level+byte)) =
        loaded.getByte (BitVec.ofNat 64 (siblingAddress index level+byte))) ∧
    ∀ k < 7, ∀ b < 2,
      state.getByte (BitVec.ofNat 64 (siblingDestination prior (6+k)+28+b)) =
        (foldValue (loaded.getHalfword (BitVec.ofNat 64 (siblingAddress index (6+k)+28)))
          ((loaded.getHalfword (BitVec.ofNat 64 (siblingAddress index 13+28))).zeroExtend 64 >>> (2*k))).extractLsb' (8*b) 8

structure RecordsFinished (s : Submission) (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (before after : MachineState) (ordinal count : Nat) : Prop where
  run : RunsOpeningBlock before after (recordsCost positions.card ordinal count)
  boundary : RecordBoundary s trapdoor positions after (ordinal+count)
  marks : RecordMarks positions after (ordinal+count)
  bytes : CompletedRecords s trapdoor positions after (ordinal+count)

def RecordExecute : Prop :=
  ∀ (s : Submission) (_layout : OpeningLayout s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions)
    (state : MachineState) (ordinal : Nat) (present : ordinal < positions.card),
    RecordBoundary s trapdoor positions state ordinal →
    OneRecord s trapdoor positions state (runRecord state (decide (ordinal+1=positions.card))) ordinal present

def RecordsExecute : Prop :=
  ∀ (s : Submission) (_layout : OpeningLayout s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions)
    (state : MachineState) (ordinal count : Nat), ordinal+count ≤ positions.card →
    RecordBoundary s trapdoor positions state ordinal →
    RecordMarks positions state ordinal →
    CompletedRecords s trapdoor positions state ordinal →
    RecordsFinished s trapdoor positions state (runRecords positions.card ordinal count state) ordinal count

end TwoPermutationPrototype.GroupedOpening
