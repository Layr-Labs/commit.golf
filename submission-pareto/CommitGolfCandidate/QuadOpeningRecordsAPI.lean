import CommitGolfCandidate.QuadOpeningRecordData
import CommitGolfCandidate.QuadOpeningRecordTail
import CommitGolfCandidate.QuadOpeningSetup
import CommitGolfCandidate.QOpeningRecordGroups

namespace TwoPermutationPrototype.QuadOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open QOpening (OpeningLayout sortedIndex SameOpeningInput trapdoorBase indicesBase nonceBase proofBase markBase RecordMarks groupsBefore machineMarks nat_address_injective)

structure RecordBoundary (s : Submission) (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (state : MachineState) (ordinal : Nat) : Prop where
  pc : state.pc = if ordinal = positions.card then 0x1b14 else 0x1044
  heap : state.getReg .x9 = BitVec.ofNat 64 trapdoorBase
  index : state.getReg .x8 = BitVec.ofNat 64 (indicesBase+8*ordinal)
  nonce : state.getReg .x22 = BitVec.ofNat 64 nonceBase
  dest : state.getReg .x21 = BitVec.ofNat 64 (recordBase ordinal)
  leaves : state.getReg .x19 = BitVec.ofNat 64 LENGTH
  input : SameOpeningInput (s.initialState .opening (trapdoor, positions)) state
  left : state.getReg .x18 = BitVec.ofNat 64 (positions.card-ordinal)
  marks : state.getReg .x26 = BitVec.ofNat 64 markBase
  one : state.getReg .x23 = 1#64
  capHeap : state.getReg .x25 = BitVec.ofNat 64 trapdoorBase
  capLeaves : state.getReg .x27 = 256#64
  proofBegin : state.getReg .x20 = BitVec.ofNat 64 proofBase
  groups : state.getReg .x24 = BitVec.ofNat 64 QOpening.groupBase
  quads : state.getReg .x28 = BitVec.ofNat 64 quadBase

theorem RecordBoundary.start {s : Submission} {trapdoor : BitVec (8*s.sizes.trapdoor)}
    {positions : Positions} {state : MachineState} {ordinal : Nat}
    (boundary : RecordBoundary s trapdoor positions state ordinal)
    (present : ordinal < positions.card) : RecordStart s trapdoor positions state ordinal :=
  ⟨by simpa only [ite_eq_right (show ordinal ≠ positions.card by omega)] using boundary.pc,
    boundary.heap, boundary.index, boundary.nonce, boundary.dest, boundary.leaves, boundary.groups,
    boundary.quads, boundary.input⟩

def recordCost (ordinal : Nat) (final : Bool) : Nat := recordDataCost ordinal+(if final then 6 else 7)

def afterLatch (marked : MachineState) (final : Bool) : MachineState :=
  if final then marked else marked.setPC 0x1044

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
  nonce : ∀ byte < 16, after.getByte (BitVec.ofNat 64 (recordBase ordinal+byte)) =
    before.getByte (BitVec.ofNat 64 (nonceAddress (sortedIndex positions ordinal present)+byte))
  leaf : ∀ j < 3, ∀ byte < 32, after.getByte (BitVec.ofNat 64 (leafDestination ordinal j+byte)) =
    before.getByte (BitVec.ofNat 64 (leafAddress (sortedIndex positions ordinal present) j+byte))
  quad : ∀ j < 3, ∀ byte < 32, after.getByte (BitVec.ofNat 64 (quadDestination ordinal j+byte)) =
    before.getByte (BitVec.ofNat 64 (quadAddress (sortedIndex positions ordinal present) j+byte))
  sibling : ∀ level < 12, ∀ byte < siblingWidth level,
    after.getByte (BitVec.ofNat 64 (siblingDestination ordinal level+byte)) =
      before.getByte (BitVec.ofNat 64 (siblingAddress (sortedIndex positions ordinal present) level+byte))

def recordsCost (size ordinal : Nat) : Nat → Nat
  | 0 => 0
  | count+1 => recordCost ordinal (decide (ordinal+1=size))+recordsCost size (ordinal+1) count

def runRecords (size ordinal : Nat) : Nat → MachineState → MachineState
  | 0, state => state
  | remaining+1, state =>
    runRecords size (ordinal+1) remaining (runRecord state (decide (ordinal+1=size)))

def CompletedRecords (s : Submission) (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions)
    (state : MachineState) (ordinal : Nat) : Prop :=
  ∀ prior (present : prior < positions.card), prior < ordinal →
    let index := sortedIndex positions prior present
    let loaded := s.initialState .opening (trapdoor, positions)
    (∀ byte < 16, state.getByte (BitVec.ofNat 64 (recordBase prior+byte)) =
      loaded.getByte (BitVec.ofNat 64 (nonceAddress index+byte))) ∧
    (∀ j < 3, ∀ byte < 32, state.getByte (BitVec.ofNat 64 (leafDestination prior j+byte)) =
      loaded.getByte (BitVec.ofNat 64 (leafAddress index j+byte))) ∧
    (∀ j < 3, ∀ byte < 32, state.getByte (BitVec.ofNat 64 (quadDestination prior j+byte)) =
      loaded.getByte (BitVec.ofNat 64 (quadAddress index j+byte))) ∧
    ∀ level < 12, ∀ byte < siblingWidth level,
      state.getByte (BitVec.ofNat 64 (siblingDestination prior level+byte)) =
        loaded.getByte (BitVec.ofNat 64 (siblingAddress index level+byte))

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

theorem site_cost_leaf (j : Fin 3) (t : Nat) : siteCost (.leaf j) t = cost32 t := by
  simp [siteCost, wideCost, cost32, CopySite.narrow, CopySite.size]

theorem site_cost_quad (j : Fin 3) (t : Nat) : siteCost (.quad j) t = cost32 t := by
  simp [siteCost, wideCost, cost32, CopySite.narrow, CopySite.size]

theorem site_cost_first (t : Nat) : siteCost .firstSibling t = cost32 t := by
  simp [siteCost, wideCost, cost32, CopySite.narrow, CopySite.size]

theorem site_cost_sibling (l : Fin 11) (t : Nat) : siteCost (.sibling l) t = cost30 t := by
  simp [siteCost, wideCost, cost30, CopySite.narrow, CopySite.size]

theorem site_cost_nonce (t : Nat) : siteCost .nonce t = 16 := by
  simp [siteCost, CopySite.narrow, CopySite.halfwords]

theorem record_data_cycles (ordinal : Nat) : recordDataCost ordinal+7 = recordCycles ordinal := by
  simp only [recordDataCost, leafPartCost, quadPartCost, lowerCost, siblingCost, siblingSite, recordCycles,
    site_cost_leaf, site_cost_quad, site_cost_nonce]
  simp [site_cost_first, site_cost_sibling]
  omega

theorem records_cost_cycles (size : Nat) : ∀ count ordinal, ordinal+count ≤ size →
    recordsCost size ordinal count+(if 0<count ∧ ordinal+count=size then 1 else 0)+recordsCycles ordinal =
      recordsCycles (ordinal+count) := by
  intro count
  induction count with
  | zero => intro ordinal _; simp [recordsCost]
  | succ count ih =>
    intro ordinal limit
    have rest := ih (ordinal+1) (by omega)
    have cyc := record_data_cycles ordinal
    have step : recordsCycles (ordinal+1) = recordsCycles ordinal+recordCycles ordinal := rfl
    have shift : ordinal+1+count = ordinal+(count+1) := by omega
    rw [shift] at rest
    simp only [recordsCost, recordCost]
    by_cases last : ordinal+1 = size
    · have zero : count = 0 := by omega
      subst zero
      subst last
      simp [recordsCost, step]
      omega
    · simp only [last, decide_false, Bool.false_eq_true, if_false]
      by_cases ends : 0 < count ∧ ordinal+1+count = size
      · rw [if_pos ⟨by omega, by omega⟩]
        rw [if_pos ⟨ends.1, by omega⟩] at rest
        omega
      · rw [if_neg (by omega)]
        rw [if_neg (by omega)] at rest
        omega

theorem records_cost_total (size : Nat) (positive : 0 < size) :
    recordsCost size 0 size = recordsCycles size-1 := by
  have total := records_cost_cycles size size 0 (by omega)
  rw [if_pos ⟨positive, by omega⟩] at total
  simp only [recordsCycles, Nat.zero_add, Nat.add_zero] at total
  omega

end TwoPermutationPrototype.QuadOpening
