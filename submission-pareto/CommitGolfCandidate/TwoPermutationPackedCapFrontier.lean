import CommitGolfCandidate.TwoPermutationPackedCapVisit
import CommitGolfCandidate.TwoPermutationPackedCapBytes

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (capRootAt)

/-- At word 294 with frontier node `first` of the packed frontier at `start` next. -/
structure FrontierReady (state : MachineState) (node start first : Nat) : Prop where
  pc : state.pc = 0x1498
  nodeReg : state.getReg .x6 = BitVec.ofNat 64 node
  capReg : state.getReg .x25 = 16384#64
  proofReg : state.getReg .x21 = BitVec.ofNat 64 (start+capPackedBytes first)
  countdown : state.getReg .x30 = BitVec.ofNat 64 (7-first%8)
  below : node < 512
  above : 32768 ≤ start
  even : start%2 = 0
  room : start+capPackedBytes (first+1) ≤ MEMORY_BYTES

/-- The bound check of the read fails: fewer than `capSlotBytes first` proof bytes remain. -/
def FrontierShort (state : MachineState) (start first : Nat) : Prop :=
  state.getReg .x22 < BitVec.ofNat 64 (start+capPackedBytes (first+1))

/-- Steps of one packed read: 45 for a normal node, 64 for the last node of a group of eight. -/
def frontierSteps (first : Nat) : Nat := if first%8 = 7 then 64 else 45

/-- Steps up to the rejecting branch when the read is short. -/
def frontierShortSteps (first : Nat) : Nat := if first%8 = 7 then 6 else 8

theorem frontier_steps_le (first : Nat) : frontierSteps first ≤ 64 := by
  unfold frontierSteps; split <;> omega

theorem frontier_short_steps_le (first : Nat) : frontierShortSteps first ≤ 8 := by
  unfold frontierShortSteps; split <;> omega

/-- One packed frontier read, exposed separately from the DFS induction. -/
structure FrontierKernel where
  after : MachineState → MachineState
  rejected : MachineState → MachineState
  run : ∀ (state : MachineState) (node start first : Nat), FrontierReady state node start first →
    ¬ FrontierShort state start first →
    ∀ fuel, execute packedImage (frontierSteps first+fuel) state false = do
      let result ← execute packedImage fuel (after state) false
      return result.charge (frontierSteps first) 0
  digest : ∀ (state : MachineState) (node start first : Nat), FrontierReady state node start first →
    ¬ FrontierShort state start first →
    capRootAt (after state) node = capFrontierValue state start first
  register : ∀ state reg, reg ≠ .x7 → reg ≠ .x21 → reg ≠ .x28 → reg ≠ .x30 → reg ≠ .x31 →
    (after state).getReg reg = state.getReg reg
  pointer : ∀ (state : MachineState) (node start first : Nat), FrontierReady state node start first →
    ¬ FrontierShort state start first →
    (after state).pc = 0x1528 ∧
    (after state).getReg .x21 = BitVec.ofNat 64 (start+capPackedBytes (first+1)) ∧
    (after state).getReg .x30 = BitVec.ofNat 64 (7-(first+1)%8)
  frame : ∀ (state : MachineState) (node start first : Nat), FrontierReady state node start first →
    ¬ FrontierShort state start first →
    ∀ word < 2^61, (word < 2048+4*node ∨ 2048+4*node+4 ≤ word) →
      memoryView (after state) word = memoryView state word
  shortRun : ∀ (state : MachineState) (node start first : Nat), FrontierReady state node start first →
    FrontierShort state start first →
    ∀ fuel, execute packedImage (frontierShortSteps first+fuel) state false = do
      let result ← execute packedImage fuel (rejected state) false
      return result.charge (frontierShortSteps first) 0
  shortPC : ∀ (state : MachineState) (node start first : Nat), FrontierReady state node start first →
    FrontierShort state start first → (rejected state).pc = 0x15b0
  shortRegister : ∀ state reg, reg ≠ .x7 → reg ≠ .x28 → reg ≠ .x30 →
    (rejected state).getReg reg = state.getReg reg
  shortMemory : ∀ state, (rejected state).mem = state.mem

theorem cap_frontier_stable (codec : FrontierKernel) (state : MachineState) :
    CapStable state (codec.after state) := by
  intro r found
  simp [capFixedRegisters] at found
  rcases found with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact codec.register _ _ (by decide) (by decide) (by decide) (by decide) (by decide)

theorem cap_short_stable (codec : FrontierKernel) (state : MachineState) :
    CapStable state (codec.rejected state) := by
  intro r found
  simp [capFixedRegisters] at found
  rcases found with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact codec.shortRegister _ _ (by decide) (by decide) (by decide)

def capFrontierSegment (codec : FrontierKernel) (oracle : Oracle) {state : MachineState} {node start first : Nat}
    (ready : FrontierReady state node start first) (fits : ¬ FrontierShort state start first) :
    Segment oracle state (codec.after state) :=
  Segment.ordinary oracle (frontierSteps first) (frontierSteps first) (codec.run state node start first ready fits)

def capShortSegment (codec : FrontierKernel) (oracle : Oracle) {state : MachineState} {node start first : Nat}
    (ready : FrontierReady state node start first) (short : FrontierShort state start first) :
    Segment oracle state (codec.rejected state) :=
  Segment.ordinary oracle (frontierShortSteps first) (frontierShortSteps first)
    (codec.shortRun state node start first ready short)

theorem cap_frontier_position (codec : FrontierKernel) {groups : List Nat}
    {state : MachineState} {node start first : Nat}
    (position : CapPosition groups state node start first) (ready : FrontierReady state node start first)
    (fits : ¬ FrontierShort state start first) :
    CapPosition groups (codec.after state) node start (first+1) := by
  obtain ⟨_, proof, count⟩ := codec.pointer state node start first ready fits
  refine ⟨position.context.transport (cap_frontier_stable codec state) ?_,
    (codec.register state .x6 (by decide) (by decide) (by decide) (by decide) (by decide)).trans position.heap,
    proof, count, position.above, position.even⟩
  intro word low high
  exact codec.frame state node start first ready fits word (by omega) (Or.inl (by omega))

end TwoPermutationPrototype.Packed.Checker
