import CommitGolfCandidate.QuadLowerGeometry

namespace TwoPermutationPrototype.Quad.Checker
open TwoPermutationPrototype.Packed.Checker (RecordBlock RecordSaved LowerSaved)
open CommitGolf CommitGolf.Riscv CommitGolfCandidate CommitGolfCandidate.ShortTree RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (check_recorded_bind)
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

structure LowerCursor (ordinal : Nat) (index : Index) (level : Nat) (state : MachineState) : Prop where
  pc : state.pc = if level=12 then 5056 else 4348
  node : state.getReg .x6 = BitVec.ofNat 64 (lowerNode index level)
  proof : state.getReg .x21 = BitVec.ofNat 64 (lowerProofByte ordinal level)
  counter : state.getReg .x29 = BitVec.ofNat 64 (12-level)
  digest : state.getReg .x23 = 12288
  pair : state.getReg .x24 = 12544
  selector : state.getReg .x5 = 0
  syscallBytes : state.getReg .x11 = 64
  syscallSelector : state.getReg .x13 = 0

def LowerFrame (before after : MachineState) : Prop :=
  ∀ word < 2^33, (word < 1536 ∨ 1540 ≤ word) → (word < 1568 ∨ 1576 ≤ word) →
    memoryView after word = memoryView before word

def LowerSaved (before after : MachineState) : Prop :=
  ∀ r, RecordSaved r → after.getReg r = before.getReg r

structure LowerStepFacts (oracle : Oracle) (ordinal : Nat) (index : Index) (level : Nat)
    (before : MachineState) (step : RecordBlock) : Prop where
  cursor : LowerCursor ordinal index (level+1) step.state
  steps : step.steps ≤ 116
  saved : LowerSaved before step.state
  frame : LowerFrame before step.state
  digest :
    let pair := pathPair (lowerNode index level) (readBuffer before 12288 32)
      (lowerWireSibling before ordinal level)
    readBuffer step.state 12288 32 = padLow (oracle.compression pair)
  row :
    let pair := pathPair (lowerNode index level) (readBuffer before 12288 32)
      (lowerWireSibling before ordinal level)
    PublicRow.compression pair (oracle.compression pair) ∈ step.rows
  run : ∀ fuel,
    let tail := checkEvaluation oracle (recordRows (execute packedImage fuel step.state false))
    checkEvaluation oracle (recordRows (execute packedImage (step.steps+fuel) before false)) =
      ((tail.1.1.charge step.cycles 1, step.rows++tail.1.2),1+tail.2)

def LowerStepRefines (step : Oracle → Nat → Index → Nat → MachineState → RecordBlock) : Prop :=
  ∀ (oracle : Oracle) (ordinal : Nat) (index : Index) (level : Nat) (state : MachineState),
    level < 12 → checkProofByte ordinal+570 ≤ MEMORY_BYTES → LowerCursor ordinal index level state →
      LowerStepFacts oracle ordinal index level state (step oracle ordinal index level state)

def runLower (step : Oracle → Nat → Index → Nat → MachineState → RecordBlock)
    (oracle : Oracle) (ordinal : Nat) (index : Index) : Nat → Nat → MachineState → RecordBlock
  | 0, _, state => ⟨state,0,0,[]⟩
  | left+1, level, state =>
    let earlier := step oracle ordinal index level state
    let later := runLower step oracle ordinal index left (level+1) earlier.state
    ⟨later.state,earlier.steps+later.steps,earlier.cycles+later.cycles,earlier.rows++later.rows⟩

structure LowerRunFacts (oracle : Oracle) (ordinal : Nat) (index : Index) (level left : Nat)
    (before : MachineState) (run : RecordBlock) : Prop where
  cursor : LowerCursor ordinal index 12 run.state
  steps : run.steps ≤ 116*left
  saved : LowerSaved before run.state
  frame : LowerFrame before run.state
  path : TwoPermutationPrototype.Packed.ProjectedPath run.rows (lowerNode index level) left (readBuffer before 12288 32)
    (readBuffer run.state 12288 32)
  honest : ∀ heap : Nat → Digest,
    (∀ j, level ≤ j → j<12 →
      padLow (oracle.compression (pathPair (lowerNode index j)
        (heap (lowerNode index j)) (heap (lowerNode index j ^^^ 1)))) = heap (lowerNode index (j+1))) →
    readBuffer before 12288 32 = heap (lowerNode index level) →
    (∀ j, level ≤ j → j<12 → lowerWireSibling before ordinal j = heap (lowerNode index j ^^^ 1)) →
    readBuffer run.state 12288 32 = heap (Sampling.capGroup index)
  exact_run : ∀ fuel,
    let tail := checkEvaluation oracle (recordRows (execute packedImage fuel run.state false))
    checkEvaluation oracle (recordRows (execute packedImage (run.steps+fuel) before false)) =
      ((tail.1.1.charge run.cycles left,run.rows++tail.1.2),left+tail.2)

private theorem saved_wire (before after : MachineState) (ordinal level : Nat)
    (room : checkProofByte ordinal+570 ≤ MEMORY_BYTES) (within : level<12) (framed : LowerFrame before after) :
    lowerWireSibling after ordinal level = lowerWireSibling before ordinal level := by
  apply lower_wire_sibling_frame
  intro j inside
  by_cases first : level=0
  · change checkProofByte ordinal+570 ≤ 2^36 at room
    simp only [lowerProofByte,lowerSiblingWidth,first,ite_true] at inside ⊢
    unfold checkProofByte at room ⊢
    exact framed _ (by omega) (Or.inr (by omega)) (Or.inr (by omega))
  · change checkProofByte ordinal+570 ≤ 2^36 at room
    simp only [lowerProofByte,lowerSiblingWidth,first,ite_false] at inside ⊢
    unfold checkProofByte at room ⊢
    exact framed _ (by omega) (Or.inr (by omega)) (Or.inr (by omega))

attribute [local irreducible] execute checkEvaluation readBuffer

theorem run_lower_facts (step : Oracle → Nat → Index → Nat → MachineState → RecordBlock)
    (kernel : LowerStepRefines step) (oracle : Oracle) (ordinal : Nat) (index : Index)
    (left level : Nat) (remaining : level+left=12) (room : checkProofByte ordinal+570 ≤ MEMORY_BYTES)
    (state : MachineState) (cursor : LowerCursor ordinal index level state) :
    LowerRunFacts oracle ordinal index level left state (runLower step oracle ordinal index left level state) := by
  induction left generalizing level state with
  | zero =>
    have done : level=12 := by omega
    subst level
    refine ⟨cursor,Nat.zero_le _,fun _ _ => rfl,fun _ _ _ _ => rfl,.done _ _,?_,?_⟩
    · intro heap _ child _
      simpa only [runLower,lower_node_cap_group] using child
    · intro fuel
      simp [runLower,Execution.charge]
  | succ left ih =>
    let head := step oracle ordinal index level state
    let rest := runLower step oracle ordinal index left (level+1) head.state
    have current : LowerStepFacts oracle ordinal index level state head :=
      kernel oracle ordinal index level state (by omega) room cursor
    have tail := ih (level+1) (by omega) head.state current.cursor
    rcases current with ⟨headCursor,headCost,headRegs,headMem,headDigest,headRow,headRun⟩
    rw [runLower]
    refine ⟨tail.cursor,?_,?_,?_,?_,?_,?_⟩
    · have tailCost : rest.steps ≤ 116*left := tail.steps
      change head.steps+rest.steps ≤ 116*(left+1)
      omega
    · intro r kept
      exact (tail.saved _ kept).trans (headRegs _ kept)
    · intro word bounded leftRange rightRange
      exact (tail.frame _ bounded leftRange rightRange).trans (headMem _ bounded leftRange rightRange)
    · have path := tail.path.mono (fun _ hit => List.mem_append_right head.rows hit)
      rw [lower_node_next,headDigest] at path
      exact .step (List.mem_append_left rest.rows headRow) path
    · intro heap climb child siblings
      apply tail.honest heap
      · intro j hj within
        exact climb j (by omega) within
      · rw [headDigest,child,siblings level (by omega) (by omega)]
        exact climb level (by omega) (by omega)
      · intro k next within
        rw [saved_wire state head.state ordinal k room within headMem]
        exact siblings k (by omega) within
    · intro fuel
      dsimp only
      show checkEvaluation oracle (recordRows (execute packedImage (head.steps+rest.steps+fuel) state false)) = _
      rw [show head.steps+rest.steps+fuel=head.steps+(rest.steps+fuel) by omega,headRun,tail.exact_run]
      simp only [Execution.charge,List.append_assoc,Nat.add_assoc,Nat.add_left_comm]
      rfl

end TwoPermutationPrototype.Quad.Checker
