-- Pair-heads copy of TwoPermutationPackedLowerRecursion (stack/check/work/mkcopy.py); edits below are marked PAIR.
import CommitGolfCandidate.PairCheckRecordGeometry
import CommitGolfCandidate.PairCheckNamespaces
import CommitGolfCandidate.QuartetCheckHeap

namespace TwoPermutationPrototype.PairCk.Packed.Checker
open  TwoPermutationPrototype.Packed TwoPermutationPrototype.Packed.Checker TwoPermutationPrototype.PairCk.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate CommitGolfCandidate.ShortTree RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (check_recorded_bind)
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

/-- Registers before Quartet upper level `level` (heap node `lowerNode index (level+2)`), or at the
mark-table insertion after level fourteen. -/
structure LowerCursor (ordinal : Nat) (index : Index) (level : Nat) (state : MachineState) : Prop where
  pc : state.pc = if level=14 then 5056 else 4348
  node : state.getReg .x6 = BitVec.ofNat 64 (Opening.lowerNode index (level+2))
  proof : state.getReg .x21 = BitVec.ofNat 64 (lowerProofByte ordinal level)
  counter : state.getReg .x29 = BitVec.ofNat 64 (14-level)
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
    let pair := pathPair (Opening.lowerNode index (level+2)) (readBuffer before 12288 32)
      (lowerWireSibling before ordinal level)
    readBuffer step.state 12288 32 = padLow (oracle.compression pair)
  row :
    let pair := pathPair (Opening.lowerNode index (level+2)) (readBuffer before 12288 32)
      (lowerWireSibling before ordinal level)
    PublicRow.compression pair (oracle.compression pair) ∈ step.rows
  run : ∀ fuel,
    let tail := checkEvaluation oracle (recordRows (execute pairImage fuel step.state false))
    checkEvaluation oracle (recordRows (execute pairImage (step.steps+fuel) before false)) =
      ((tail.1.1.charge step.cycles 1, step.rows++tail.1.2),1+tail.2)

def LowerStepRefines (step : Oracle → Nat → Index → Nat → MachineState → RecordBlock) : Prop :=
  ∀ (oracle : Oracle) (ordinal : Nat) (index : Index) (level : Nat) (state : MachineState),
    level < 14 → checkProofByte ordinal+534 ≤ MEMORY_BYTES → LowerCursor ordinal index level state →
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
  cursor : LowerCursor ordinal index 14 run.state
  steps : run.steps ≤ 116*left
  saved : LowerSaved before run.state
  frame : LowerFrame before run.state
  path : ProjectedPath run.rows (Opening.lowerNode index (level+2)) left (readBuffer before 12288 32)
    (readBuffer run.state 12288 32)
  honest : ∀ (lookup : BitVec 1024 → BitVec 256) (leaves : DigestTape),
    let heap := Sampling.Quartet.upperHeap lookup oracle.compression leaves
    readBuffer before 12288 32 = heap (Opening.lowerNode index (level+2)) →
    (∀ j, level ≤ j → j < 14 →
      lowerWireSibling before ordinal j = heap (Opening.lowerNode index (j+2) ^^^ 1)) →
    readBuffer run.state 12288 32 = heap (capGroup index)
  exact_run : ∀ fuel,
    let tail := checkEvaluation oracle (recordRows (execute pairImage fuel run.state false))
    checkEvaluation oracle (recordRows (execute pairImage (run.steps+fuel) before false)) =
      ((tail.1.1.charge run.cycles left,run.rows++tail.1.2),left+tail.2)

private theorem saved_wire (before after : MachineState) (ordinal level : Nat)
    (room : checkProofByte ordinal+534 ≤ MEMORY_BYTES) (within : level<14) (framed : LowerFrame before after) :
    lowerWireSibling after ordinal level = lowerWireSibling before ordinal level := by
  apply lower_wire_sibling_frame
  intro j inside
  by_cases first : level=0
  · change checkProofByte ordinal+534 ≤ 2^36 at room
    simp only [lowerProofByte,lowerSiblingWidth,first,ite_true] at inside ⊢
    unfold checkProofByte at room ⊢
    exact framed _ (by omega) (Or.inr (by omega)) (Or.inr (by omega))
  · change checkProofByte ordinal+534 ≤ 2^36 at room
    simp only [lowerProofByte,lowerSiblingWidth,first,ite_false] at inside ⊢
    unfold checkProofByte at room ⊢
    exact framed _ (by omega) (Or.inr (by omega)) (Or.inr (by omega))

attribute [local irreducible] execute checkEvaluation Sampling.Quartet.upperHeap readBuffer

theorem run_lower_facts (step : Oracle → Nat → Index → Nat → MachineState → RecordBlock)
    (kernel : LowerStepRefines step) (oracle : Oracle) (ordinal : Nat) (index : Index)
    (left level : Nat) (remaining : level+left=14) (room : checkProofByte ordinal+534 ≤ MEMORY_BYTES)
    (state : MachineState) (cursor : LowerCursor ordinal index level state) :
    LowerRunFacts oracle ordinal index level left state (runLower step oracle ordinal index left level state) := by
  induction left generalizing level state with
  | zero =>
    have done : level=14 := by omega
    subst level
    refine ⟨cursor,Nat.zero_le _,fun _ _ => rfl,fun _ _ _ _ => rfl,.done _ _,?_,?_⟩
    · intro lookup leaves
      dsimp only
      intro child _
      exact child.trans (congrArg _ (Opening.lower_node_cap_group index))
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
      rw [show level+1+2 = (level+2)+1 by omega, Opening.lower_node_next index (level+2),headDigest] at path
      exact .step (List.mem_append_left rest.rows headRow) path
    · intro lookup leaves
      dsimp only
      intro child siblings
      apply tail.honest lookup leaves
      · have fit : level<14 := by omega
        have bounds := QuartetCheck.lower_node_upper_bounds index level fit
        change readBuffer head.state 12288 32 =
          Sampling.Quartet.upperHeap lookup oracle.compression leaves (Opening.lowerNode index (level+1+2))
        rw [headDigest, child, siblings level (by omega) fit,show level+1+2 = (level+2)+1 by omega,Opening.lower_node_next index (level+2)]
        exact QuartetCheck.upper_heap_climb lookup oracle.compression leaves _ bounds.1 bounds.2
      · intro k next within
        rw [saved_wire state head.state ordinal k room within headMem]
        exact siblings k (by omega) within
    · intro fuel
      dsimp only
      show checkEvaluation oracle (recordRows (execute pairImage (head.steps+rest.steps+fuel) state false)) = _
      rw [show head.steps+rest.steps+fuel=head.steps+(rest.steps+fuel) by omega,headRun,tail.exact_run]
      simp only [Execution.charge,List.append_assoc,Nat.add_assoc,Nat.add_left_comm]
      rfl

end TwoPermutationPrototype.PairCk.Packed.Checker
