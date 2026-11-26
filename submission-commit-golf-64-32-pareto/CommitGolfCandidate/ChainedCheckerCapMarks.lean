import CommitGolfCandidate.ChainedCheckerCapRoot
import CommitGolfCandidate.TwoPermutationOpeningMarkMachine
import CommitGolfCandidate.TwoPermutationOpeningMarkContents

/-! Actual descending cap-parent mark sweep and its canonical mark/frame predicates. -/
namespace CommitGolfCandidate.Chained.Native.CheckerCap.Visit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype TwoPermutationPrototype.RV64
open TwoPermutationPrototype.Sampling
attribute [local irreducible] execute chainedCheckerImage
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 4096
open TwoPermutationPrototype.Opening

attribute [local simp] getReg_setReg getReg_setMem

private theorem cap_fetch (state : MachineState) (index : Nat) (instruction : Instr)
    (bounded : index<3012) (pc : state.pc=BitVec.ofNat 64 (4096+4*index))
    (opcode : chainedCheckerOps.getD index .EBREAK=instruction) :
    fetch chainedCheckerImage state=some (.base instruction) := by
  have location : state.pc=4096+BitVec.ofNat 64 (4*index) := by
    change state.pc=BitVec.ofNat 64 4096+BitVec.ofNat 64 (4*index)
    rwa [←BitVec.ofNat_add]
  simpa only [opcode] using chained_checker_ops_at index
    (by rw [chained_checker_ops_length]; exact bounded) state location


@[local simp] private theorem pc_setPC (state : MachineState) (pc : Word) :
    (state.setPC pc).pc = pc := rfl

@[local simp] private theorem zero_reg (state : MachineState) : state.getReg .x0 = 0#64 := rfl

def markParentPrefix (state : MachineState) (count : Nat) : MachineState :=
  ((TwoPermutationPrototype.Opening.capMarkInstructions.drop 1).take count).foldl execInstrBr state

def childrenAddress (state : MachineState) : Word :=
  state.getReg .x26 + (state.getReg .x6 <<< 4)

def parentAddress (state : MachineState) : Word :=
  state.getReg .x26 + (state.getReg .x6 <<< 3)

private theorem mark_decode (i : Fin 10) :
    chainedCheckerOps.getD (2648+i.val) .EBREAK =
      ((TwoPermutationPrototype.Opening.capMarkInstructions.drop 1)[i.val]?.getD .EBREAK) := by
  fin_cases i <;> rfl

theorem mark_prefix_succ (state : MachineState) (i : Nat) (bounded : i < 10) :
    markParentPrefix state (i+1) =
      execInstrBr (markParentPrefix state i) ((TwoPermutationPrototype.Opening.capMarkInstructions.drop 1)[i]?.getD .EBREAK) := by
  have inside : i < (TwoPermutationPrototype.Opening.capMarkInstructions.drop 1).length := bounded
  rw [markParentPrefix, markParentPrefix, List.take_succ_eq_append_getElem inside,
    List.foldl_append, List.getElem?_eq_getElem inside]
  rfl

private theorem mark_ordinary (state : MachineState) (i : Fin 10)
    (valid : memoryArgumentsValid state ((TwoPermutationPrototype.Opening.capMarkInstructions.drop 1)[i.val]?.getD .EBREAK) = true) :
    ordinaryStep state (.base ((TwoPermutationPrototype.Opening.capMarkInstructions.drop 1)[i.val]?.getD .EBREAK)) =
      some (execInstrBr state ((TwoPermutationPrototype.Opening.capMarkInstructions.drop 1)[i.val]?.getD .EBREAK)) := by
  fin_cases i <;> simp [TwoPermutationPrototype.Opening.capMarkInstructions] at valid ⊢ <;> exact ite_eq_left valid

/-- One iteration of the actual descending cap-parent loop takes ten cycles. -/
theorem execute_mark_parent (state : MachineState) (pc : state.pc = (4096+4*2648)) (fuel : Nat)
    (left : accessValid (childrenAddress state) 8 = true)
    (right : accessValid (childrenAddress state + 8#64) 8 = true)
    (parent : accessValid (parentAddress state) 8 = true) :
    execute chainedCheckerImage (10 + fuel) state false =
      (do let result ← execute chainedCheckerImage fuel (markParentPrefix state 10) false
          return result.charge 10 0) := by
  apply execute_unit_steps (states := markParentPrefix state)
  intro i bounded
  refine ⟨.base ((TwoPermutationPrototype.Opening.capMarkInstructions.drop 1)[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply cap_fetch _ (2648 + i) _ (by omega) _ (mark_decode ⟨i, bounded⟩)
    interval_cases i <;> simp [markParentPrefix, TwoPermutationPrototype.Opening.capMarkInstructions, execInstrBr, pc]
  · rw [mark_prefix_succ state i bounded]
    apply mark_ordinary _ ⟨i, bounded⟩
    simp only [childrenAddress] at left right
    simp only [parentAddress] at parent
    interval_cases i <;>
      simp [memoryArgumentsValid, memAccess, markParentPrefix, TwoPermutationPrototype.Opening.capMarkInstructions,
        execInstrBr, signExtend12, left, right, parent]
  · interval_cases i <;> rfl

@[local simp] private theorem mark_mem_setReg (s : MachineState) (r : Reg) (w : Word) :
    (s.setReg r w).mem = s.mem := by cases r <;> rfl

@[local simp] private theorem mark_mem_setPC (s : MachineState) (w : Word) :
    (s.setPC w).mem = s.mem := rfl

@[local simp] private theorem mark_mem_setMem (s : MachineState) (address value : Word) :
    (s.setMem address value).mem =
      fun atAddress => if atAddress = address then value else s.mem atAddress := by
  funext atAddress
  simp [MachineState.setMem]

/-- The parent instruction reads both children, ORs their marks, and changes only
the parent word. Its latch visits the next parent or starts the cap walk. -/
theorem mark_parent_post (state : MachineState) (pc : state.pc = (4096+4*2648)) :
    let after := markParentPrefix state 10
    let left := state.getMem (childrenAddress state)
    let right := state.getMem (childrenAddress state + 8#64)
    after.mem = (state.setMem (parentAddress state) (left ||| right)).mem ∧
    after.getReg .x26 = state.getReg .x26 ∧
    after.getReg .x6 = state.getReg .x6 - 1 ∧
    after.pc = if state.getReg .x6 - 1 = 0#64 then (4096+4*2658) else (4096+4*2648) := by
  by_cases done : state.getReg .x6 + 18446744073709551615#64 = 0#64 <;>
    simp [markParentPrefix, TwoPermutationPrototype.Opening.capMarkInstructions, execInstrBr, parentAddress, childrenAddress,
      signExtend12, signExtend13, BitVec.sub_eq_add_neg, pc, done]

open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.Opening hiding markParentPrefix execute_mark_parent mark_parent_post
  mark_sweep_pc markMachine machineMarks machine_mark_parent

attribute [local irreducible] markParentPrefix
set_option maxRecDepth 4096

def machineMarks (state : MachineState) (node : Nat) : Word :=
  state.getMem (BitVec.ofNat 64 (markBase + 8 * node))

def markMachine (state : MachineState) : Nat → MachineState
  | 0 => state
  | remaining + 1 => markMachine (markParentPrefix state 10) remaining

theorem mark_sweep_pc (state : MachineState) (remaining : Nat) (within : remaining < 256)
    (pc : state.pc = (4096+4*2648))
    (count : state.getReg .x6 = BitVec.ofNat 64 (remaining + 1)) :
    (markParentPrefix state 10).pc = (if remaining = 0 then (4096+4*2658) else (4096+4*2648)) ∧
      (markParentPrefix state 10).getReg .x6 = BitVec.ofNat 64 remaining := by
  have decrease : state.getReg .x6 - 1 = BitVec.ofNat 64 remaining := by
    rw [count]
    change BitVec.ofNat 64 (remaining + 1) - BitVec.ofNat 64 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) _ _ (by decide) (by omega)]
    rw [Nat.add_sub_cancel]
  have zero : BitVec.ofNat 64 remaining = 0#64 ↔ remaining = 0 := by
    constructor
    · intro h
      exact nat_address_injective (left := remaining) (right := 0) (by omega) (by decide) h
    · rintro rfl
      rfl
  exact ⟨by rw [(mark_parent_post state pc).2.2.2, decrease]; simp [zero],
    (mark_parent_post state pc).2.2.1.trans decrease⟩

private theorem mark_cell_access (node : Nat) (bounded : node < 512) :
    accessValid (BitVec.ofNat 64 (markBase + 8 * node)) 8 = true := by
  apply TwoPermutationPrototype.Opening.aligned_access
  · unfold markBase
    omega
  · unfold markBase MEMORY_BYTES
    omega

/-- Execute the actual entire descending sweep, accounting for every iteration. -/
theorem execute_mark_sweep (state : MachineState) (remaining fuel : Nat)
    (bounded : remaining < 256)
    (pc : state.pc = if remaining = 0 then (4096+4*2658) else (4096+4*2648))
    (base : state.getReg .x26 = BitVec.ofNat 64 markBase)
    (count : state.getReg .x6 = BitVec.ofNat 64 remaining) :
    execute chainedCheckerImage (10 * remaining + fuel) state false =
      (do let result ← execute chainedCheckerImage fuel (markMachine state remaining) false
          return result.charge (10 * remaining) 0) := by
  induction remaining generalizing state with
  | zero => simp [markMachine, Execution.charge]
  | succ remaining ih =>
    have headPC : state.pc = (4096+4*2648) := by simpa using pc
    have ⟨left, right, parent⟩ := mark_addresses state (remaining + 1) base count
    change childrenAddress state = _ at left
    change childrenAddress state + 8#64 = _ at right
    change parentAddress state = _ at parent
    have leftValid : accessValid (childrenAddress state) 8 = true := by
      rw [left]
      exact mark_cell_access _ (by omega)
    have rightValid : accessValid (childrenAddress state + 8#64) 8 = true := by
      rw [right]
      exact mark_cell_access _ (by omega)
    have parentValid : accessValid (parentAddress state) 8 = true := by
      rw [parent]
      exact mark_cell_access _ (by omega)
    have head := execute_mark_parent state headPC (10 * remaining + fuel)
      leftValid rightValid parentValid
    have ⟨nextPC, nextCount⟩ := mark_sweep_pc state remaining (by omega) headPC count
    have nextBase := (mark_parent_post state headPC).2.1.trans base
    rw [show 10 * (remaining + 1) + fuel = 10 + (10 * remaining + fuel) by omega, head,
      ih _ (by omega) nextPC nextBase nextCount]
    simp [markMachine, Execution.charge, Nat.add_assoc, Nat.mul_succ, Nat.add_comm 10]

private theorem observed_mark_update (before after : MachineState) (node other : Nat)
    (bounded : node < 256) (otherBound : other < 512)
    (memory : after.mem = (before.setMem (BitVec.ofNat 64 (markBase + 8 * node))
      (machineMarks before (2 * node) ||| machineMarks before (2 * node + 1))).mem) :
    machineMarks after other = markParent (machineMarks before) node other := by
  have point := congrFun memory (BitVec.ofNat 64 (markBase + 8 * other))
  unfold machineMarks at *
  refine point.trans ?_
  by_cases same : other = node
  · subst other
    simp [markParent, MachineState.setMem, MachineState.getMem]
  · have different : BitVec.ofNat 64 (markBase + 8 * other) ≠
        BitVec.ofNat 64 (markBase + 8 * node) := by
      intro equal
      unfold markBase at equal
      have := nat_address_injective (by omega) (by omega) equal
      omega
    simp [markParent, same, MachineState.setMem, MachineState.getMem, different]

/-- In physical memory, one mark iteration implements the corresponding array update. -/
theorem machine_mark_parent (state : MachineState) (node other : Nat)
    (bounded : node < 256) (otherBound : other < 512) (pc : state.pc = (4096+4*2648))
    (base : state.getReg .x26 = BitVec.ofNat 64 markBase)
    (count : state.getReg .x6 = BitVec.ofNat 64 node) :
    machineMarks (markParentPrefix state 10) other = markParent (machineMarks state) node other := by
  have ⟨left, right, parent⟩ := mark_addresses state node base count
  change childrenAddress state = _ at left
  change childrenAddress state + 8#64 = _ at right
  change parentAddress state = _ at parent
  have memory := (mark_parent_post state pc).1
  rw [right, left, parent] at memory
  exact observed_mark_update state _ node other bounded otherBound memory

/-- Memory after the complete sweep contains the exact occupancy of every cap subtree. -/
theorem machine_mark_sweep (state : MachineState) (groups : List Nat) (remaining : Nat)
    (bounded : remaining < 256)
    (pc : state.pc = if remaining = 0 then (4096+4*2658) else (4096+4*2648))
    (base : state.getReg .x26 = BitVec.ofNat 64 markBase)
    (count : state.getReg .x6 = BitVec.ofNat 64 remaining)
    (finished : ∀ node, remaining < node → node < 512 →
      machineMarks state node = markWord groups node) :
    ∀ node, 0 < node → node < 512 →
      machineMarks (markMachine state remaining) node = markWord groups node := by
  induction remaining generalizing state with
  | zero => exact finished
  | succ remaining ih =>
    have headPC : state.pc = (4096+4*2648) := by simpa using pc
    have ⟨nextPC, nextCount⟩ := mark_sweep_pc state remaining (by omega) headPC count
    have nextBase := (mark_parent_post state headPC).2.1.trans base
    apply ih _ (by omega) nextPC nextBase nextCount
    intro node after inside
    rw [machine_mark_parent state (remaining+1) node bounded inside headPC base count]
    by_cases same : node = remaining + 1
    · subst node
      have children := mark_word_parent groups ⟨remaining + 1, bounded⟩
        (show 0 < remaining + 1 by omega)
      change markWord groups (remaining + 1) =
        markWord groups (2 * (remaining + 1)) ||| markWord groups (2 * (remaining + 1) + 1) at children
      rw [markParent, ite_eq_left rfl, finished _ (by omega) (by omega),
        finished _ (by omega) (by omega), children]
    · rw [markParent, ite_eq_right same, finished _ (by omega) inside]

def startMark (state : MachineState) : MachineState :=
  (state.setReg .x6 255).setPC (4096+4*2648)

theorem execute_start_mark (state : MachineState) (pc : state.pc = (4096+4*2647)) (fuel : Nat) :
    execute chainedCheckerImage (1+fuel) state false =
      (do let result ← execute chainedCheckerImage fuel (startMark state) false
          return result.charge 1 0) := by
  have fetched := cap_fetch state 2647 (.ADDI .x6 .x0 255) (by decide) pc rfl
  have next : ordinaryStep state (.base (.ADDI .x6 .x0 255)) = some (startMark state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, startMark, pc] <;> rfl
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched next]
  rfl

theorem mark_machine_pc (state : MachineState) (remaining : Nat) (bounded : remaining < 256)
    (pc : state.pc = if remaining = 0 then (4096+4*2658) else (4096+4*2648))
    (count : state.getReg .x6 = BitVec.ofNat 64 remaining) :
    (markMachine state remaining).pc = (4096+4*2658) := by
  induction remaining generalizing state with
  | zero => exact pc
  | succ remaining ih =>
    have atLoop : state.pc = (4096+4*2648) := by simpa using pc
    have ⟨tailPC, tailCount⟩ := mark_sweep_pc state remaining (by omega) atLoop count
    exact ih _ (by omega) tailPC tailCount

def startedCap (state : MachineState) := capStart (markMachine (startMark state) 255)

theorem execute_started_cap (state : MachineState) (pc : state.pc = (4096+4*2647)) (fuel : Nat)
    (base : state.getReg .x26 = BitVec.ofNat 64 markBase) :
    execute chainedCheckerImage (2554+fuel) state false =
      (do let result ← execute chainedCheckerImage fuel (startedCap state) false
          return result.charge 2554 0) := by
  have markPC : (startMark state).pc = (4096+4*2648) := rfl
  have bound : 255 < 256 := by decide
  have count : (startMark state).getReg .x6 = BitVec.ofNat 64 255 := by
    simp [startMark, MachineState.getReg_setPC, TwoPermutationPrototype.Opening.getReg_setReg]
  have markBaseReg : (startMark state).getReg .x26 = BitVec.ofNat 64 markBase := by
    simpa [startMark, MachineState.getReg_setPC, TwoPermutationPrototype.Opening.getReg_setReg] using base
  have tailPC := mark_machine_pc (startMark state) 255 bound markPC count
  rw [show 2554+fuel = 1+(10*255+(3+fuel)) by omega, execute_start_mark state pc,
    execute_mark_sweep (startMark state) 255 _ bound markPC markBaseReg count,
    execute_cap_start _ tailPC]
  simp [startedCap, Execution.charge, ← Nat.add_assoc]

open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open TwoPermutationPrototype TwoPermutationPrototype.RV64

attribute [local simp] TwoPermutationPrototype.Opening.getReg_setReg TwoPermutationPrototype.Opening.getReg_setMem MachineState.getReg_setPC
set_option maxRecDepth 4096

theorem mark_parent_register (state : MachineState) (reg : Reg)
    (a : reg ≠ .x6) (b : reg ≠ .x7) (c : reg ≠ .x28) (d : reg ≠ .x29) :
    (markParentPrefix state 10).getReg reg = state.getReg reg := by
  have step (before : MachineState) (i : Fin 10) :
      (execInstrBr before ((TwoPermutationPrototype.Opening.capMarkInstructions.drop 1)[i.val]?.getD .EBREAK)).getReg reg =
        before.getReg reg := by
    fin_cases i
    all_goals simp [TwoPermutationPrototype.Opening.capMarkInstructions, execInstrBr, Ne.symm a, Ne.symm b, Ne.symm c, Ne.symm d]
    all_goals (by_cases held : before.getReg .x6 = 0#64 <;> simp [held])
  have keeps (n : Nat) (bound : n ≤ 10) :
      (markParentPrefix state n).getReg reg = state.getReg reg := by
    induction n with
    | zero => simp [markParentPrefix]
    | succ n ih =>
      rw [mark_prefix_succ _ n (by omega)]
      exact (step _ ⟨n, by omega⟩).trans (ih (by omega))
  exact keeps 10 (by decide)

attribute [local irreducible] markMachine

theorem mark_sweep_register (state : MachineState) (remaining : Nat) (reg : Reg)
    (a : reg ≠ .x6) (b : reg ≠ .x7) (c : reg ≠ .x28) (d : reg ≠ .x29) :
    (markMachine state remaining).getReg reg = state.getReg reg := by
  induction remaining generalizing state with
  | zero => simp [markMachine]
  | succ remaining ih =>
    rw [markMachine]
    change (markMachine (markParentPrefix state 10) remaining).getReg reg = _
    exact (ih (markParentPrefix state 10)).trans (mark_parent_register state reg a b c d)

private theorem mark_parent_address_before_write (state : MachineState) :
    (markParentPrefix state 7).getReg .x7 = parentAddress state := by
  simp [markParentPrefix, parentAddress, TwoPermutationPrototype.Opening.capMarkInstructions, execInstrBr]

private theorem mark_parent_keeps_word (state : MachineState) (address : Word)
    (diff : address ≠ parentAddress state) :
    (markParentPrefix state 10).getMem address = state.getMem address := by
  have preserve (step : Nat) (inside : step < 10) :
      (markParentPrefix state (step+1)).getMem address = (markParentPrefix state step).getMem address := by
    rw [mark_prefix_succ _ _ inside]
    interval_cases step
    all_goals simp [TwoPermutationPrototype.Opening.capMarkInstructions, execInstrBr, signExtend12,
      mark_parent_address_before_write, diff]
    all_goals split <;> exact MachineState.getMem_setPC
  have fold (count : Nat) (within : count ≤ 10) :
      (markParentPrefix state count).getMem address = state.getMem address := by
    induction count with
    | zero => simp [markParentPrefix]
    | succ count ih => exact (preserve count (by omega)).trans (ih (by omega))
  exact fold 10 (by decide)

theorem mark_sweep_getMem (state : MachineState) (remaining : Nat)
    (bounded : remaining < 256) (pc : state.pc = if remaining = 0 then (4096+4*2658) else (4096+4*2648))
    (base : state.getReg .x26 = BitVec.ofNat 64 TwoPermutationPrototype.Opening.markBase)
    (count : state.getReg .x6 = BitVec.ofNat 64 remaining)
    (address : Word) (outside : ∀ node, 0 < node → node < 256 →
      address ≠ BitVec.ofNat 64 (TwoPermutationPrototype.Opening.markBase+8*node)) :
    (markMachine state remaining).getMem address = state.getMem address := by
  induction remaining generalizing state with
  | zero => simp [markMachine]
  | succ remaining ih =>
    have start : state.pc = (4096+4*2648) := by simpa using pc
    have ⟨tailPC, counter⟩ := mark_sweep_pc state remaining (by omega) start count
    obtain ⟨mem, baseReg, _, _⟩ := mark_parent_post state start
    have addressAt := (TwoPermutationPrototype.Opening.mark_addresses state (remaining+1) base count).2.2
    change parentAddress state = _ at addressAt
    have diff : address ≠ parentAddress state :=
      fun same => outside (remaining+1) (by omega) bounded (same.trans addressAt)
    rw [markMachine]
    exact (ih (markParentPrefix state 10) (by omega) tailPC (baseReg.trans base) counter).trans
      (mark_parent_keeps_word state address diff)


theorem mark_sweep_word (state : MachineState) (remaining : Nat)
    (bounded : remaining < 256) (pc : state.pc = if remaining = 0 then (4096+4*2658) else (4096+4*2648))
    (base : state.getReg .x26 = BitVec.ofNat 64 TwoPermutationPrototype.Opening.markBase)
    (count : state.getReg .x6 = BitVec.ofNat 64 remaining)
    (word : Nat) (wordBound : word < 2^61) (outside : word < 513 ∨ 768 ≤ word) :
    memoryView (markMachine state remaining) word = memoryView state word := by
  apply mark_sweep_getMem state remaining bounded pc base count
  intro node low high
  have atNode : BitVec.ofNat 64 (TwoPermutationPrototype.Opening.markBase+8*node) = wordAddress (512+node) := by
    unfold TwoPermutationPrototype.Opening.markBase wordAddress
    congr 1
    omega
  rw [atNode]
  intro same
  have hit := wordAddress_injective_of_bound wordBound (by omega) same
  omega
structure CapMarkReady (groups : List Nat) (state : MachineState) (pointer finish : Nat) : Prop where
  pc : state.pc=4096+4*2647
  selector : state.getReg .x5=0#64
  roots : state.getReg .x25=16384#64
  markBase : state.getReg .x26=4096#64
  capLeaves : state.getReg .x27=256#64
  marked : ∀ node, 256≤node → node<512 → memoryView state (512+node)=TwoPermutationPrototype.Opening.markWord groups node
  cursor : state.getReg .x21=BitVec.ofNat 64 pointer
  endReg : state.getReg .x22=BitVec.ofNat 64 finish
  above : 32768≤pointer
  even : pointer%2=0
  endBound : finish≤MEMORY_BYTES
  room : pointer+30*(capFrontierNodes groups 1 8).length≤finish

def capMarkedState (state : MachineState) := markMachine (startMark state) 255

theorem cap_marked_register (state : MachineState) (reg : Reg)
    (a : reg≠.x6) (b : reg≠.x7) (c : reg≠.x28) (d : reg≠.x29) :
    (capMarkedState state).getReg reg=state.getReg reg := by
  exact (mark_sweep_register (startMark state) 255 reg a b c d).trans
    (by simp [startMark,Ne.symm a])

theorem cap_mark_ready {groups : List Nat} {state : MachineState} {pointer finish : Nat}
    (ready : CapMarkReady groups state pointer finish) :
    CapDfsEntryReady groups (capMarkedState state) pointer finish := by
  have startPC : (startMark state).pc=4096+4*2648 := rfl
  have count : (startMark state).getReg .x6=255#64 := by simp [startMark]
  have base : (startMark state).getReg .x26=BitVec.ofNat 64 TwoPermutationPrototype.Opening.markBase := by
    simpa [startMark,TwoPermutationPrototype.Opening.markBase] using ready.markBase
  have marks := machine_mark_sweep (startMark state) groups 255 (by decide) startPC base count
    (by
      intro node positive bounded
      have convert : machineMarks (startMark state) node=memoryView state (512+node) := by
        simp [machineMarks,startMark,memoryView,TwoPermutationPrototype.Opening.markBase,wordAddress,
          Nat.mul_add,MachineState.getMem]
      exact convert.trans (ready.marked node (by omega) bounded))
  refine ⟨mark_machine_pc (startMark state) 255 (by decide) startPC count,
    (cap_marked_register state .x5 (by decide) (by decide) (by decide) (by decide)).trans ready.selector,
    (cap_marked_register state .x25 (by decide) (by decide) (by decide) (by decide)).trans ready.roots,
    (cap_marked_register state .x26 (by decide) (by decide) (by decide) (by decide)).trans ready.markBase,
    (cap_marked_register state .x27 (by decide) (by decide) (by decide) (by decide)).trans ready.capLeaves,?_,
    (cap_marked_register state .x21 (by decide) (by decide) (by decide) (by decide)).trans ready.cursor,
    (cap_marked_register state .x22 (by decide) (by decide) (by decide) (by decide)).trans ready.endReg,
    ready.above,ready.even,ready.endBound,ready.room⟩
  intro node positive bounded
  simpa [machineMarks,memoryView,TwoPermutationPrototype.Opening.markBase,wordAddress,Nat.mul_add,capMarkedState]
    using marks node positive bounded

theorem cap_mark_execution (state : MachineState) (pc : state.pc=4096+4*2647)
    (base : state.getReg .x26=4096#64) (fuel : Nat) :
    execute chainedCheckerImage (2551+fuel) state false=
      (do let result ← execute chainedCheckerImage fuel (capMarkedState state) false
          return result.charge 2551 0) := by
  have startPC : (startMark state).pc=4096+4*2648 := rfl
  have count : (startMark state).getReg .x6=255#64 := by simp [startMark]
  have startBase : (startMark state).getReg .x26=BitVec.ofNat 64 TwoPermutationPrototype.Opening.markBase := by
    simpa [startMark,TwoPermutationPrototype.Opening.markBase] using base
  rw [show 2551+fuel=1+(10*255+fuel) by omega,execute_start_mark state pc,
    execute_mark_sweep (startMark state) 255 _ (by decide) startPC startBase count]
  simp [capMarkedState,Execution.charge,←Nat.add_assoc]

theorem cap_mark_dfs_execution {groups : List Nat} {state : MachineState} {pointer finish : Nat}
    (ready : CapMarkReady groups state pointer finish) (fuel : Nat) :
    execute chainedCheckerImage (2556+capTreeSteps groups 1 8+fuel) state false=
      (do let out ← capDfsEntryTrace groups (capMarkedState state)
          let result ← execute chainedCheckerImage fuel out false
          return result.charge (2556+capTreeSteps groups 1 8+7*TwoPermutationPrototype.Checker.capHashCount groups 1 8)
            (TwoPermutationPrototype.Checker.capHashCount groups 1 8)) := by
  rw [show 2556+capTreeSteps groups 1 8+fuel=2551+(5+capTreeSteps groups 1 8+fuel) by omega,
    cap_mark_execution state ready.pc ready.markBase,cap_entry_execution (cap_mark_ready ready)]
  simp only [bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support
  intro out _
  apply bind_congr_of_forall_mem_support
  intro result _
  congr 1
  cases result
  (simp [Execution.charge,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]; omega)

theorem cap_mark_dfs_limits (groups : List Nat) :
    2556+capTreeSteps groups 1 8≤61246 ∧ TwoPermutationPrototype.Checker.capHashCount groups 1 8≤255 ∧
      2556+capTreeSteps groups 1 8+7*TwoPermutationPrototype.Checker.capHashCount groups 1 8≤63031 := by
  have := cap_tree_root_limits groups
  omega

end CommitGolfCandidate.Chained.Native.CheckerCap.Visit
