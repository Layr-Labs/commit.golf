import CommitGolfCandidate.QuadCheckerMeasure
import CommitGolfCandidate.QuadCheckerSetup
import CommitGolfCandidate.QuadCheckerExit
import CommitGolfCandidate.QuadInputFrame

/-! The donor header (words 1-21) run from the cap wrapper's exit. The wrapper returns to word 1
with `t1 = 1424` and every other register equal to the loader's registers for the expanded input
`target`, whose proof is exactly `1424 k` bytes. The header reads only registers and writes no
memory, so it reaches the donor's record cursor for `target` with the wrapper's memory. -/
namespace TwoPermutationPrototype.Quad.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
attribute [local irreducible] execute

/-- The machine state at word 1 after the wrapper accepted a cap proof. -/
structure HeaderStart (target : CheckInput) (state : MachineState) : Prop where
  pc : state.pc = BitVec.ofNat 64 4100
  factor : state.getReg .x6 = BitVec.ofNat 64 1424
  regs : ∀ r, r ≠ .x6 → state.getReg r = (loaderReference.initialState .check target).getReg r
  exact : target.proof.length = 1424*target.positions.card

private abbrev measured (state : MachineState) := measureState state
private abbrev shortChecked (state : MachineState) := CheckGuard.short.next (measured state)
private abbrev emptyChecked (state : MachineState) := CheckGuard.empty.next (shortChecked state)

private theorem measured_view {target : CheckInput} {state : MachineState} (start : HeaderStart target state) :
    (measured state).pc = 4104 ∧
      (measured state).getReg .x6 = BitVec.ofNat 64 (1424*target.positions.card) ∧
      (measured state).mem = state.mem ∧
      ∀ r, r ≠ .x6 → (measured state).getReg r = (loaderReference.initialState .check target).getReg r := by
  obtain ⟨pc, product, memory, kept⟩ := measure_post state start.pc
  obtain ⟨_,_,_,_,_,count,_⟩ := check_initial_registers target
  refine ⟨pc, ?_, memory, fun r a => (kept r a).trans (start.regs r a)⟩
  rw [product, start.regs .x16 (by decide), count, start.factor, ← BitVec.ofNat_mul, Nat.mul_comm]

private theorem measure_hop {target : CheckInput} {state : MachineState} (start : HeaderStart target state) :
    Hop state (measured state) 1 4 :=
  execute_measure state start.pc

private theorem short_hop {target : CheckInput} {state : MachineState} (start : HeaderStart target state) :
    Hop state (shortChecked state) 2 5 :=
  (measure_hop start).thenDo (check_guard_hop .short (measured state) (measured_view start).1)

private theorem short_pc {target : CheckInput} {state : MachineState} (start : HeaderStart target state) :
    (shortChecked state).pc = 4108 := by
  obtain ⟨pc, required, _, kept⟩ := measured_view start
  obtain ⟨_,_,_,_,_,_,length⟩ := check_initial_registers target
  rw [check_short_guard _ pc, required, kept .x17 (by decide), length, start.exact]
  simp

private theorem empty_hop {target : CheckInput} {state : MachineState} (start : HeaderStart target state) :
    Hop state (emptyChecked state) 3 6 :=
  (short_hop start).thenDo (check_guard_hop .empty _ (short_pc start))

private theorem empty_pc {target : CheckInput} {state : MachineState} (start : HeaderStart target state) :
    (emptyChecked state).pc = if target.positions.card = 0 then 0x15a0 else 0x1010 := by
  have count := (check_guard_register .short (measured state) .x16).trans
    (((measured_view start).2.2.2 .x16 (by decide)).trans (check_initial_registers target).2.2.2.2.2.1)
  have cardinal := checker_positions_bound target
  have same : BitVec.ofNat 64 target.positions.card = (0 : Word) ↔ target.positions.card = 0 := by
    rw [← BitVec.toNat_inj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : target.positions.card < 2^64)]
    rfl
  rw [check_empty_guard _ (short_pc start), count]
  simp only [same]

private theorem empty_keeps {target : CheckInput} {state : MachineState} (start : HeaderStart target state)
    (reg : Reg) (a : reg ≠ .x6) :
    (emptyChecked state).getReg reg = (loaderReference.initialState .check target).getReg reg :=
  (check_guard_register .empty (shortChecked state) reg).trans
    ((check_guard_register .short (measured state) reg).trans ((measured_view start).2.2.2 reg a))

/-- No positions: the donor's empty-opening exit accepts the (empty) expanded proof. -/
theorem wrapped_header_empty {target : CheckInput} {state : MachineState} (start : HeaderStart target state)
    (empty : target.positions.card = 0) (fuel : Nat) :
    ∃ result : Execution,
      execute packedImage (7+fuel) state false = pure result ∧ result.exit = .success ∧ result.oracleCalls = 0 := by
  have pc := (empty_pc start).trans (ite_eq_left empty)
  obtain ⟨result, accepts, _, calls, finished⟩ := execute_empty_check _ pc fuel
  have run := empty_hop start (4+fuel)
  rw [finished] at run
  refine ⟨result.charge 6 0, ?_, ?_, by simp [Execution.charge, calls]⟩
  · rw [show 7+fuel = 3+(4+fuel) by omega]
    simpa only [pure_bind] using run
  · apply accepts.mpr
    rw [empty_keeps start .x17 (by decide), (check_initial_registers target).2.2.2.2.2.2, start.exact, empty]

/-- At least one position: the donor's record cursor for the expanded input, memory untouched. -/
theorem wrapped_header_positive {target : CheckInput} {state : MachineState} (start : HeaderStart target state)
    (nonempty : target.positions.card ≠ 0) :
    ∃ next : MachineState, RecordCursor target 0 next ∧ next.mem = state.mem ∧ Hop state next 21 24 := by
  let next := checkPreparePrefix (emptyChecked state) 18
  have here := (empty_pc start).trans (ite_eq_right nonempty)
  have usable := check_prepare_view _ here
  have code := (empty_hop start).thenDo (check_prepare_hop _ here)
  obtain ⟨_,root,indices,values,proof,count,length⟩ := check_initial_registers target
  have keep (r : Reg) (a : r ≠ .x6) := empty_keeps start r a
  refine ⟨next,⟨?_,?_,?_,?_,?_,usable.tag,?_,usable.length,?_,usable.digest,
    usable.pair,usable.capRoots,usable.marks,usable.capCount,usable.selector,usable.nonceScratch⟩,?_,code⟩
  · exact usable.pc.trans (ite_eq_right (Ne.symm nonempty)).symm
  · exact usable.index.trans ((keep .x13 (by decide)).trans indices)
  · rw [usable.value,keep .x14 (by decide),values]
    rfl
  · exact usable.proof.trans ((keep .x15 (by decide)).trans proof)
  · exact usable.count.trans ((keep .x16 (by decide)).trans count)
  · exact usable.root.trans ((keep .x11 (by decide)).trans root)
  · rw [usable.proofEnd,keep .x15 (by decide),keep .x17 (by decide),proof,length]
    change BitVec.ofNat 64 10804535392+BitVec.ofNat 64 target.proof.length = _
    rw [← BitVec.ofNat_add]
  · exact usable.memory.trans ((check_guard_memory .empty (shortChecked state)).trans
      ((check_guard_memory .short (measured state)).trans (measured_view start).2.2.1))

end TwoPermutationPrototype.Quad.Checker
