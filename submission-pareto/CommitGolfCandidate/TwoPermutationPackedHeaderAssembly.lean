import CommitGolfCandidate.TwoPermutationPackedCheckerMeasure
import CommitGolfCandidate.TwoPermutationPackedCheckerSetup
import CommitGolfCandidate.TwoPermutationPackedCheckerExit
import CommitGolfCandidate.TwoPermutationPackedCheckCursor
import CommitGolfCandidate.TwoPermutationPackedUnpackRun
import CommitGolfCandidate.TwoPermutationPackedCapBytes

/-! The checker header after the unpacking wrapper: it starts at word 2 from any state with
the registers and bytes of the measured initial state of the (unpacked) input. -/
namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (check_initial_registers checker_positions_bound)
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
attribute [local irreducible] execute

private abbrev headerInput (input : CheckInput) := Assembly.submission.initialState .check input
private abbrev shortChecked (m : MachineState) := CheckGuard.short.next m
private abbrev emptyChecked (m : MachineState) := CheckGuard.empty.next (shortChecked m)

private theorem short_hop (input : CheckInput) (m : MachineState) (view : UnpackedView input m) :
    Hop m (shortChecked m) 1 1 :=
  check_guard_hop .short m view.pc

private theorem short_pc (input : CheckInput) (m : MachineState) (view : UnpackedView input m)
    (fits : input.proof.length ≤ 2^33) :
    (shortChecked m).pc = if input.proof.length < 498*input.positions.card then 0x15b0 else 4108 := by
  obtain ⟨_,_,_,_,_,count,length⟩ := check_initial_registers input
  have requiredEq : m.getReg .x6 = BitVec.ofNat 64 (498*input.positions.card) := by
    rw [view.factor, count]
    change BitVec.ofNat 64 input.positions.card * BitVec.ofNat 64 498 = _
    rw [← BitVec.ofNat_mul, Nat.mul_comm]
  have lengthEq : m.getReg .x17 = BitVec.ofNat 64 input.proof.length :=
    (view.regs .x17 (by decide)).trans length
  have maximum := checker_positions_bound input
  have size : input.proof.length < 2^64 := by omega
  have countSize : 498*input.positions.card < 2^64 := by omega
  rw [check_short_guard _ view.pc,requiredEq,lengthEq]
  have same : BitVec.ofNat 64 input.proof.length < BitVec.ofNat 64 (498*input.positions.card) ↔
      input.proof.length < 498*input.positions.card := by
    change (BitVec.ofNat 64 input.proof.length).toNat < (BitVec.ofNat 64 (498*input.positions.card)).toNat ↔ _
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt size,Nat.mod_eq_of_lt countSize]
  simp only [same]

private theorem empty_hop (input : CheckInput) (m : MachineState) (view : UnpackedView input m)
    (fits : input.proof.length ≤ 2^33) (long : 498*input.positions.card ≤ input.proof.length) :
    Hop m (emptyChecked m) 2 2 := by
  have pc := (short_pc input m view fits).trans (ite_eq_right (Nat.not_lt.mpr long))
  exact (short_hop input m view).thenDo (check_guard_hop .empty _ pc)

private theorem empty_pc (input : CheckInput) (m : MachineState) (view : UnpackedView input m)
    (fits : input.proof.length ≤ 2^33) (long : 498*input.positions.card ≤ input.proof.length) :
    (emptyChecked m).pc = if input.positions.card = 0 then 0x15a0 else 0x1010 := by
  have start := (short_pc input m view fits).trans (ite_eq_right (Nat.not_lt.mpr long))
  have count := (check_guard_register .short m .x16).trans
    ((view.regs .x16 (by decide)).trans (check_initial_registers input).2.2.2.2.2.1)
  have cardinal := checker_positions_bound input
  have same : BitVec.ofNat 64 input.positions.card = (0 : Word) ↔ input.positions.card = 0 := by
    rw [← BitVec.toNat_inj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : input.positions.card < 2^64)]
    rfl
  rw [check_empty_guard _ start,count]
  simp only [same]

private theorem empty_keeps (input : CheckInput) (m : MachineState) (view : UnpackedView input m)
    (reg : Reg) (a : reg ≠ .x6) :
    (emptyChecked m).getReg reg = (headerInput input).getReg reg :=
  (check_guard_register .empty (shortChecked m) reg).trans
    ((check_guard_register .short m reg).trans (view.regs reg a))

theorem header_empty (input : CheckInput) (m : MachineState) (view : UnpackedView input m)
    (fits : input.proof.length ≤ 2^33) (empty : input.positions.card = 0) (fuel : Nat) (enough : 6 ≤ fuel) :
    ∃ result : Execution,
      execute packedImage fuel m false = pure result ∧
      result.exit ≠ .unfinished ∧ (input.proof.length = 0 → result.exit = .success) := by
  have long : 498*input.positions.card ≤ input.proof.length := by omega
  have pc := (empty_pc input m view fits long).trans (ite_eq_left empty)
  obtain ⟨result,accepts,ends,_,finished⟩ := execute_empty_check _ pc (fuel-6)
  have run := empty_hop input m view fits long (4+(fuel-6))
  rw [finished, show 2+(4+(fuel-6)) = fuel by omega] at run
  refine ⟨result.charge 2 0, ?_, ends, ?_⟩
  · simpa only [pure_bind] using run
  · intro noProof
    apply accepts.mpr
    rw [empty_keeps input m view .x17 (by decide),
      (check_initial_registers input).2.2.2.2.2.2,noProof]

theorem header_short (input : CheckInput) (m : MachineState) (view : UnpackedView input m)
    (fits : input.proof.length ≤ 2^33) (short : input.proof.length < 498*input.positions.card)
    (fuel : Nat) (enough : 4 ≤ fuel) :
    ∃ result : Execution,
      execute packedImage fuel m false = pure result ∧ result.exit = .failure := by
  have failed := (short_pc input m view fits).trans (ite_eq_left short)
  have abort := execute_header_reject _ failed (fuel-4)
  have run := short_hop input m view (3+(fuel-4))
  rw [abort, show 1+(3+(fuel-4)) = fuel by omega] at run
  exact ⟨_,by simpa only [pure_bind] using run,rfl⟩

theorem header_positive (input : CheckInput) (m : MachineState) (view : UnpackedView input m)
    (fits : input.proof.length ≤ 2^33)
    (nonempty : input.positions.card ≠ 0) (long : 498*input.positions.card ≤ input.proof.length) :
    ∃ state : MachineState,
      RecordCursor input 0 state ∧ (∀ word, memoryView state word = memoryView (headerInput input) word) ∧
        Hop m state 20 20 := by
  let state := checkPreparePrefix (emptyChecked m) 18
  have here := (empty_pc input m view fits long).trans (ite_eq_right nonempty)
  have usable := check_prepare_view _ here
  have code := (empty_hop input m view fits long).thenDo (check_prepare_hop _ here)
  obtain ⟨_,root,indices,values,proof,count,length⟩ := check_initial_registers input
  have keep (r : Reg) (a : r ≠ .x6) := empty_keeps input m view r a
  refine ⟨state,⟨?_,?_,?_,?_,?_,usable.tag,?_,usable.length,?_,usable.digest,
    usable.pair,usable.capRoots,usable.marks,usable.capCount,usable.selector,usable.nonceScratch⟩,?_,code⟩
  · exact usable.pc.trans (ite_eq_right (Ne.symm nonempty)).symm
  · exact usable.index.trans ((keep .x13 (by decide)).trans indices)
  · rw [usable.value,keep .x14 (by decide),values]
    rfl
  · exact usable.proof.trans ((keep .x15 (by decide)).trans proof)
  · exact usable.count.trans ((keep .x16 (by decide)).trans count)
  · exact usable.root.trans ((keep .x11 (by decide)).trans root)
  · rw [usable.proofEnd,keep .x15 (by decide),keep .x17 (by decide),proof,length]
    change BitVec.ofNat 64 10334769248+BitVec.ofNat 64 input.proof.length = _
    rw [← BitVec.ofNat_add]
  · have memory : state.mem = m.mem := usable.memory.trans ((check_guard_memory .empty (shortChecked m)).trans
      (check_guard_memory .short m))
    intro word
    apply word_eq_of_byte_frame
    intro i _
    rw [getByte_of_mem memory]
    exact view.bytes nonempty _

end TwoPermutationPrototype.Packed.Checker
