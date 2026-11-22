import CommitGolfCandidate.TwoPermutationPackedCheckerMeasure
import CommitGolfCandidate.TwoPermutationPackedCheckerSetup
import CommitGolfCandidate.TwoPermutationPackedCheckerExit
import CommitGolfCandidate.TwoPermutationPackedCheckCursor

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (check_initial_registers checker_positions_bound)
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
attribute [local irreducible] execute

/-- Register interface at the first original checker instruction after conversion. -/
structure HeaderEntry (input : CheckInput) where
  state : MachineState
  factor : state.getReg .x6=534
  args : state.pc=4100 ∧ state.getReg .x11=4294971392 ∧ state.getReg .x13=9395245088 ∧
    state.getReg .x14=9529462880 ∧ state.getReg .x15=13824430176 ∧
    state.getReg .x16=BitVec.ofNat 64 input.positions.card ∧ state.getReg .x17=BitVec.ofNat 64 input.proof.length

private abbrev measured (input : CheckInput) (entry : HeaderEntry input) := measureState entry.state
private abbrev shortChecked (input : CheckInput) (entry : HeaderEntry input) := CheckGuard.short.next (measured input entry)
private abbrev emptyChecked (input : CheckInput) (entry : HeaderEntry input) := CheckGuard.empty.next (shortChecked input entry)

private abbrev measured_view (input : CheckInput) (entry : HeaderEntry input) := measure_post entry.state entry.args.1 entry.factor

private theorem measure_hop (input : CheckInput) (entry : HeaderEntry input) : Hop entry.state (measured input entry) 1 4 :=
  execute_measure entry.state entry.args.1

private theorem short_hop (input : CheckInput) (entry : HeaderEntry input) : Hop entry.state (shortChecked input entry) 2 5 :=
  (measure_hop input entry).thenDo (check_guard_hop .short (measured input entry) (measured_view input entry).1)

private theorem short_pc (input : CheckInput) (entry : HeaderEntry input) (fits : input.proof.length ≤ 8959041024) :
    (shortChecked input entry).pc = if input.proof.length < 534*input.positions.card then 0x15b0 else 4108 := by
  obtain ⟨_,_,_,_,_,count,length⟩ := entry.args
  obtain ⟨pc,required,_,kept⟩ := measured_view input entry
  have requiredEq : (measured input entry).getReg .x6 = BitVec.ofNat 64 (534*input.positions.card) := by
    rw [required, count]
    change BitVec.ofNat 64 input.positions.card * BitVec.ofNat 64 534 = _
    rw [← BitVec.ofNat_mul, Nat.mul_comm]
  have lengthEq : (measured input entry).getReg .x17 = BitVec.ofNat 64 input.proof.length :=
    (kept .x17 (by decide)).trans length
  have maximum := checker_positions_bound input
  have size : input.proof.length < 2^64 := by omega
  have countSize : 534*input.positions.card < 2^64 := by omega
  rw [check_short_guard _ pc,requiredEq,lengthEq]
  have same : BitVec.ofNat 64 input.proof.length < BitVec.ofNat 64 (534*input.positions.card) ↔
      input.proof.length < 534*input.positions.card := by
    change (BitVec.ofNat 64 input.proof.length).toNat < (BitVec.ofNat 64 (534*input.positions.card)).toNat ↔ _
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt size,Nat.mod_eq_of_lt countSize]
  simp only [same]

private theorem empty_hop (input : CheckInput) (entry : HeaderEntry input) (fits : input.proof.length ≤ 8959041024)
    (long : 534*input.positions.card ≤ input.proof.length) :
    Hop entry.state (emptyChecked input entry) 3 6 := by
  have pc := (short_pc input entry fits).trans (ite_eq_right (Nat.not_lt.mpr long))
  exact (short_hop input entry).thenDo (check_guard_hop .empty _ pc)

private theorem empty_pc (input : CheckInput) (entry : HeaderEntry input) (fits : input.proof.length ≤ 8959041024)
    (long : 534*input.positions.card ≤ input.proof.length) :
    (emptyChecked input entry).pc = if input.positions.card = 0 then 0x15a0 else 0x1010 := by
  have start := (short_pc input entry fits).trans (ite_eq_right (Nat.not_lt.mpr long))
  have count := (check_guard_register .short (measured input entry) .x16).trans
    (((measured_view input entry).2.2.2 .x16 (by decide)).trans entry.args.2.2.2.2.2.1)
  have cardinal := checker_positions_bound input
  have same : BitVec.ofNat 64 input.positions.card = (0 : Word) ↔ input.positions.card = 0 := by
    rw [← BitVec.toNat_inj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : input.positions.card < 2^64)]
    rfl
  rw [check_empty_guard _ start,count]
  simp only [same]

private theorem empty_keeps (input : CheckInput) (entry : HeaderEntry input) (reg : Reg) (a : reg ≠ .x6) :
    (emptyChecked input entry).getReg reg = entry.state.getReg reg :=
  (check_guard_register .empty (shortChecked input entry) reg).trans
    ((check_guard_register .short (measured input entry) reg).trans ((measured_view input entry).2.2.2 reg a))

theorem header_empty (input : CheckInput) (entry : HeaderEntry input) (fits : input.proof.length ≤ 8959041024)
    (empty : input.positions.card = 0) (extra : Nat) :
    ∃ result : Execution,
      execute packedImage (7+extra) entry.state false = pure result ∧
      result.exit ≠ .unfinished ∧ (input.proof.length = 0 → result.exit = .success) := by
  have long : 534*input.positions.card ≤ input.proof.length := by omega
  have pc := (empty_pc input entry fits long).trans (ite_eq_left empty)
  obtain ⟨result,accepts,ends,_,finished⟩ := execute_empty_check _ pc extra
  have run := empty_hop input entry fits long (4+extra)
  rw [finished] at run
  refine ⟨result.charge 6 0, ?_, ends, ?_⟩
  · simpa only [pure_bind,show 3+(4+extra)=7+extra by omega] using run
  · intro noProof
    apply accepts.mpr
    rw [empty_keeps input entry .x17 (by decide),
      entry.args.2.2.2.2.2.2,noProof]

theorem header_positive (input : CheckInput) (entry : HeaderEntry input) (fits : input.proof.length ≤ 8959041024)
    (nonempty : input.positions.card ≠ 0) (long : 534*input.positions.card ≤ input.proof.length) :
    ∃ state : MachineState,
      RecordCursor input 0 state ∧ state.mem = entry.state.mem ∧ Hop entry.state state 21 24 := by
  let state := checkPreparePrefix (emptyChecked input entry) 18
  have here := (empty_pc input entry fits long).trans (ite_eq_right nonempty)
  have usable := check_prepare_view _ here
  have code := (empty_hop input entry fits long).thenDo (check_prepare_hop _ here)
  obtain ⟨_,root,indices,values,proof,count,length⟩ := entry.args
  have keep (r : Reg) (a : r ≠ .x6) := empty_keeps input entry r a
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
    change BitVec.ofNat 64 13824430176+BitVec.ofNat 64 input.proof.length = _
    rw [← BitVec.ofNat_add]
  · exact usable.memory.trans ((check_guard_memory .empty (shortChecked input entry)).trans
      ((check_guard_memory .short (measured input entry)).trans (measured_view input entry).2.2.1))

end TwoPermutationPrototype.Packed.Checker
