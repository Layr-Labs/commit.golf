import CommitGolfCandidate.R1bCheckFront
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

variable {input : CheckInput} {st : MachineState}
private abbrev measured (h : Header input st) := measureState st
private abbrev shortChecked (h : Header input st) := CheckGuard.short.next (measured h)
private abbrev emptyChecked (h : Header input st) := CheckGuard.empty.next (shortChecked h)
private abbrev measured_view (h : Header input st) := measure_post st h.pc h.factor

private theorem measure_hop (h : Header input st) : Hop st (measured h) 1 4 :=
  execute_measure st h.pc

private theorem short_hop (h : Header input st) : Hop st (shortChecked h) 2 5 :=
  (measure_hop h).thenDo (check_guard_hop .short (measured h) (measured_view h).1)

private theorem short_pc (h : Header input st) (fits : input.proof.length ≤ 8388615680) :
    (shortChecked h).pc = if input.proof.length < 500*input.positions.card then 0x15b0 else 4108 := by
  have count:=h.count
  have length:=h.length
  obtain ⟨pc,required,_,kept⟩ := measured_view h
  have requiredEq : (measured h).getReg .x6 = BitVec.ofNat 64 (500*input.positions.card) := by
    rw [required, count]
    change BitVec.ofNat 64 input.positions.card * BitVec.ofNat 64 500 = _
    rw [← BitVec.ofNat_mul, Nat.mul_comm]
  have lengthEq : (measured h).getReg .x17 = BitVec.ofNat 64 input.proof.length :=
    (kept .x17 (by decide)).trans length
  have maximum := checker_positions_bound input
  have size : input.proof.length < 2^64 := by omega
  have countSize : 500*input.positions.card < 2^64 := by omega
  rw [check_short_guard _ pc,requiredEq,lengthEq]
  have same : BitVec.ofNat 64 input.proof.length < BitVec.ofNat 64 (500*input.positions.card) ↔
      input.proof.length < 500*input.positions.card := by
    change (BitVec.ofNat 64 input.proof.length).toNat < (BitVec.ofNat 64 (500*input.positions.card)).toNat ↔ _
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt size,Nat.mod_eq_of_lt countSize]
  simp only [same]

private theorem empty_hop (h : Header input st) (fits : input.proof.length ≤ 8388615680)
    (long : 500*input.positions.card ≤ input.proof.length) :
    Hop st (emptyChecked h) 3 6 := by
  have pc := (short_pc h fits).trans (ite_eq_right (Nat.not_lt.mpr long))
  exact (short_hop h).thenDo (check_guard_hop .empty _ pc)

private theorem empty_pc (h : Header input st) (fits : input.proof.length ≤ 8388615680)
    (long : 500*input.positions.card ≤ input.proof.length) :
    (emptyChecked h).pc = if input.positions.card = 0 then 0x15a0 else 0x1010 := by
  have start := (short_pc h fits).trans (ite_eq_right (Nat.not_lt.mpr long))
  have count := (check_guard_register .short (measured h) .x16).trans
    (((measured_view h).2.2.2 .x16 (by decide)).trans h.count)
  have cardinal := checker_positions_bound input
  have same : BitVec.ofNat 64 input.positions.card = (0 : Word) ↔ input.positions.card = 0 := by
    rw [← BitVec.toNat_inj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : input.positions.card < 2^64)]
    rfl
  rw [check_empty_guard _ start,count]
  simp only [same]

private theorem empty_keeps (h : Header input st) (reg : Reg) (a : reg ≠ .x6) :
    (emptyChecked h).getReg reg = st.getReg reg :=
  (check_guard_register .empty (shortChecked h) reg).trans
    ((check_guard_register .short (measured h) reg).trans ((measured_view h).2.2.2 reg a))

theorem header_empty (h : Header input st) (fuel : Nat) (enough : 7≤fuel) (fits : input.proof.length ≤ 8388615680)
    (empty : input.positions.card = 0) :
    ∃ result : Execution,
      execute packedImage fuel st false = pure result ∧
      result.exit ≠ .unfinished ∧ (input.proof.length = 0 → result.exit = .success) := by
  have long : 500*input.positions.card ≤ input.proof.length := by omega
  have pc := (empty_pc h fits long).trans (ite_eq_left empty)
  obtain ⟨result,accepts,ends,_,finished⟩ := execute_empty_check _ pc (fuel-7)
  have run := empty_hop h fits long (4+(fuel-7))
  rw [finished] at run
  refine ⟨result.charge 6 0, ?_, ends, ?_⟩
  · rw [show fuel=3+(4+(fuel-7)) by omega];simpa only [pure_bind] using run
  · intro noProof
    apply accepts.mpr
    rw [empty_keeps h .x17 (by decide),
      h.length,noProof]

theorem header_short (h : Header input st) (fuel : Nat) (enough : 7≤fuel) (fits : input.proof.length ≤ 8388615680)
    (short : input.proof.length < 500*input.positions.card) :
    ∃ result : Execution,
      execute packedImage fuel st false = pure result ∧ result.exit = .failure := by
  have failed := (short_pc h fits).trans (ite_eq_left short)
  have abort := execute_header_reject _ failed (fuel-5)
  have run := short_hop h (3+(fuel-5))
  rw [abort] at run
  exact ⟨_,by rw [show fuel=2+(3+(fuel-5)) by omega];simpa only [pure_bind] using run,rfl⟩

theorem header_positive (h : Header input st) (fits : input.proof.length ≤ 8388615680)
    (nonempty : input.positions.card ≠ 0) (long : 500*input.positions.card ≤ input.proof.length) :
    ∃ state : MachineState,
      RecordCursor input 0 state ∧ state.mem = st.mem ∧ Hop st state 21 24 := by
  let state := checkPreparePrefix (emptyChecked h) 18
  have here := (empty_pc h fits long).trans (ite_eq_right nonempty)
  have usable := check_prepare_view _ here
  have code := (empty_hop h fits long).thenDo (check_prepare_hop _ here)
  have root:=h.root
  have indices:=h.indices
  have values:=h.values
  have proof:=h.proof
  have count:=h.count
  have length:=h.length
  have keep (r : Reg) (a : r ≠ .x6) := empty_keeps h r a
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
  · exact usable.memory.trans ((check_guard_memory .empty (shortChecked h)).trans
      ((check_guard_memory .short (measured h)).trans (measured_view h).2.2.1))

end TwoPermutationPrototype.Packed.Checker
