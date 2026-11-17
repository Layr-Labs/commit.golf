import CommitGolfCandidate.TwoPermutationCheckerComplete
import CommitGolfCandidate.TwoPermutationCheckerEmpty
import CommitGolfCandidate.TwoPermutationCheckSetup

namespace TwoPermutationPrototype.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
attribute [local irreducible] execute

private abbrev headerInput (input : CheckInput) := Assembly.submission.initialState .check input
private abbrev measured (input : CheckInput) := measureState 16 (headerInput input)
private abbrev shortChecked (input : CheckInput) := CheckGuard.short.next (measured input)
private abbrev emptyChecked (input : CheckInput) := CheckGuard.empty.next (shortChecked input)

private abbrev measured_view (input : CheckInput) := measure_post (headerInput input) (check_initial_registers input).1

private theorem measure_hop (input : CheckInput) : GroupHop (headerInput input) (measured input) 33 :=
  execute_measure (headerInput input) 16 (by decide) (check_initial_registers input).1

private theorem short_hop (input : CheckInput) : GroupHop (headerInput input) (shortChecked input) 34 :=
  (measure_hop input).thenDo (check_guard_hop .short (measured input) (measured_view input).1)

private theorem short_pc (input : CheckInput) (fits : input.proof.length ≤ Assembly.submission.sizes.proof) :
    (shortChecked input).pc = if input.proof.length < 528*input.positions.card then 0x1368 else 4232 := by
  obtain ⟨_,_,_,_,_,count,length⟩ := check_initial_registers input
  obtain ⟨pc,required,_,kept⟩ := measured_view input
  have requiredEq : (measured input).getReg .x6 = BitVec.ofNat 64 (528*input.positions.card) := by
    rw [required, requiredProofWord, count]
    change BitVec.ofNat 64 input.positions.card * BitVec.ofNat 64 528 = _
    rw [← BitVec.ofNat_mul, Nat.mul_comm]
  have lengthEq : (measured input).getReg .x17 = BitVec.ofNat 64 input.proof.length :=
    (kept .x17 (by decide) (by decide)).trans length
  have maximum := checker_positions_bound input
  have size : input.proof.length < 2^64 := (check_loader_bounds input fits).2.1
  have countSize : 528*input.positions.card < 2^64 := by omega
  rw [check_short_guard _ pc,requiredEq,lengthEq]
  have same : BitVec.ofNat 64 input.proof.length < BitVec.ofNat 64 (528*input.positions.card) ↔
      input.proof.length < 528*input.positions.card := by
    change (BitVec.ofNat 64 input.proof.length).toNat < (BitVec.ofNat 64 (528*input.positions.card)).toNat ↔ _
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt size,Nat.mod_eq_of_lt countSize]
  simp only [same]

private theorem empty_hop (input : CheckInput) (fits : input.proof.length ≤ Assembly.submission.sizes.proof)
    (long : 528*input.positions.card ≤ input.proof.length) :
    GroupHop (headerInput input) (emptyChecked input) 35 := by
  have pc := (short_pc input fits).trans (ite_eq_right (Nat.not_lt.mpr long))
  exact (short_hop input).thenDo (check_guard_hop .empty _ pc)

private theorem empty_pc (input : CheckInput) (fits : input.proof.length ≤ Assembly.submission.sizes.proof)
    (long : 528*input.positions.card ≤ input.proof.length) :
    (emptyChecked input).pc = if input.positions.card = 0 then 0x1358 else 0x108c := by
  have start := (short_pc input fits).trans (ite_eq_right (Nat.not_lt.mpr long))
  have count := (check_guard_register .short (measured input) .x16).trans
    (((measured_view input).2.2.2 .x16 (by decide) (by decide)).trans (check_initial_registers input).2.2.2.2.2.1)
  have cardinal := checker_positions_bound input
  have same : BitVec.ofNat 64 input.positions.card = (0 : Word) ↔ input.positions.card = 0 := by
    rw [← BitVec.toNat_inj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : input.positions.card < 2^64)]
    rfl
  rw [check_empty_guard _ start,count]
  simp only [same]

private theorem empty_keeps (input : CheckInput) (reg : Reg) (a : reg ≠ .x6) (b : reg ≠ .x7) :
    (emptyChecked input).getReg reg = (headerInput input).getReg reg :=
  (check_guard_register .empty (shortChecked input) reg).trans
    ((check_guard_register .short (measured input) reg).trans ((measured_view input).2.2.2 reg a b))

private theorem header_empty (input : CheckInput) (fits : input.proof.length ≤ Assembly.submission.sizes.proof)
    (empty : input.positions.card = 0) :
    ∃ result : Execution,
      execute checkerImage 17179934720 (headerInput input) false = pure result ∧
      result.exit ≠ .unfinished ∧ (input.proof.length = 0 → result.exit = .success) := by
  have long : 528*input.positions.card ≤ input.proof.length := by omega
  have pc := (empty_pc input fits long).trans (ite_eq_left empty)
  obtain ⟨result,accepts,ends,_,finished⟩ := execute_empty_check _ pc (17179934720-39)
  have run := empty_hop input fits long (4+(17179934720-39))
  rw [finished] at run
  refine ⟨result.charge 35 0, ?_, ends, ?_⟩
  · simpa only [pure_bind] using run
  · intro noProof
    apply accepts.mpr
    rw [empty_keeps input .x17 (by decide) (by decide),
      (check_initial_registers input).2.2.2.2.2.2,noProof]

private theorem header_short (input : CheckInput) (fits : input.proof.length ≤ Assembly.submission.sizes.proof)
    (short : input.proof.length < 528*input.positions.card) :
    ∃ result : Execution,
      execute checkerImage 17179934720 (headerInput input) false = pure result ∧ result.exit = .failure := by
  have failed := (short_pc input fits).trans (ite_eq_left short)
  have abort := execute_reject _ failed (17179934720-37)
  have run := short_hop input (3+(17179934720-37))
  rw [abort] at run
  exact ⟨_,by simpa only [pure_bind] using run,rfl⟩

private theorem header_positive (input : CheckInput) (fits : input.proof.length ≤ Assembly.submission.sizes.proof)
    (nonempty : input.positions.card ≠ 0) (long : 528*input.positions.card ≤ input.proof.length) :
    ∃ state : MachineState, ∃ cost ≤ 64,
      RecordCursor input 0 state ∧ state.mem = (headerInput input).mem ∧ GroupHop (headerInput input) state cost := by
  let state := checkPreparePrefix (emptyChecked input) 16
  have here := (empty_pc input fits long).trans (ite_eq_right nonempty)
  have usable := check_prepare_view _ here
  have code := (empty_hop input fits long).thenDo (check_prepare_hop _ here)
  obtain ⟨_,root,indices,values,proof,count,length⟩ := check_initial_registers input
  have keep (r : Reg) (a : r ≠ .x6) (b : r ≠ .x7) := empty_keeps input r a b
  refine ⟨state,51,by decide,⟨?_,?_,?_,?_,?_,usable.tag,?_,usable.length,?_,usable.digest,
    usable.pair,usable.capRoots,usable.marks,usable.capCount,usable.selector⟩,?_,code⟩
  · exact usable.pc.trans (ite_eq_right (Ne.symm nonempty)).symm
  · exact usable.index.trans ((keep .x13 (by decide) (by decide)).trans indices)
  · rw [usable.value,keep .x14 (by decide) (by decide),values]
    rfl
  · exact usable.proof.trans ((keep .x15 (by decide) (by decide)).trans proof)
  · exact usable.count.trans ((keep .x16 (by decide) (by decide)).trans count)
  · exact usable.root.trans ((keep .x11 (by decide) (by decide)).trans root)
  · rw [usable.proofEnd,keep .x15 (by decide) (by decide),keep .x17 (by decide) (by decide),proof,length]
    change BitVec.ofNat 64 10334769248+BitVec.ofNat 64 input.proof.length = _
    rw [← BitVec.ofNat_add]
  · exact usable.memory.trans ((check_guard_memory .empty (shortChecked input)).trans
      ((check_guard_memory .short (measured input)).trans (measured_view input).2.2.1))

theorem checker_header_facts : CheckerHeaderFacts :=
  ⟨header_empty,header_short,header_positive⟩

theorem verifiedChecker : Assembly.CheckerFacts := checker_facts_of_header checker_header_facts

end TwoPermutationPrototype.Checker
