import CommitGolfCandidate.ChainedContinuationEntry

/-! Caller-register, return-address and public-query frames of the full call. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

theorem mask_register (s : MachineState) (reg : Reg) (kept : reg ≠ .x29) :
    (ordinaryPrefix s 15 4).getReg reg = s.getReg reg := by
  cases reg <;> first | exact (kept rfl).elim | rfl

theorem mask_return_pc (s : MachineState) :
    (ordinaryPrefix s 15 4).pc = (s.getReg .x1+signExtend12 0) &&& ~~~1#64 := by
  rfl

theorem loop_trace_register (buffer : Word) (remaining : Nat) (s out : MachineState)
    (reached : out ∈ support (loopTrace buffer remaining s)) (reg : Reg)
    (not29 : reg ≠ .x29) (not18 : reg ≠ .x18) : out.getReg reg = s.getReg reg := by
  induction remaining generalizing s with
  | zero =>
    simp only [loopTrace,support_pure,Set.mem_singleton_iff] at reached
    subst out
    rfl
  | succ remaining ih =>
    simp only [loopTrace,mem_support_bind_iff] at reached
    obtain ⟨answer,_,last⟩ := reached
    rw [ih _ last,loopAfter,tail_register _ reg not29 not18,writeBits_register]

theorem continuation_prepared_register (base : Word) (remaining : Nat) (s : MachineState)
    (reg : Reg) (not29 : reg ≠ .x29) (not30 : reg ≠ .x30) :
    (continuationPrepared base remaining s).getReg reg = s.getReg reg := by
  unfold continuationPrepared
  split
  · rfl
  · rw [header_register _ reg not29 not30]
    rfl

theorem continuation_full_register (base buffer : Word) (remaining : Nat) (s out : MachineState)
    (reached : out ∈ support (continuationFullTrace base buffer remaining s)) (reg : Reg)
    (not29 : reg ≠ .x29) (not30 : reg ≠ .x30) (not18 : reg ≠ .x18) :
    out.getReg reg = s.getReg reg := by
  simp only [continuationFullTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨middle,last,rfl⟩ := reached
  rw [mask_register _ reg not29,loop_trace_register _ _ _ _ last reg not29 not18,
    continuation_prepared_register _ _ _ reg not29 not30]

theorem continuation_full_return_pc (base buffer : Word) (remaining : Nat) (s out : MachineState)
    (reached : out ∈ support (continuationFullTrace base buffer remaining s)) :
    out.pc = (s.getReg .x1+signExtend12 0) &&& ~~~1#64 := by
  simp only [continuationFullTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨middle,last,rfl⟩ := reached
  rw [mask_return_pc,loop_trace_register _ _ _ _ last .x1 (by decide) (by decide),
    continuation_prepared_register _ _ _ .x1 (by decide) (by decide)]

theorem continuation_full_bounded (base buffer : Word) (remaining : Nat) (s : MachineState) :
    PublicQueryBound (continuationFullTrace base buffer remaining s) remaining := by
  simpa only [continuationFullTrace,Nat.add_zero] using public_query_bound_bind
    (next := fun out : MachineState => pure (ordinaryPrefix out 15 4))
    (loop_trace_bounded buffer remaining (continuationPrepared base remaining s))
    (second := 0) (fun _ => trivial)

end CommitGolfCandidate.Chained.Native
