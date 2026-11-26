import CommitGolfCandidate.Execution

/-! State predicates preserved by all execution outcomes, including faults and syscalls. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

structure ExecutionInvariant (image : Image) (P : MachineState → Prop) : Prop where
  ordinary : ∀ s instruction next, P s → fetch image s=some instruction →
    ordinaryStep s instruction=some next → P next
  oracle : ∀ s input answer, P s → fetch image s=some (.base .ECALL) →
    P (writeOracleAnswer s (s.getReg .x12) input answer)
  random : ∀ s (bytes : Nat) (answer : BitVec (8*bytes)), P s → fetch image s=some (.base .ECALL) →
    P (writeBits s (s.getReg .x10) answer)

theorem ExecutionInvariant.preserves {image : Image} {P : MachineState → Prop}
    (closed : ExecutionInvariant image P) (steps : Nat) (s : MachineState) (coins : Bool)
    (initial : P s) (result : Execution) (reached : result∈support (execute image steps s coins)) :
    P result.state := by
  induction steps generalizing s result with
  | zero =>
    simp only [execute,support_pure,Set.mem_singleton_iff] at reached
    subst result
    exact initial
  | succ steps ih =>
    simp only [execute] at reached
    split at reached
    · simp only [support_pure,Set.mem_singleton_iff] at reached
      subst result
      exact initial
    · rename_i fetched
      split at reached
      · split at reached
        · simp only [support_pure,Set.mem_singleton_iff] at reached
          subst result
          exact initial
        · simp only [mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
          obtain ⟨answer,_,next,live,rfl⟩ := reached
          exact ih _ (closed.oracle _ _ _ initial fetched) next live
      · split at reached
        · simp only [support_pure,Set.mem_singleton_iff] at reached
          subst result
          exact initial
        · split at reached
          · simp only [mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
            obtain ⟨answer,_,next,live,rfl⟩ := reached
            exact ih _ (closed.random _ _ _ initial fetched) next live
          · simp only [support_pure,Set.mem_singleton_iff] at reached
            subst result
            exact initial
    · rename_i instruction fetched
      split at reached
      · simp only [support_pure,Set.mem_singleton_iff] at reached
        subst result
        exact initial
      · rename_i next stepped
        simp only [mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
        obtain ⟨last,live,rfl⟩ := reached
        exact ih _ (closed.ordinary _ _ _ initial fetched stepped) last live

end CommitGolfCandidate.Chained.Native
