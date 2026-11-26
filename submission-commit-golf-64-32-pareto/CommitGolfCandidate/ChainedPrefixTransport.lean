import CommitGolfCandidate.ChainedPrefixInvariant

/-! Transfer an ordinary prefix without equating either image's postpass. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

theorem fetch_eq_of_prefix (source target : Image) (words : Nat)
    (codePrefix : target.code.take words=source.code.take words)
    (s : MachineState) (below : s.pc.toNat<4096+4*words) :
    fetch target s=fetch source s := by
  unfold fetch
  split
  · rename_i aligned
    have inside : (s.pc.toNat-4096)/4<words := by omega
    have word := congrArg (fun code => code[(s.pc.toNat-4096)/4]?) codePrefix
    simp only [List.getElem?_take,inside,ite_true] at word
    rw [word]
  · rfl

private theorem execute_non_ecall (image : Image) (s : MachineState) (instruction : Instruction)
    (steps : Nat) (coins : Bool) (fetched : fetch image s=some instruction)
    (ordinary : instruction≠.base .ECALL) :
    execute image (steps+1) s coins =
      match ordinaryStep s instruction with
      | none => pure ⟨.failure,s,1,0⟩
      | some next => do
          let result ← execute image steps next coins
          return result.charge (instructionCycles instruction) 0 := by
  cases instruction with
  | base instruction => cases instruction <;> simp_all [execute] <;> rfl
  | word op rd rs1 rs2 => simp only [execute,fetched]; rfl
  | sraiw rd rs shift => simp only [execute,fetched]; rfl

theorem transport_unfinished_prefix (source target : Image) (cut : Nat)
    (closed : ExecutionInvariant source (fun s => cut<s.pc.toNat))
    (leaves : ∀ s instruction next, s.pc.toNat=cut → fetch source s=some instruction →
      ordinaryStep s instruction=some next → cut<next.pc.toNat)
    (ordinary : ∀ s instruction, s.pc.toNat≤cut → fetch source s=some instruction →
      instruction≠.base .ECALL)
    (same : ∀ s, s.pc.toNat<cut → fetch target s=fetch source s)
    (steps : Nat) (s : MachineState) (coins : Bool) (result : Execution)
    (reached : result∈support (execute source steps s coins))
    (unfinished : result.exit=.unfinished) (below : result.state.pc.toNat≤cut) :
    execute target steps s coins=pure result := by
  induction steps generalizing s result with
  | zero =>
    simp only [execute,support_pure,Set.mem_singleton_iff] at reached
    subst result
    rfl
  | succ steps ih =>
    have initial : s.pc.toNat≤cut := by
      by_contra outside
      have above := closed.preserves (steps+1) s coins (by omega) result reached
      omega
    cases fetched : fetch source s with
    | none =>
      simp only [execute,fetched,support_pure,Set.mem_singleton_iff] at reached
      subst result
      contradiction
    | some instruction =>
      rw [execute_non_ecall source s instruction steps coins fetched (ordinary s instruction initial fetched)] at reached
      cases stepped : ordinaryStep s instruction with
      | none =>
        simp only [stepped,support_pure,Set.mem_singleton_iff] at reached
        subst result
        contradiction
      | some next =>
        simp only [stepped,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
        obtain ⟨tail,live,rfl⟩ := reached
        have strict : s.pc.toNat<cut := by
          by_contra boundary
          have nextAbove := leaves s instruction next (by omega) fetched stepped
          have finalAbove := closed.preserves steps next coins nextAbove tail live
          change tail.state.pc.toNat≤cut at below
          omega
        have fetchedTarget : fetch target s=some instruction := (same s strict).trans fetched
        rw [execute_ordinary_step target instruction s next steps coins fetchedTarget stepped,
          ih next tail live unfinished below]
        rfl

end CommitGolfCandidate.Chained.Native
