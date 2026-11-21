import CommitGolfCandidate.ChainedCheckHashState
import CommitGolfCandidate.ChainedFirstPackExecution
import CommitGolfCandidate.ChainedContinuationReturn

/-! Actual checking hash calls through the generic packer and continuation code. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
attribute [local irreducible] execute firstPackPrefix writeBits

theorem checker_hash_pack_execution (site : CheckerHashSite) (s : MachineState)
    (args : LoopArgs s 256) (pc : s.pc=site.base)
    (inputs : ∀ k : Fin 8, accessValid (s.getReg .x14+BitVec.ofNat 64 (8*k.val)) 8=true)
    (fuel : Nat) (coins : Bool) :
    execute chainedCheckerImage (32+fuel) s coins=
      (do let result ← execute chainedCheckerImage fuel (checkerHashPacked site s) coins
          return result.charge 32 0) := by
  have fetched : fetch chainedCheckerImage s=some (.base (.JAL .x1 site.packJump)) :=
    checker_hash_site_at site 0 (by change 0<3; decide) s (by simpa using pc)
  have step : ordinaryStep s (.base (.JAL .x1 site.packJump))=some (checkerHashPackStart site s) := by
    rw [checker_hash_pack_start_eq]
    rfl
  have src : ∀ k : Fin 8,
      accessValid ((checkerHashPackStart site s).getReg .x14+BitVec.ofNat 64 (8*k.val)) 8=true := by
    intro k
    rw [checker_hash_pack_start_register _ _ _ (by decide)]
    exact inputs k
  have dst : ∀ k : Fin 8,
      accessValid ((checkerHashPackStart site s).getReg .x10+BitVec.ofNat 64 (8*k.val)) 8=true := by
    intro k
    rw [(args.checkerPackStart site).source]
    fin_cases k <;> decide +kernel
  rw [show 32+fuel=(31+fuel)+1 by omega,
    execute_ordinary_step chainedCheckerImage _ _ _ _ coins fetched step,
    first_pack_execution chainedCheckerImage checkerPackBase chained_checker_first_pack_at _
      (checker_hash_pack_start_pc site s pc) src dst]
  simp only [checker_hash_packed_eq,bind_assoc,pure_bind,Execution.charge,
    Nat.zero_add,←Nat.add_assoc,Nat.reduceAdd,instructionCycles]

theorem checker_hash_first_call (site : CheckerHashSite) (s : MachineState)
    (args : LoopArgs s 256) (pc : s.pc=site.base) (fuel : Nat) (coins : Bool) :
    execute chainedCheckerImage (1+fuel) (checkerHashPacked site s) coins=
      (do let answer ← (liftM (World.query (.inr (.inl (readBuffer (checkerHashPacked site s) 256 64)))) :
            OracleComp World Output)
          let result ← execute chainedCheckerImage fuel (writeBits (checkerHashPacked site s) 256 answer) coins
          return result.charge 8 1) := by
  have fetched : fetch chainedCheckerImage (checkerHashPacked site s)=some (.base .ECALL) :=
    checker_hash_site_at site 1 (by change 1<3; decide) (checkerHashPacked site s)
      (checker_hash_packed_pc site s pc)
  rw [show 1+fuel=fuel+1 by omega]
  simp only [execute,fetched,(args.checkerPacked site).selector,ite_eq_left,
    (args.checkerPacked site).query,writeOracleAnswer,(args.checkerPacked site).target,
    oracleCycles,COMPRESSION_CYCLES]
  rfl

theorem checker_hash_link_execution (site : CheckerHashSite) (s : MachineState)
    (answer : Output) (pc : s.pc=site.base) (fuel : Nat) (coins : Bool) :
    execute chainedCheckerImage (1+fuel) (writeBits (checkerHashPacked site s) 256 answer) coins=
      (do let result ← execute chainedCheckerImage fuel (checkerHashContinued site s answer) coins
          return result.charge 1 0) := by
  have writtenPc : (writeBits (checkerHashPacked site s) 256 answer).pc=site.base+8 := by
    rw [checker_write_pc,checker_hash_packed_pc site s pc,BitVec.add_assoc]
    rfl
  have fetched : fetch chainedCheckerImage (writeBits (checkerHashPacked site s) 256 answer)=
      some (.base (.JAL .x1 site.nextJump)) :=
    checker_hash_site_at site 2 (by change 2<3; decide) _ writtenPc
  have step : ordinaryStep (writeBits (checkerHashPacked site s) 256 answer)
      (.base (.JAL .x1 site.nextJump))=some (checkerHashContinued site s answer) := by
    rw [checker_hash_continued_eq]
    rfl
  simpa only [Nat.add_comm,instructionCycles] using
    execute_ordinary_step chainedCheckerImage _ _ _ fuel coins fetched step

@[irreducible] def checkerHashTrace (site : CheckerHashSite) (remaining : Nat) (s : MachineState) :
    OracleComp World MachineState := do
  let answer ← (liftM (World.query (.inr (.inl (readBuffer (checkerHashPacked site s) 256 64)))) :
    OracleComp World Output)
  continuationFullTrace checkerContinuationBase 256 remaining (checkerHashContinued site s answer)

theorem checker_hash_trace_eq (site : CheckerHashSite) (remaining : Nat) (s : MachineState) :
    checkerHashTrace site remaining s=
      (do let answer ← (liftM (World.query (.inr (.inl (readBuffer (checkerHashPacked site s) 256 64)))) :
            OracleComp World Output)
          continuationFullTrace checkerContinuationBase 256 remaining (checkerHashContinued site s answer)) := by
  rw [checkerHashTrace]

theorem checker_hash_execution (site : CheckerHashSite) (remaining : Nat) (small : remaining≤7)
    (s : MachineState) (args : LoopArgs s 256) (pc : s.pc=site.base)
    (counter : s.getReg .x18=BitVec.ofNat 64 remaining)
    (inputs : ∀ k : Fin 8, accessValid (s.getReg .x14+BitVec.ofNat 64 (8*k.val)) 8=true)
    (fuel : Nat) (coins : Bool) :
    execute chainedCheckerImage (34+continuationInstructions remaining+fuel) s coins=
      (do let out ← checkerHashTrace site remaining s
          let result ← execute chainedCheckerImage fuel out coins
          return result.charge (41+continuationCycles remaining) (remaining+1)) := by
  rw [show 34+continuationInstructions remaining+fuel=
    32+(1+(1+(continuationInstructions remaining+fuel))) by omega,
    checker_hash_pack_execution site s args pc inputs,checker_hash_first_call site s args pc]
  simp only [checker_hash_trace_eq,bind_assoc]
  apply bind_congr
  intro answer
  rw [checker_hash_link_execution site s answer pc]
  simp only [bind_assoc,pure_bind]
  have nextCounter : (checkerHashContinued site s answer).getReg .x18=BitVec.ofNat 64 remaining := by
    rw [checker_hash_continued_register _ _ _ _ (by decide),
      checker_hash_packed_register _ _ _ (by decide)]
    exact counter
  change (do let result ← execute chainedCheckerImage (continuationInstructions remaining+fuel)
                (checkerHashContinued site s answer) coins
             return ((result.charge 1 0).charge 8 1).charge 32 0)=_
  rw [continuation_entry_execution chainedCheckerImage checkerContinuationBase 256
    chained_checker_continuation_at remaining small _ (args.checkerContinued site answer) nextCounter
    (checker_hash_continued_pc site s answer pc) (by intro k; fin_cases k <;> decide +kernel)]
  simp [Execution.charge,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

theorem checker_hash_trace_bounded (site : CheckerHashSite) (remaining : Nat) (s : MachineState) :
    PublicQueryBound (checkerHashTrace site remaining s) (remaining+1) := by
  rw [checker_hash_trace_eq]
  change 1≤remaining+1 ∧ ∀ answer,
    PublicQueryBound (continuationFullTrace checkerContinuationBase 256 remaining
      (checkerHashContinued site s answer)) (remaining+1-1)
  refine ⟨by omega,?_⟩
  intro answer
  simpa using continuation_full_bounded checkerContinuationBase 256 remaining (checkerHashContinued site s answer)

theorem checker_hash_return_pc (site : CheckerHashSite) (remaining : Nat) (s out : MachineState)
    (pc : s.pc=site.base) (reached : out ∈ support (checkerHashTrace site remaining s)) :
    out.pc=site.resume := by
  rw [checker_hash_trace_eq] at reached
  simp only [mem_support_bind_iff] at reached
  obtain ⟨answer,_,last⟩ := reached
  rw [continuation_full_return_pc _ _ _ _ _ last,checker_hash_continued_link site s answer pc]
  cases site <;> decide +kernel

end CommitGolfCandidate.Chained.Native
