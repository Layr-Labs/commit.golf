import CommitGolfCandidate.ChainedCommitFetch
import CommitGolfCandidate.ChainedHashState
import CommitGolfCandidate.ChainedContinuationReturn

/-! The actual delivered hash call, including both subroutine returns. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
attribute [local irreducible] execute firstPackPrefix writeBits

private theorem hash_fetch0 (s : MachineState) (pc : s.pc = 186612) :
    fetch chainedCommitImage s = some (.base (.JAL .x1 16)) :=
  chained_parent_at ⟨496,by decide⟩ s pc

private theorem hash_fetch1 (s : MachineState) (pc : s.pc = 186616) :
    fetch chainedCommitImage s = some (.base .ECALL) :=
  chained_parent_at ⟨497,by decide⟩ s pc

def hashLinkPrefix (s : MachineState) (count : Nat) : MachineState :=
  ([Instr.ADDI .x1 .x19 0,.JAL .x0 128].take count).foldl execInstrBr s

theorem hash_link_execution (s : MachineState) (pc : s.pc = 186620) (fuel : Nat) (coins : Bool) :
    execute chainedCommitImage (2+fuel) s coins =
      (do let result ← execute chainedCommitImage fuel (hashLinkPrefix s 2) coins
          return result.charge 2 0) := by
  apply execute_unit_steps (states := hashLinkPrefix s)
  intro i inside
  interval_cases i
  · refine ⟨.base (.ADDI .x1 .x19 0),?_,rfl,rfl⟩
    exact chained_parent_at ⟨498,by decide⟩ s pc
  · refine ⟨.base (.JAL .x0 128),?_,rfl,rfl⟩
    apply chained_parent_at ⟨499,by decide⟩
    change s.pc+4 = _
    rw [pc]
    rfl

theorem hash_pack_execution (s : MachineState) (args : LoopArgs s 256) (pc : s.pc = 186612)
    (inputs : ∀ k : Fin 8, accessValid (s.getReg .x14+BitVec.ofNat 64 (8*k.val)) 8 = true)
    (fuel : Nat) (coins : Bool) :
    execute chainedCommitImage (32+fuel) s coins =
      (do let result ← execute chainedCommitImage fuel (hashPacked s) coins
          return result.charge 32 0) := by
  have step : ordinaryStep s (.base (.JAL .x1 16)) = some (hashPackStart s) := rfl
  rw [show 32+fuel = (31+fuel)+1 by omega,
    execute_ordinary_step chainedCommitImage _ _ _ _ coins (hash_fetch0 s pc) step,
    delivered_first_pack_execution _ (hash_pack_start_pc s pc) args.packStart.source inputs]
  simp only [hashPacked,bind_assoc,pure_bind,Execution.charge,Nat.zero_add,←Nat.add_assoc,Nat.reduceAdd,instructionCycles]

theorem hash_first_call (s : MachineState) (args : LoopArgs s 256) (pc : s.pc = 186612)
    (fuel : Nat) (coins : Bool) :
    execute chainedCommitImage (1+fuel) (hashPacked s) coins =
      (do let answer ← (liftM (World.query (.inr (.inl (readBuffer (hashPacked s) 256 64)))) :
            OracleComp World Output)
          let result ← execute chainedCommitImage fuel (writeBits (hashPacked s) 256 answer) coins
          return result.charge 8 1) := by
  have fetched := hash_fetch1 _ (hash_packed_pc s pc)
  rw [show 1+fuel = fuel+1 by omega]
  simp only [execute,fetched,args.packed.selector,ite_eq_left,args.packed.query,
    writeOracleAnswer,args.packed.target,oracleCycles,COMPRESSION_CYCLES]
  rfl

def hashTrace (remaining : Nat) (s : MachineState) : OracleComp World MachineState := do
  let answer ← (liftM (World.query (.inr (.inl (readBuffer (hashPacked s) 256 64)))) :
    OracleComp World Output)
  continuationFullTrace 186752 256 remaining (hashContinued s answer)

theorem hash_execution (remaining : Nat) (small : remaining ≤ 7) (s : MachineState)
    (args : LoopArgs s 256) (pc : s.pc = 186612)
    (counter : s.getReg .x18 = BitVec.ofNat 64 remaining)
    (inputs : ∀ k : Fin 8, accessValid (s.getReg .x14+BitVec.ofNat 64 (8*k.val)) 8 = true)
    (fuel : Nat) (coins : Bool) :
    execute chainedCommitImage (35+continuationInstructions remaining+fuel) s coins =
      (do let out ← hashTrace remaining s
          let result ← execute chainedCommitImage fuel out coins
          return result.charge (42+continuationCycles remaining) (remaining+1)) := by
  rw [show 35+continuationInstructions remaining+fuel =
    32+(1+(2+(continuationInstructions remaining+fuel))) by omega,
    hash_pack_execution s args pc inputs,hash_first_call s args pc]
  simp only [hashTrace,bind_assoc]
  apply bind_congr
  intro answer
  have writtenPc : (writeBits (hashPacked s) 256 answer).pc = 186620 := by
    have written : (writeBits (hashPacked s) 256 answer).pc = (hashPacked s).pc+4 := by
      simp only [writeBits,MachineState.setPC]
    rw [written,hash_packed_pc s pc]
    rfl
  rw [hash_link_execution _ writtenPc]
  have nextCounter : (hashContinued s answer).getReg .x18 = BitVec.ofNat 64 remaining := by
    rw [hash_continued_register s answer .x18 (by decide),hash_packed_register s .x18 (by decide)]
    exact counter
  simp only [bind_assoc,pure_bind]
  change (do let result ← execute chainedCommitImage (continuationInstructions remaining+fuel)
                (hashContinued s answer) coins
             return ((result.charge 2 0).charge 8 1).charge 32 0) = _
  rw [delivered_continuation_execution remaining small _ (args.continued answer) nextCounter
    (hash_continued_pc s pc answer)]
  simp [Execution.charge,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

theorem hash_trace_bounded (remaining : Nat) (s : MachineState) :
    PublicQueryBound (hashTrace remaining s) (remaining+1) := by
  change 1 ≤ remaining+1 ∧ ∀ answer,
    PublicQueryBound (continuationFullTrace 186752 256 remaining (hashContinued s answer)) (remaining+1-1)
  exact ⟨by omega,fun answer => by simpa using continuation_full_bounded 186752 256 remaining (hashContinued s answer)⟩

theorem hash_return_pc (remaining : Nat) (s out : MachineState)
    (reached : out ∈ support (hashTrace remaining s)) :
    out.pc = (s.getReg .x19+signExtend12 0) &&& ~~~1#64 := by
  simp only [hashTrace,mem_support_bind_iff] at reached
  obtain ⟨answer,_,last⟩ := reached
  rw [continuation_full_return_pc _ _ _ _ _ last,hash_continued_link]

theorem hash_trace_register (remaining : Nat) (s out : MachineState)
    (reached : out ∈ support (hashTrace remaining s)) (reg : Reg)
    (kept : reg ∉ ([.x1,.x18,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x28,.x29,.x30] : List Reg)) :
    out.getReg reg = s.getReg reg := by
  simp only [hashTrace,mem_support_bind_iff] at reached
  obtain ⟨answer,_,last⟩ := reached
  rw [continuation_full_register _ _ _ _ _ last reg (by simp_all) (by simp_all) (by simp_all),
    hash_continued_register s answer reg (by simp_all),hash_packed_register s reg (by simp_all)]

end CommitGolfCandidate.Chained.Native
