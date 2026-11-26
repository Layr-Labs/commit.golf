import CommitGolfCandidate.PairFresh
namespace CommitGolfCandidate.PairCap.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 5000
set_option maxHeartbeats 20000
attribute [local irreducible] bucketState tested copied compared lowerHash readBuffer storedAt Runs
theorem classifyRow (o : Oracle) (input : CheckInput) (n : Nat) (hn : n<128) (s : MachineState)
    (h : HashedFrame o input n s)
    (table : storedAt s (rowBucket input n)=prefixNode o.compression input n (rowBucket input n)) :
    (Rejects o s 28 0 ∧ ¬BatchValid o.compression input) ∨ ∃ fresh,TailOK o input n s fresh := by
  let u := rowBucket input n
  have flagIff := recordFlag o input n s h
  by_cases z : s.getByte (BitVec.ofNat 64 (flag u.val))=0
  · have flagZ : (bucketState s).getReg .x7=0 := flagIff.mpr z
    have safe := freshSafe o input n s h
    have empty : storedAt s u=none := by unfold storedAt;rw [if_pos z]
    exact Or.inr ⟨true,tailFresh flagZ (freshRuntime o s h.pc u h.index flagZ safe) empty⟩
  · have flagNZ : (bucketState s).getReg .x7≠0 := fun eqn => z (flagIff.mp eqn)
    have prior : storedAt s u=some (readBuffer s (cell u.val) 32) := by unfold storedAt;rw [if_neg z]
    by_cases eqn : lowerHash o.compression input n=readBuffer s (cell u.val) 32
    · have wordEq := (comparedWords o input n s h).mpr eqn
      have access := compareAccess _ _ _ _ h
      exact Or.inr ⟨false,tailSeen flagNZ
        (seenRuntime o s h.pc u h.index flagNZ access.1 access.2 wordEq) wordEq (prior.trans (congrArg some eqn.symm))⟩
    · exact Or.inl ⟨duplicateReject o input n s h flagNZ (fun hit => eqn ((comparedWords o input n s h).mp hit)),
        invalidMismatch _ input n hn u rfl _ (table.symm.trans prior) eqn⟩
end CommitGolfCandidate.PairCap.Batch
