import CommitGolfCandidate.ChainedLevelFrame

/-! Canonical chained digest readback after the complete node, including its back edge. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
attribute [local irreducible] cursorPrefix branchState

theorem node_content (s : MachineState) (h : Height) (args : LoopArgs s 256)
    (left right : BitVec 238) (height : s.getReg .x17 = BitVec.ofNat 64 h.val)
    (mask : s.getReg .x16 = finalMask h)
    (inputs : ∀ k : Fin 8, s.getMem (s.getReg .x6+BitVec.ofNat 64 (8*k.val)) =
      if k.val < 4 then childWord left k.val else childWord right (k.val-4))
    (aligned : (s.getReg .x7).toNat % 8 = 0)
    (separate : ∀ a b : Fin 4, (256 : Word)+BitVec.ofNat 64 (8*a.val) ≠ s.getReg .x7+BitVec.ofNat 64 (8*b.val)) :
    (do let out ← nodeTrace h s; pure (readBuffer out (s.getReg .x7).toNat 32)) =
      (do let answer ← (liftM (World.query (.inr (.inl (canonicalEncoding.first h (right ++ left))))) :
            OracleComp World Output)
          let value ← continuationTrace h 0 (calls h-1) answer
          pure (finalValue h value)) := by
  trans (do let stored ← storeTrace h s; pure (readBuffer stored (s.getReg .x7).toNat 32))
  · simp only [nodeTrace,bind_assoc,pure_bind]
    apply bind_congr_of_forall_mem_support
    intro stored reached
    apply congrArg pure
    apply read_digest_congr _ _ _ aligned
    intro i inside
    rw [branch_memory,cursor_memory]
  · exact store_content s h args left right height mask inputs aligned separate

end CommitGolfCandidate.Chained.Native
