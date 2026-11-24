import CommitGolfCandidate.ChainedLevelCall
import CommitGolfCandidate.ChainedHashMeaning

/-! Canonical content of a delivered level's hash call, before heap copying. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

theorem level_setup_memory (s : MachineState) (h : Height) (query : Word) :
    (parentLevelPrefix s h 8).getMem query = s.getMem query := by rfl

theorem level_called_height (s : MachineState) (h : Height) :
    (parentLevelPrefix s h 8).getReg .x17 = BitVec.ofNat 64 h.val := by
  fin_cases h <;> rfl

theorem level_called_mask (s : MachineState) (h : Height) :
    (parentLevelPrefix s h 8).getReg .x16 = finalMask h := by
  change (BitVec.ofNat 64 0+signExtend12 4095) >>>
    (BitVec.ofNat 6 (256-width h)).toNat = _
  fin_cases h <;> decide

theorem level_hash_content (s : MachineState) (h : Height) (args : LoopArgs s 256)
    (left right : BitVec 238)
    (inputs : ∀ k : Fin 8, s.getMem (s.getReg .x6+BitVec.ofNat 64 (8*k.val)) =
      if k.val < 4 then childWord left k.val else childWord right (k.val-4)) :
    (do let out ← levelHashTrace h s; pure (readBuffer out 256 32)) =
      (do let answer ← (liftM (World.query (.inr (.inl (canonicalEncoding.first h (right ++ left))))) :
            OracleComp World Output)
          let value ← continuationTrace h 0 (calls h-1) answer
          pure (finalValue h value)) := by
  have small : calls h-1 ≤ 7 := by have := calls_bound h; omega
  have data : ∀ k : Fin 8,
      (parentLevelPrefix s h 8).getMem ((parentLevelPrefix s h 8).getReg .x14+BitVec.ofNat 64 (8*k.val)) =
        if k.val < 4 then childWord left k.val else childWord right (k.val-4) := by
    intro k
    rw [level_called_source,level_setup_memory]
    exact inputs k
  simpa only [levelHashTrace] using hash_content (calls h-1) small (parentLevelPrefix s h 8)
    (args.levelCalled h) h left right (level_called_height s h) (level_called_mask s h) data

end CommitGolfCandidate.Chained.Native
