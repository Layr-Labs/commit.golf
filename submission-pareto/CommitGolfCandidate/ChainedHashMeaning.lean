import CommitGolfCandidate.ChainedHashInput
import CommitGolfCandidate.ChainedContinuationMeaning

/-! The delivered shared call implements canonical full-width chaining and final truncation. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
attribute [local irreducible] firstPackPrefix writeBits

theorem hash_link_read (s : MachineState) (address count : Nat) :
    readBuffer (execInstrBr (execInstrBr s (.ADDI .x1 .x19 0)) (.JAL .x0 128)) address count =
      readBuffer s address count := by rfl

theorem hash_continued_value (s : MachineState) (answer : Output) :
    readBuffer (hashContinued s answer) 256 32 = answer := by
  rw [hashContinued,hash_link_read]
  have written := write_bits_digest (hashPacked s) 256 0 answer (by decide) (by decide)
  rw [show BitVec.ofNat 64 256 = (256 : Word) from rfl] at written
  simpa only [Nat.add_zero,Nat.mul_zero,BitVec.extractLsb'_eq_self] using written

theorem hash_content (remaining : Nat) (small : remaining ≤ 7) (s : MachineState)
    (args : LoopArgs s 256) (h : Height) (left right : BitVec 238)
    (height : s.getReg .x17 = BitVec.ofNat 64 h.val) (mask : s.getReg .x16 = finalMask h)
    (inputs : ∀ k : Fin 8, s.getMem (s.getReg .x14+BitVec.ofNat 64 (8*k.val)) =
      if k.val < 4 then childWord left k.val else childWord right (k.val-4)) :
    (do let out ← hashTrace remaining s; pure (readBuffer out 256 32)) =
      (do let answer ← (liftM (World.query (.inr (.inl (canonicalEncoding.first h (right ++ left))))) :
            OracleComp World Output)
          let value ← continuationTrace h 0 remaining answer
          pure (finalValue h value)) := by
  rw [hash_trace_first remaining s args h left right height inputs]
  simp only [bind_assoc]
  apply bind_congr
  intro answer
  have heightNext : (hashContinued s answer).getReg .x17 = BitVec.ofNat 64 h.val := by
    rw [hash_continued_register s answer .x17 (by decide),hash_packed_register s .x17 (by decide)]
    exact height
  have maskNext : (hashContinued s answer).getReg .x16 = finalMask h := by
    rw [hash_continued_register s answer .x16 (by decide),hash_packed_register s .x16 (by decide)]
    exact mask
  have content := continuation_full_content 186752 256 h remaining small
    (hashContinued s answer) (args.continued answer) heightNext maskNext
  simp only [show (256 : Word).toNat = 256 from rfl,hash_continued_value] at content
  exact content

end CommitGolfCandidate.Chained.Native
