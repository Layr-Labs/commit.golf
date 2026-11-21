import CommitGolfCandidate.ChainedCheckHashRun
import CommitGolfCandidate.ChainedContinuationMeaning

/-! Both checking hash sites implement full-width chaining and final truncation. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
attribute [local irreducible] firstPackPrefix writeBits

theorem checker_hash_pack_input (site : CheckerHashSite) (s : MachineState)
    (args : LoopArgs s 256) (h : Height) (left right : BitVec 238)
    (height : s.getReg .x17=BitVec.ofNat 64 h.val)
    (inputs : ∀ k : Fin 8, s.getMem (s.getReg .x14+BitVec.ofNat 64 (8*k.val))=
      if k.val<4 then childWord left k.val else childWord right (k.val-4)) :
    readBuffer (checkerHashPacked site s) 256 64=canonicalEncoding.first h (right ++ left) := by
  have nextHeight : (checkerHashPackStart site s).getReg .x17=BitVec.ofNat 64 h.val :=
    (checker_hash_pack_start_register site s .x17 (by decide)).trans height
  have nextInputs : ∀ k : Fin 8,
      (checkerHashPackStart site s).getMem ((checkerHashPackStart site s).getReg .x14+BitVec.ofNat 64 (8*k.val))=
        if k.val<4 then childWord left k.val else childWord right (k.val-4) := by
    intro k
    rw [checker_hash_pack_start_memory,checker_hash_pack_start_register _ _ _ (by decide)]
    exact inputs k
  have pack := first_pack_input (checkerHashPackStart site s) h left right nextHeight
    (by rw [(args.checkerPackStart site).source]; decide) nextInputs
  simpa only [checker_hash_packed_eq,(args.checkerPackStart site).source,
    show (256 : Word).toNat=256 from rfl] using pack

private theorem jal_read (s : MachineState) (offset : BitVec 21) (address count : Nat) :
    readBuffer (execInstrBr s (.JAL .x1 offset)) address count=readBuffer s address count := by rfl

theorem checker_hash_continued_value (site : CheckerHashSite) (s : MachineState) (answer : Output) :
    readBuffer (checkerHashContinued site s answer) 256 32=answer := by
  rw [checker_hash_continued_eq,jal_read]
  have written := write_bits_digest (checkerHashPacked site s) 256 0 answer (by decide) (by decide)
  rw [show BitVec.ofNat 64 256=(256 : Word) from rfl] at written
  simpa only [Nat.add_zero,Nat.mul_zero,BitVec.extractLsb'_eq_self] using written

theorem checker_hash_content (site : CheckerHashSite) (remaining : Nat) (small : remaining≤7)
    (s : MachineState) (args : LoopArgs s 256) (h : Height) (left right : BitVec 238)
    (height : s.getReg .x17=BitVec.ofNat 64 h.val) (mask : s.getReg .x16=finalMask h)
    (inputs : ∀ k : Fin 8, s.getMem (s.getReg .x14+BitVec.ofNat 64 (8*k.val))=
      if k.val<4 then childWord left k.val else childWord right (k.val-4)) :
    (do let out ← checkerHashTrace site remaining s; pure (readBuffer out 256 32))=
      (do let answer ← (liftM (World.query (.inr (.inl (canonicalEncoding.first h (right ++ left))))) :
            OracleComp World Output)
          let value ← continuationTrace h 0 remaining answer
          pure (finalValue h value)) := by
  rw [checker_hash_trace_eq,checker_hash_pack_input site s args h left right height inputs]
  simp only [bind_assoc]
  apply bind_congr
  intro answer
  have nextHeight : (checkerHashContinued site s answer).getReg .x17=BitVec.ofNat 64 h.val := by
    rw [checker_hash_continued_register _ _ _ _ (by decide),
      checker_hash_packed_register _ _ _ (by decide)]
    exact height
  have nextMask : (checkerHashContinued site s answer).getReg .x16=finalMask h := by
    rw [checker_hash_continued_register _ _ _ _ (by decide),
      checker_hash_packed_register _ _ _ (by decide)]
    exact mask
  have content := continuation_full_content checkerContinuationBase 256 h remaining small
    (checkerHashContinued site s answer) (args.checkerContinued site answer) nextHeight nextMask
  simp only [show (256 : Word).toNat=256 from rfl,checker_hash_continued_value] at content
  exact content

end CommitGolfCandidate.Chained.Native
