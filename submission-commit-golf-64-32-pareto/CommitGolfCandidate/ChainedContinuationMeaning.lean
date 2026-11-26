import CommitGolfCandidate.ChainedMaskValue

/-! Full-width continuation queries followed by the single scheduled truncation. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

theorem read_buffer_pc (s : MachineState) (pc : Word) (address count : Nat) :
    readBuffer (s.setPC pc) address count = readBuffer s address count := by rfl

theorem header_read_value (s : MachineState) (buffer : Word) (source : s.getReg .x10 = buffer)
    (aligned : buffer.toNat % 8 = 0) :
    readBuffer (ordinaryPrefix s 1 8) buffer.toNat 32 = readBuffer s buffer.toNat 32 := by
  apply read_digest_congr _ _ _ aligned
  intro i small
  have word := header_low_word s ⟨i,small⟩
  rw [source] at word
  simpa only [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq] using word

theorem continuation_full_content (base buffer : Word) (h : Height) (remaining : Nat)
    (small : remaining ≤ 7) (s : MachineState) (args : LoopArgs s buffer)
    (height : s.getReg .x17 = BitVec.ofNat 64 h.val) (mask : s.getReg .x16 = finalMask h) :
    (do let out ← continuationFullTrace base buffer remaining s
        pure (readBuffer out buffer.toNat 32)) =
      (do let value ← continuationTrace h 0 remaining (readBuffer s buffer.toNat 32)
          pure (finalValue h value)) := by
  by_cases empty : remaining = 0
  · subst remaining
    simp only [continuationFullTrace,continuationPrepared,ite_true,loopTrace,continuationTrace,pure_bind]
    rw [mask_value (s.setPC (base+60)) buffer h args.source args.aligned mask,read_buffer_pc]
  · let next := s.setPC (base+4)
    have nextArgs : LoopArgs next buffer :=
      ⟨args.source,args.target,args.selector,args.size,args.kind,args.aligned,
        args.inputValid,args.outputValid,args.access⟩
    have words := header_domain next h height
    rw [nextArgs.source] at words
    have prepared : continuationPrepared base remaining s = ordinaryPrefix next 1 8 := by
      simp only [continuationPrepared,ite_eq_right empty,next]
    have reduceMask :
        (do let out ← loopTrace buffer remaining (ordinaryPrefix next 1 8)
            pure (readBuffer (ordinaryPrefix out 15 4) buffer.toNat 32)) =
          (do let value ← (do let out ← loopTrace buffer remaining (ordinaryPrefix next 1 8); pure (readBuffer out buffer.toNat 32))
              pure (finalValue h value)) := by
      simp only [bind_assoc,pure_bind]
      apply bind_congr_of_forall_mem_support
      intro out reached
      have source : out.getReg .x10 = buffer :=
        (loop_trace_register _ _ _ _ reached .x10 (by decide) (by decide)).trans nextArgs.header.source
      have final : out.getReg .x16 = finalMask h := by
        rw [loop_trace_register _ _ _ _ reached .x16 (by decide) (by decide),
          header_register _ .x16 (by decide) (by decide)]
        exact mask
      rw [mask_value out buffer h source args.aligned final]
    simp only [continuationFullTrace,prepared,bind_assoc,pure_bind]
    rw [reduceMask,loop_trace_content buffer h 0 remaining (by omega) _ nextArgs.header words,
      header_read_value next buffer nextArgs.source args.aligned,read_buffer_pc]

end CommitGolfCandidate.Chained.Native
