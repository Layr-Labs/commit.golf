import CommitGolfCandidate.ChainedCheckHashDelivered
import CommitGolfCandidate.TwoPermutationCheckerCopyDigest

/-! The two delivered hash sites only write their scratch words at256–312. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192

def checkerSaveWord (slot : Fin 31) : Word := BitVec.ofNat 64 (8*slot.val)

theorem checker_save_word_apart (slot : Fin 31) (word : Fin 8) :
    checkerSaveWord slot≠(256 : Word)+BitVec.ofNat 64 (8*word.val) := by
  have low : (checkerSaveWord slot).toNat<248 := by
    simp only [checkerSaveWord,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : 8*slot.val<2^64)]
    omega
  have high : 256≤((256 : Word)+BitVec.ofNat 64 (8*word.val)).toNat := by
    fin_cases word <;> decide +kernel
  intro same
  rw [same] at low
  omega

theorem checker_reply_saved_memory (s : MachineState) (answer : Output) (slot : Fin 31) :
    (writeBits s 256 answer).getMem (checkerSaveWord slot)=s.getMem (checkerSaveWord slot) := by
  have frame := TwoPermutationPrototype.Checker.write_bits_word_outside s answer 32 slot.val
    (by decide) (by omega) (Or.inl (by omega))
  exact frame

theorem checker_header_saved_memory (s : MachineState) (args : LoopArgs s 256) (slot : Fin 31) :
    (ordinaryPrefix s 1 8).getMem (checkerSaveWord slot)=s.getMem (checkerSaveWord slot) := by
  apply header_prefix_memory_outside s _ _ 8 (by omega)
  intro word
  rw [args.source,show 32+8*word.val=8*(word.val+4) by omega]
  exact checker_save_word_apart slot ⟨word.val+4,by omega⟩

theorem checker_prepared_saved_memory (base : Word) (remaining : Nat) (s : MachineState)
    (args : LoopArgs s 256) (slot : Fin 31) :
    (continuationPrepared base remaining s).getMem (checkerSaveWord slot)=s.getMem (checkerSaveWord slot) := by
  unfold continuationPrepared
  split
  · rfl
  · exact checker_header_saved_memory (s.setPC (base+4))
      ⟨args.source,args.target,args.selector,args.size,args.kind,args.aligned,
        args.inputValid,args.outputValid,args.access⟩ slot

private theorem prepared_args (base : Word) (remaining : Nat) (s : MachineState) (args : LoopArgs s 256) :
    LoopArgs (continuationPrepared base remaining s) 256 := by
  unfold continuationPrepared
  split
  · exact ⟨args.source,args.target,args.selector,args.size,args.kind,args.aligned,
      args.inputValid,args.outputValid,args.access⟩
  · exact (show LoopArgs (s.setPC (base+4)) 256 from
      ⟨args.source,args.target,args.selector,args.size,args.kind,args.aligned,
        args.inputValid,args.outputValid,args.access⟩).header

theorem checker_loop_saved_memory (remaining : Nat) (s out : MachineState) (args : LoopArgs s 256)
    (reached : out∈support (loopTrace 256 remaining s)) (slot : Fin 31) :
    out.getMem (checkerSaveWord slot)=s.getMem (checkerSaveWord slot) := by
  induction remaining generalizing s with
  | zero =>
    simp only [loopTrace,support_pure,Set.mem_singleton_iff] at reached
    subst out
    rfl
  | succ remaining ih =>
    simp only [loopTrace,mem_support_bind_iff] at reached
    obtain ⟨answer,_,last⟩ := reached
    rw [ih _ (args.after answer) last,loopAfter,tail_memory_outside]
    · exact checker_reply_saved_memory s answer slot
    · rw [writeBits_register,args.source]
      exact checker_save_word_apart slot (4 : Fin 8)

theorem checker_continuation_saved_memory (base : Word) (remaining : Nat) (s out : MachineState)
    (args : LoopArgs s 256) (reached : out∈support (continuationFullTrace base 256 remaining s))
    (slot : Fin 31) : out.getMem (checkerSaveWord slot)=s.getMem (checkerSaveWord slot) := by
  simp only [continuationFullTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨middle,last,rfl⟩ := reached
  have source : middle.getReg .x10=256 :=
    (loop_trace_register _ _ _ _ last .x10 (by decide) (by decide)).trans (prepared_args base remaining s args).source
  rw [mask_memory,source]
  have apart : checkerSaveWord slot≠(256 : Word)+24 := checker_save_word_apart slot (3 : Fin 8)
  simp only [beq_iff_eq,ite_eq_right apart]
  exact (checker_loop_saved_memory remaining _ middle (prepared_args base remaining s args) last slot).trans
    (checker_prepared_saved_memory base remaining s args slot)

theorem checker_hash_packed_saved_memory (site : CheckerHashSite) (s : MachineState) (args : LoopArgs s 256)
    (slot : Fin 31) : (checkerHashPacked site s).getMem (checkerSaveWord slot)=s.getMem (checkerSaveWord slot) := by
  rw [checker_hash_packed_eq,first_pack_memory_outside]
  · exact checker_hash_pack_start_memory site s _
  · rw [(args.checkerPackStart site).source]
    exact checker_save_word_apart slot

theorem checker_hash_continued_saved_memory (site : CheckerHashSite) (s : MachineState) (args : LoopArgs s 256)
    (answer : Output) (slot : Fin 31) :
    (checkerHashContinued site s answer).getMem (checkerSaveWord slot)=s.getMem (checkerSaveWord slot) := by
  rw [checker_hash_continued_eq]
  change (writeBits (checkerHashPacked site s) 256 answer).getMem (checkerSaveWord slot)=_
  rw [checker_reply_saved_memory,checker_hash_packed_saved_memory site s args slot]

theorem checker_hash_saved_memory (site : CheckerHashSite) (remaining : Nat) (s out : MachineState)
    (args : LoopArgs s 256) (reached : out∈support (checkerHashTrace site remaining s))
    (slot : Fin 31) : out.getMem (checkerSaveWord slot)=s.getMem (checkerSaveWord slot) := by
  rw [checker_hash_trace_eq] at reached
  simp only [mem_support_bind_iff] at reached
  obtain ⟨answer,_,last⟩ := reached
  exact (checker_continuation_saved_memory checkerContinuationBase remaining _ out
    (args.checkerContinued site answer) last slot).trans
      (checker_hash_continued_saved_memory site s args answer slot)

end CommitGolfCandidate.Chained.Native
