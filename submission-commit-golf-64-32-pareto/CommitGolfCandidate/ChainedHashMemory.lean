import CommitGolfCandidate.ChainedScratchFrame

/-! Every supported delivered hash trace preserves heap words outside scratch. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

theorem loop_trace_memory (remaining : Nat) (s out : MachineState) (args : LoopArgs s 256)
    (reached : out ∈ support (loopTrace 256 remaining s)) (query : Word)
    (outside : OutsideScratch query) : out.getMem query = s.getMem query := by
  induction remaining generalizing s with
  | zero =>
    simp only [loopTrace,support_pure,Set.mem_singleton_iff] at reached
    subst out
    rfl
  | succ remaining ih =>
    simp only [loopTrace,mem_support_bind_iff] at reached
    obtain ⟨answer,_,last⟩ := reached
    rw [ih _ (args.after answer) last,loopAfter,tail_memory_outside]
    · exact write_reply_memory s answer query outside
    · rw [writeBits_register,args.source]
      exact scratch_address_ne query outside.lower (4 : Fin 8)

theorem continuation_full_memory (base : Word) (remaining : Nat) (s out : MachineState)
    (args : LoopArgs s 256) (reached : out ∈ support (continuationFullTrace base 256 remaining s))
    (query : Word) (outside : OutsideScratch query) : out.getMem query = s.getMem query := by
  simp only [continuationFullTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨middle,last,rfl⟩ := reached
  have source : middle.getReg .x10 = 256 :=
    (loop_trace_register _ _ _ _ last .x10 (by decide) (by decide)).trans
      (args.prepared base remaining).source
  rw [mask_memory,source]
  have avoid := scratch_address_ne query outside.lower (3 : Fin 8)
  rw [show BitVec.ofNat 64 (8*(3 : Fin 8).val) = (24 : Word) from rfl] at avoid
  simp only [beq_iff_eq,ite_eq_right avoid]
  exact (loop_trace_memory remaining _ middle (args.prepared base remaining) last query outside).trans
    (continuation_prepared_memory base remaining s args query outside)

theorem hash_packed_memory (s : MachineState) (args : LoopArgs s 256) (query : Word)
    (outside : OutsideScratch query) : (hashPacked s).getMem query = s.getMem query := by
  rw [hashPacked,first_pack_memory_outside]
  · rfl
  · rw [args.packStart.source]
    exact scratch_address_ne query outside.lower

theorem hash_continued_memory (s : MachineState) (args : LoopArgs s 256) (answer : Output)
    (query : Word) (outside : OutsideScratch query) :
    (hashContinued s answer).getMem query = s.getMem query := by
  change (writeBits (hashPacked s) 256 answer).getMem query = _
  rw [write_reply_memory _ answer query outside,hash_packed_memory s args query outside]

theorem hash_trace_memory (remaining : Nat) (s out : MachineState) (args : LoopArgs s 256)
    (reached : out ∈ support (hashTrace remaining s)) (query : Word)
    (outside : OutsideScratch query) : out.getMem query = s.getMem query := by
  simp only [hashTrace,mem_support_bind_iff] at reached
  obtain ⟨answer,_,last⟩ := reached
  exact (continuation_full_memory 186752 remaining _ out (args.continued answer) last query outside).trans
    (hash_continued_memory s args answer query outside)

end CommitGolfCandidate.Chained.Native
