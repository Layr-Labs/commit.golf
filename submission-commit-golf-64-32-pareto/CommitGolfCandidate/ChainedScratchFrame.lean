import CommitGolfCandidate.ChainedHashMeaning

/-! Word frames outside the fixed 64-byte chained-hash scratch buffer. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

structure OutsideScratch (query : Word) : Prop where
  aligned : query.toNat % 8 = 0
  lower : 320 ≤ query.toNat
  room : query.toNat+32 ≤ 2^64

theorem scratch_address_ne (query : Word) (lower : 320 ≤ query.toNat) (i : Fin 8) :
    query ≠ (256 : Word)+BitVec.ofNat 64 (8*i.val) := by
  intro same
  have numeric := congrArg BitVec.toNat same
  have bound : ((256 : Word)+BitVec.ofNat 64 (8*i.val)).toNat < 320 := by
    fin_cases i <;> decide
  omega

theorem write_reply_memory (s : MachineState) (answer : Output) (query : Word)
    (outside : OutsideScratch query) : (writeBits s 256 answer).getMem query = s.getMem query := by
  have bytes := write_bits_read_outside s answer 256 query.toNat 32 (by decide)
    outside.room (Or.inr (by have := outside.lower; omega))
  rw [show BitVec.ofNat 64 256 = (256 : Word) from rfl] at bytes
  have word := congrArg (fun v : Output => v.extractLsb' 0 64) bytes
  rw [read_digest_word _ _ 0 outside.aligned (by decide),
    read_digest_word _ _ 0 outside.aligned (by decide)] at word
  simpa only [Nat.add_zero,Nat.mul_zero,BitVec.ofNat_toNat,BitVec.setWidth_eq] using word

theorem header_heap_memory (s : MachineState) (args : LoopArgs s 256) (query : Word)
    (outside : OutsideScratch query) : (ordinaryPrefix s 1 8).getMem query = s.getMem query := by
  apply header_prefix_memory_outside s query _ 8 (by decide)
  intro j
  rw [args.source,show 32+8*j.val = 8*(j.val+4) by omega]
  exact scratch_address_ne query outside.lower ⟨j.val+4,by omega⟩

theorem LoopArgs.prepared {s : MachineState} (args : LoopArgs s 256) (base : Word) (remaining : Nat) :
    LoopArgs (continuationPrepared base remaining s) 256 := by
  unfold continuationPrepared
  split
  · exact ⟨args.source,args.target,args.selector,args.size,args.kind,args.aligned,
      args.inputValid,args.outputValid,args.access⟩
  · exact (show LoopArgs (s.setPC (base+4)) 256 from
      ⟨args.source,args.target,args.selector,args.size,args.kind,args.aligned,
        args.inputValid,args.outputValid,args.access⟩).header

theorem continuation_prepared_memory (base : Word) (remaining : Nat) (s : MachineState)
    (args : LoopArgs s 256) (query : Word) (outside : OutsideScratch query) :
    (continuationPrepared base remaining s).getMem query = s.getMem query := by
  unfold continuationPrepared
  split
  · rfl
  · exact header_heap_memory (s.setPC (base+4))
      ⟨args.source,args.target,args.selector,args.size,args.kind,args.aligned,
        args.inputValid,args.outputValid,args.access⟩ query outside

end CommitGolfCandidate.Chained.Native
