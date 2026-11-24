import CommitGolfCandidate.ChainedContinuationInput
import CommitGolfCandidate.WriteMemory

/-! Full-width reply and domain preservation between native continuation calls. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

theorem DomainWords.written {s : MachineState} {buffer : Word} {h : Height} {j : Nat}
    (words : DomainWords s buffer h j) (answer : Output)
    (aligned : buffer.toNat % 8 = 0) (room : buffer.toNat+64 ≤ 2^64) :
    DomainWords (writeBits s buffer answer) buffer h j := by
  have address (offset : Nat) : BitVec.ofNat 64 (buffer.toNat+offset) = buffer+BitVec.ofNat 64 offset := by
    rw [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  have upper : readBuffer (writeBits s buffer answer) (buffer.toNat+32) 32 =
      readBuffer s (buffer.toNat+32) 32 := by
    have written := write_bits_read_outside s answer buffer.toNat (buffer.toNat+32) 32
      (by omega) (by omega) (Or.inr (by omega))
    simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using written
  have same (i : Fin 4) :
      (writeBits s buffer answer).getMem (buffer+BitVec.ofNat 64 (32+8*i.val)) =
        s.getMem (buffer+BitVec.ofNat 64 (32+8*i.val)) := by
    have word := congrArg (fun v : BitVec 256 => v.extractLsb' (64*i.val) 64) upper
    rw [read_digest_word _ _ _ (by omega) i.isLt,read_digest_word _ _ _ (by omega) i.isLt] at word
    simpa only [Nat.add_assoc,address] using word
  constructor
  · exact (same ⟨0,by decide⟩).trans words.tag
  · exact (same ⟨1,by decide⟩).trans words.zero0
  · exact (same ⟨2,by decide⟩).trans words.zero1
  · exact (same ⟨3,by decide⟩).trans words.flag

theorem DomainWords.tail {s : MachineState} {buffer : Word} {h : Height} {j : Nat}
    (words : DomainWords s buffer h j) (source : s.getReg .x10 = buffer) :
    DomainWords (tailAfter s) buffer h (j+1) := by
  have same (offset : Word) (different : offset ≠ signExtend12 32) :
      (tailAfter s).getMem (buffer+offset) = s.getMem (buffer+offset) := by
    apply tail_memory_outside
    rw [source]
    intro equal
    exact different ((BitVec.add_right_inj _).mp equal)
  constructor
  · have tag := tail_tag s
    rw [source,words.tag] at tag
    rw [tag]
    change BitVec.ofNat 64 (7*h.val+j)+BitVec.ofNat 64 1 = _
    rw [← BitVec.ofNat_add,Nat.add_assoc]
  · exact (same 40 (by decide +kernel)).trans words.zero0
  · exact (same 48 (by decide +kernel)).trans words.zero1
  · exact (same 56 (by decide +kernel)).trans words.flag

theorem loop_after_value (s : MachineState) (buffer : Word) (answer : Output)
    (aligned : buffer.toNat % 8 = 0) (source : s.getReg .x10 = buffer) :
    readBuffer (loopAfter buffer s answer) buffer.toNat 32 = answer := by
  unfold loopAfter
  have kept : readBuffer (tailAfter (writeBits s buffer answer)) buffer.toNat 32 =
      readBuffer (writeBits s buffer answer) buffer.toNat 32 := by
    apply read_digest_congr _ _ _ aligned
    intro i small
    have word := tail_low_word (writeBits s buffer answer) ⟨i,small⟩
    rw [writeBits_register,source] at word
    simpa only [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq] using word
  rw [kept]
  have written := write_bits_digest s buffer.toNat 0 answer (by decide) (by decide)
  simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq,Nat.add_zero,Nat.mul_zero,
    BitVec.extractLsb'_eq_self] using written

def continuationTrace (h : Height) : Nat → Nat → Output → OracleComp World Output
  | _,0,value => pure value
  | stage,remaining+1,value => do
    let answer ← (liftM (World.query (.inr (.inl (encodeNext h (stage+1) value)))) :
      OracleComp World Output)
    continuationTrace h (stage+1) remaining answer

theorem loop_trace_content (buffer : Word) (h : Height) (stage remaining : Nat)
    (small : stage+remaining ≤ 7) (s : MachineState) (args : LoopArgs s buffer)
    (words : DomainWords s buffer h stage) :
    (do let out ← loopTrace buffer remaining s; pure (readBuffer out buffer.toNat 32)) =
      continuationTrace h stage remaining (readBuffer s buffer.toNat 32) := by
  induction remaining generalizing stage s with
  | zero => simp [loopTrace,continuationTrace]
  | succ remaining ih =>
    have room : buffer.toNat+64 ≤ 2^64 := by
      have valid := of_decide_eq_true args.inputValid
      change buffer.toNat+64 ≤ MEMORY_BYTES at valid
      unfold MEMORY_BYTES at valid
      omega
    rw [loopTrace,continuationTrace,domain_input s buffer h stage (by omega) args.aligned words]
    simp only [bind_assoc]
    apply bind_congr
    intro answer
    have next := (words.written answer args.aligned room).tail (by
      rw [writeBits_register]; exact args.source)
    rw [ih (stage+1) (by omega) _ (args.after answer) next,
      loop_after_value s buffer answer args.aligned args.source]

end CommitGolfCandidate.Chained.Native
