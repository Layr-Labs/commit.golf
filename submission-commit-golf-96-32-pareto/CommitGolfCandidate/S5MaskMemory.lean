import CommitGolfCandidate.S5MaskValue
import CommitGolfCandidate.CopyRefinement
import CommitGolfCandidate.WriteMemory
import CommitGolfCandidate.Execution
namespace CommitGolfCandidate.S5Machine
open CommitGolfCandidate.Chained
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
attribute [local irreducible] readBuffer

theorem output_word (state : MachineState) (base k : Nat) (answer : BitVec 256)
    (aligned : base % 8 = 0) (inside : k < 4) :
    (writeBits state (BitVec.ofNat 64 base) answer).getMem (BitVec.ofNat 64 (base+8*k)) =
      answer.extractLsb' (64*k) 64 := by
  have written := write_bits_digest state base 0 answer (by decide) (by decide)
  simp only [Nat.add_zero, Nat.mul_zero, BitVec.extractLsb'_eq_self] at written
  rw [← read_digest_word _ _ _ aligned inside, written]

theorem byte_offset (a : Word) : byteOffset a = a.toNat % 8 := by
  unfold byteOffset
  rw [BitVec.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod _ 3

theorem split_address (a : Word) : alignToDword a + BitVec.ofNat 64 (byteOffset a) = a := by
  unfold alignToDword byteOffset
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have disjoint : (a &&& ~~~7#64) &&& (a &&& 7#64) = 0 := by
    ext i
    simp only [BitVec.getElem_and, BitVec.getElem_not]
    cases h : (7#64)[i] <;> simp
  rw [BitVec.add_eq_or_of_and_eq_zero _ _ disjoint]
  ext i
  simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not]
  cases h : (7#64)[i] <;> simp

theorem word_address (base i : Nat) (aligned : base % 8 = 0) :
    alignToDword (BitVec.ofNat 64 (base+i)) = BitVec.ofNat 64 (base+8*(i/8)) := by
  have offset : byteOffset (BitVec.ofNat 64 (base+i)) = i%8 := by
    rw [byte_offset, BitVec.toNat_ofNat]; omega
  have parts := split_address (BitVec.ofNat 64 (base+i))
  rw [offset] at parts
  have joined : BitVec.ofNat 64 (base+8*(i/8)) + BitVec.ofNat 64 (i%8) =
      BitVec.ofNat 64 (base+i) := by
    rw [← BitVec.ofNat_add]; congr 1; omega
  have eq := congrArg (fun v : Word => v - BitVec.ofNat 64 (i%8)) (parts.trans joined.symm)
  simpa only [BitVec.add_sub_cancel] using eq


private theorem high_full (d : Height) (width : wireWidth d=240) (v : Output) :
    replaceHalfword (v.extractLsb' 192 64) 3 0=(storeReply d v).extractLsb' 192 64 := by
  apply BitVec.eq_of_getLsbD_eq;intro b hb
  have bound : 192+b<256 := by omega
  simp only [replaceHalfword,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_or,
    BitVec.getLsbD_extractLsb',projected_bit d v (192+b) bound,width]
  interval_cases b <;> simp

theorem clear_reply_memory (d : Height) (width : wireWidth d=240) (state : MachineState) (base : Nat) (answer : BitVec 256)
    (aligned : base % 8 = 0) (bound : base + 32 ≤ 2^64) :
    ((writeBits state (BitVec.ofNat 64 base) answer).setHalfword
      (BitVec.ofNat 64 (base+30)) 0).mem =
    (writeBits state (BitVec.ofNat 64 base) (storeReply d answer)).mem := by
  have off : byteOffset (BitVec.ofNat 64 (base+30)) = 6 := by
    rw [byte_offset, BitVec.toNat_ofNat]; omega
  have addr : alignToDword (BitVec.ofNat 64 (base+30)) = BitVec.ofNat 64 (base+24) :=
    word_address base 30 aligned
  funext q
  change (((writeBits state (BitVec.ofNat 64 base) answer).setHalfword _ 0).getMem q) = _
  by_cases last : q = BitVec.ofNat 64 (base+24)
  · subst q
    rw [MachineState.setHalfword, addr, off, MachineState.getMem_setMem_eq]
    change replaceHalfword _ 3 _ = (writeBits state _ _).getMem (BitVec.ofNat 64 (base+8*3))
    rw [output_word state base 3 _ aligned (by decide), output_word state base 3 _ aligned (by decide)]
    exact high_full d width answer
  · rw [MachineState.setHalfword, addr, MachineState.getMem_setMem_ne last]
    by_cases someWord : ∃ k < 4, q = BitVec.ofNat 64 (base+8*k)
    · obtain ⟨k, hk, rfl⟩ := someWord
      change _ = (writeBits state _ _).getMem _
      rw [output_word state base k _ aligned hk, output_word state base k _ aligned hk]
      apply early_projection d _ (by omega)
      by_contra! large
      have eq : k=3 := by omega
      exact last (by rw [eq])
    · have away : ∀ i < 32, q ≠ alignToDword (BitVec.ofNat 64 base + BitVec.ofNat 64 i) := by
        intro i hi eq; apply someWord
        exact ⟨i/8, by omega, eq.trans (by rw [← BitVec.ofNat_add, word_address base i aligned])⟩
      exact (writeBits_memory_outside state _ q answer away).trans
        (writeBits_memory_outside state _ q (storeReply d answer) away).symm



def maskedWord (s : MachineState) (base : Nat) (mask : Word) :=
  let a:=BitVec.ofNat 64 (base+28)
  s.setWord32 a ((((s.getHalfword a).zeroExtend 64) &&& mask).truncate 32)

theorem narrow_reply_memory (d : Height) (lo : 224≤wireWidth d) (hi : wireWidth d≤240)
    (s : MachineState) (base : Nat) (reply : Output) (aligned : base%8=0) (bound : base+32≤2^64) :
    (maskedWord (writeBits s (BitVec.ofNat 64 base) reply) base (heldMask d)).mem=
      (writeBits s (BitVec.ofNat 64 base) (storeReply d reply)).mem := by
  let t:=writeBits s (BitVec.ofNat 64 base) reply
  let a:=BitVec.ofNat 64 (base+28)
  have off : byteOffset a=4 := by dsimp [a];rw [byte_offset,BitVec.toNat_ofNat];omega
  have addr : alignToDword a=BitVec.ofNat 64 (base+24) := word_address base 28 aligned
  funext q
  change ((maskedWord t base (heldMask d)).getMem q)=_
  by_cases last : q=BitVec.ofNat 64 (base+24)
  · subst q
    change (t.setWord32 a _).getMem _=_
    rw [MachineState.setWord32,addr,off,MachineState.getMem_setMem_eq]
    change replaceWord32 (t.getMem (BitVec.ofNat 64 (base+8*3))) 1
      ((((t.getHalfword a).zeroExtend 64) &&& heldMask d).truncate 32)=
      (writeBits s _ _).getMem (BitVec.ofNat 64 (base+8*3))
    rw [MachineState.getHalfword,addr,off]
    change replaceWord32 (t.getMem (BitVec.ofNat 64 (base+8*3))) 1
      (keptHalf (t.getMem (BitVec.ofNat 64 (base+8*3))) (heldMask d))=_
    rw [show t.getMem (BitVec.ofNat 64 (base+8*3))=reply.extractLsb' (64*3) 64 from output_word s base 3 reply aligned (by decide),
      output_word s base 3 _ aligned (by decide)]
    exact last_projection d reply lo hi
  · change (t.setWord32 a _).getMem _=_
    rw [MachineState.setWord32,addr,MachineState.getMem_setMem_ne last]
    by_cases someWord : ∃ k<4,q=BitVec.ofNat 64 (base+8*k)
    · obtain ⟨k,hk,rfl⟩:=someWord
      change _=(writeBits s (BitVec.ofNat 64 base) (storeReply d reply)).getMem (BitVec.ofNat 64 (base+8*k))
      rw [show t.getMem (BitVec.ofNat 64 (base+8*k))=_ from output_word s base k reply aligned hk,output_word s base k _ aligned hk]
      apply early_projection d _ lo
      by_contra! large
      exact last (by rw [show k=3 by omega])
    · have away : ∀ i<32,q≠alignToDword (BitVec.ofNat 64 base+BitVec.ofNat 64 i) := by
        intro i small eq;apply someWord
        exact ⟨i/8,by omega,eq.trans (by rw [←BitVec.ofNat_add,word_address base i aligned])⟩
      exact (writeBits_memory_outside s _ q reply away).trans (writeBits_memory_outside s _ q (storeReply d reply) away).symm
end CommitGolfCandidate.S5Machine
