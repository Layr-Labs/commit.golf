import CommitGolfCandidate.TwoPermutationPackedParentMask
import CommitGolfCandidate.TwoPermutationPackedParentControl
import CommitGolfCandidate.K3GQModel

/-!
# A 238-bit heap parent

`ecall; lhu x31,28(x12); and x31,x31,x6; sw x31,28(x12); addi x10,x10,-64; addi x12,x12,-32` with
`x6 = 0x3fff`: the compression reply is written at the node, then the node's bits `238..256` are
cleared (bytes 28..31 become the low 14 bits of the halfword at 28, zero-extended), so the node holds
`pad238 reply`. Only the node's last 64-bit word changes; `x31` is scratch.
-/

namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open CommitGolfCandidate (write_bits_digest read_digest_word writeBits_memory_outside writeBits_register)
set_option maxRecDepth 8192
set_option maxHeartbeats 2500000
attribute [local irreducible] execute

def t238Mask (s : MachineState) (n : Nat) (answer : BitVec 256) :=
  execInstrBr (execInstrBr (execInstrBr (parentWritten s n answer) (.LHU .x31 .x12 28)) (.AND .x31 .x31 .x6))
    (.SW .x12 .x31 28)

def t238After (s : MachineState) (n : Nat) (answer : BitVec 256) :=
  execInstrBr (execInstrBr (t238Mask s n answer) (.ADDI .x10 .x10 4032)) (.ADDI .x12 .x12 4064)

structure T238WordsAt (image : Image) (pc : Word) : Prop where
  call : ∀ s : MachineState, s.pc=pc → fetch image s=some (.base .ECALL)
  load : ∀ s : MachineState, s.pc=pc+4 → fetch image s=some (.base (.LHU .x31 .x12 28))
  mask : ∀ s : MachineState, s.pc=pc+8 → fetch image s=some (.base (.AND .x31 .x31 .x6))
  store : ∀ s : MachineState, s.pc=pc+12 → fetch image s=some (.base (.SW .x12 .x31 28))
  source : ∀ s : MachineState, s.pc=pc+16 → fetch image s=some (.base (.ADDI .x10 .x10 4032))
  target : ∀ s : MachineState, s.pc=pc+20 → fetch image s=some (.base (.ADDI .x12 .x12 4064))

private theorem output_word (state : MachineState) (base k : Nat) (answer : BitVec 256)
    (aligned : base % 8 = 0) (inside : k < 4) :
    (writeBits state (BitVec.ofNat 64 base) answer).getMem (BitVec.ofNat 64 (base+8*k)) =
      answer.extractLsb' (64*k) 64 := by
  have written := write_bits_digest state base 0 answer (by decide) (by decide)
  simp only [Nat.add_zero, Nat.mul_zero, BitVec.extractLsb'_eq_self] at written
  rw [← read_digest_word _ _ _ aligned inside, written]

private theorem byte_offset (a : Word) : byteOffset a = a.toNat % 8 := by
  unfold byteOffset
  rw [BitVec.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod _ 3

private theorem split_address (a : Word) : alignToDword a + BitVec.ofNat 64 (byteOffset a) = a := by
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

private theorem word_address (base i : Nat) (aligned : base % 8 = 0) :
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

/-- The last 64-bit word of a node after the mask. -/
theorem t238_last_word (x : BitVec 256) :
    replaceWord32 (x.extractLsb' 192 64) 1
      ((((extractHalfword (x.extractLsb' 192 64) 2).zeroExtend 64) &&& (16383 : Word)).truncate 32) =
    (pad238 x).extractLsb' 192 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit hb
  have rhs : ((pad238 x).extractLsb' 192 64).getLsbD bit = (decide (bit < 46) && x.getLsbD (192+bit)) := by
    unfold pad238
    rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
    by_cases h : 192+bit < 238
    · rw [if_pos h, BitVec.getLsbD_extractLsb']
      simp [hb, h, show bit < 46 by omega]
    · rw [if_neg h]
      simp [show ¬ bit < 46 by omega]
  rw [rhs]
  simp only [replaceWord32, extractHalfword]
  interval_cases bit <;> simp

private theorem low_t238 (x : BitVec 256) (k : Nat) (hk : k < 3) :
    x.extractLsb' (64*k) 64 = (pad238 x).extractLsb' (64*k) 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit hb
  have inside : 64*k+bit < 238 := by omega
  simp only [pad238, BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and]
  rw [BitVec.getLsbD_append, if_pos inside]
  simp [BitVec.getLsbD_extractLsb', inside]

/-- The masked node: the memory equals the plain write of `pad238 answer`. -/
theorem t238_mask_memory (s : MachineState) (n : Nat) (answer : BitVec 256)
    (target : s.getReg .x12=wordAddress (treeWord n)) (mask : s.getReg .x6=16383) (inside : n<2^24) :
    (t238Mask s n answer).mem=(parentWritten s n (pad238 answer)).mem := by
  let base := 8*treeWord n
  have aligned : base%8=0 := by dsimp [base]; omega
  have baseWord : wordAddress (treeWord n)=BitVec.ofNat 64 base := rfl
  let t := parentWritten s n answer
  let u := execInstrBr t (.LHU .x31 .x12 28)
  let v := execInstrBr u (.AND .x31 .x31 .x6)
  have tx12 : t.getReg .x12=BitVec.ofNat 64 base := by
    simp only [t,parentWritten,writeBits_register,target,baseWord]
  have tx6 : t.getReg .x6=16383 := by simp only [t,parentWritten,writeBits_register,mask]
  have address : t.getReg .x12+signExtend12 28=BitVec.ofNat 64 (base+28) := by
    rw [tx12]; change BitVec.ofNat 64 base+BitVec.ofNat 64 28=_; rw [←BitVec.ofNat_add]
  have dword : alignToDword (BitVec.ofNat 64 (base+28))=BitVec.ofNat 64 (base+24) := word_address base 28 aligned
  have offset : byteOffset (BitVec.ofNat 64 (base+28))=4 := by
    rw [byte_offset,BitVec.toNat_ofNat]; dsimp [base]; unfold treeWord; omega
  have last : t.getMem (BitVec.ofNat 64 (base+24))=answer.extractLsb' 192 64 :=
    output_word s base 3 answer aligned (by decide)
  have ux12 : u.getReg .x12=t.getReg .x12 := by
    simp only [u,execInstrBr,MachineState.getReg_setPC]
    exact MachineState.getReg_setReg_ne _ _ _ _ (by decide)
  have ux6 : u.getReg .x6=t.getReg .x6 := by
    simp only [u,execInstrBr,MachineState.getReg_setPC]
    exact MachineState.getReg_setReg_ne _ _ _ _ (by decide)
  have ux31 : u.getReg .x31=(t.getHalfword (t.getReg .x12+signExtend12 28)).zeroExtend 64 := by
    simp only [u,execInstrBr,MachineState.getReg_setPC]
    exact MachineState.getReg_setReg_eq (by decide)
  have vx12 : v.getReg .x12=t.getReg .x12 := by
    simp only [v,execInstrBr,MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide)]; exact ux12
  have vx31 : v.getReg .x31=u.getReg .x31 &&& u.getReg .x6 := by
    simp only [v,execInstrBr,MachineState.getReg_setPC]
    exact MachineState.getReg_setReg_eq (by decide)
  have vmem (a : Word) : v.getMem a=t.getMem a := by
    simp only [v,u,execInstrBr,MachineState.getMem_setPC,MachineState.getMem_setReg]
  have value : (v.getReg .x31).truncate 32 =
      (((extractHalfword (answer.extractLsb' 192 64) 2).zeroExtend 64) &&& (16383 : Word)).truncate 32 := by
    rw [vx31,ux31,ux6,tx6,address]
    simp only [MachineState.getHalfword,dword,offset,last]
  have shape (q : Word) : (t238Mask s n answer).getMem q =
      if q=BitVec.ofNat 64 (base+24) then replaceWord32 (answer.extractLsb' 192 64) 1
        ((((extractHalfword (answer.extractLsb' 192 64) 2).zeroExtend 64) &&& (16383 : Word)).truncate 32)
      else t.getMem q := by
    change (execInstrBr v (.SW .x12 .x31 28)).getMem q=_
    simp only [execInstrBr,MachineState.getMem_setPC,MachineState.setWord32]
    rw [vx12,address,dword,offset,value]
    by_cases here : q=BitVec.ofNat 64 (base+24)
    · subst here
      rw [if_pos rfl,MachineState.getMem_setMem_eq,vmem,last]
    · rw [if_neg here,MachineState.getMem_setMem_ne here,vmem]
  funext q
  change (t238Mask s n answer).getMem q=(writeBits s (BitVec.ofNat 64 base) (pad238 answer)).getMem q
  rw [shape]
  by_cases lastWord : q=BitVec.ofNat 64 (base+24)
  · rw [if_pos lastWord,lastWord,output_word s base 3 _ aligned (by decide)]
    exact t238_last_word answer
  · rw [if_neg lastWord]
    change (writeBits s (BitVec.ofNat 64 base) answer).getMem q=_
    by_cases someWord : ∃ k < 4, q=BitVec.ofNat 64 (base+8*k)
    · obtain ⟨k,hk,rfl⟩ := someWord
      rw [output_word s base k _ aligned hk,output_word s base k _ aligned hk]
      apply low_t238
      by_contra! large
      have eq : k=3 := by omega
      exact lastWord (by rw [eq])
    · have away : ∀ i < 32, q ≠ alignToDword (BitVec.ofNat 64 base + BitVec.ofNat 64 i) := by
        intro i hi eq; apply someWord
        exact ⟨i/8, by omega, eq.trans (by rw [← BitVec.ofNat_add, word_address base i aligned])⟩
      exact (writeBits_memory_outside s _ q answer away).trans
        (writeBits_memory_outside s _ q (pad238 answer) away).symm

end TwoPermutationPrototype.RV64
