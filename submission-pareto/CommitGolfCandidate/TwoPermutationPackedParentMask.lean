import CommitGolfCandidate.TwoPermutationPackedParents
import CommitGolfCandidate.TwoPermutationParentBatchesContent
import CommitGolfCandidate.TwoPermutationCounted

namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open CommitGolfCandidate (write_bits_digest read_digest_word writeBits_memory_outside writeBits_register
  read_buffer_memory_congr write_bits_read_outside checkEvaluation check_evaluation_pure
  check_evaluation_bind check_evaluation_public)
set_option maxRecDepth 8192
set_option maxHeartbeats 2500000

/-- The stored internal digest: the reply's low 238 bits, zero-extended. -/
def projectReply (answer : BitVec 256) : BitVec 256 := CommitGolfCandidate.ShortTree.padLow answer

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

theorem packed_parent_memory (state : MachineState) (n : Nat) (answer : BitVec 256)
    (regs : ParentRegs state n) (mask : state.getReg .x30=CommitGolfCandidate.ShortTree.digestMaskWord)
    (inside : n<2^24) :
    (packedParentAfter state n answer).mem=(parentWritten state n (projectReply answer)).mem := by
  have target := regs.target
  have base : wordAddress (treeWord n) = BitVec.ofNat 64 (8*treeWord n) := rfl
  have aligned : (8*treeWord n) % 8 = 0 := by omega
  let first := parentWritten state n answer
  have firstTarget : first.getReg .x12 = BitVec.ofNat 64 (8*treeWord n) := by
    unfold first parentWritten
    rw [writeBits_register,target,base]
  have firstMask : first.getReg .x30 = CommitGolfCandidate.ShortTree.digestMaskWord := by
    unfold first parentWritten
    rw [writeBits_register,mask]
  have address : first.getReg .x12+signExtend12 24 = BitVec.ofNat 64 (8*treeWord n+24) := by
    rw [firstTarget]
    change BitVec.ofNat 64 (8*treeWord n)+BitVec.ofNat 64 24=_
    rw [←BitVec.ofNat_add]
  have top : first.getMem (BitVec.ofNat 64 (8*treeWord n+24)) = answer.extractLsb' 192 64 := by
    unfold first parentWritten
    rw [base]
    exact CommitGolfCandidate.ShortTree.reply_top_word state _ answer aligned
  let loaded := execInstrBr first (.LD .x31 .x12 24)
  let anded := execInstrBr loaded (.AND .x31 .x31 .x30)
  have loaded31 : loaded.getReg .x31 = answer.extractLsb' 192 64 := by
    simp only [loaded,execInstrBr,MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (show Reg.x31≠Reg.x0 by decide)]
    rw [address,top]
  have loaded30 : loaded.getReg .x30 = CommitGolfCandidate.ShortTree.digestMaskWord := by
    simp only [loaded,execInstrBr,MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (show Reg.x31≠Reg.x30 by decide)]
    exact firstMask
  have anded31 : anded.getReg .x31 = (CommitGolfCandidate.ShortTree.padLow answer).extractLsb' 192 64 := by
    simp only [anded,execInstrBr,MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (show Reg.x31≠Reg.x0 by decide)]
    rw [loaded31,loaded30,CommitGolfCandidate.ShortTree.top_word_mask]
  have anded12 : anded.getReg .x12 = first.getReg .x12 := by
    simp only [anded,loaded,execInstrBr,MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (show Reg.x31≠Reg.x12 by decide)]
  have andedMem : anded.mem = first.mem := rfl
  have stored : (packedParentAfter state n answer).mem =
      (anded.setMem (anded.getReg .x12 + signExtend12 24) (anded.getReg .x31)).mem := rfl
  rw [stored,anded12,address,anded31]
  have whole := CommitGolfCandidate.ShortTree.masked_reply_memory state (8*treeWord n) answer aligned
    (by unfold treeWord; omega)
  rw [← base] at whole
  refine Eq.trans ?_ whole
  change (fun q => if q == _ then _ else anded.mem q) = (fun q => if q == _ then _ else first.mem q)
  rw [andedMem]

end TwoPermutationPrototype.RV64
