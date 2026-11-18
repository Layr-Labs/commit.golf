import CommitGolfCandidate.TwoPermutationPackedCheckerSteps
import CommitGolfCandidate.ProjectedMask

/-! The lower-path compression reply is kept at levels 0 and 1 and projected
at every later level. The appended branch does not change cap processing. -/
namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp OracleSpec ShortTree
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
attribute [local irreducible] execute readBuffer writeBits capCompressionAnswer

def lowerMaskCost (left : Nat) : Nat := if 14 ≤ left then 4 else 5

def lowerMask (s : MachineState) (left : Nat) : MachineState :=
  ((if 14 ≤ left then s else s.setHalfword (s.getReg .x23 + signExtend12 30) 0).setReg .x31 14).setPC 5040

def lowerReply (s : MachineState) (answer : BitVec 256) (left : Nat) : MachineState :=
  lowerMask (capCompressionAnswer s answer) left

private theorem one (s t : MachineState) (i : Instr)
    (f : fetch packedImage s=some (.base i)) (step : ordinaryStep s (.base i)=some t)
    (cost : instructionCycles (.base i)=1) : GroupHop s t 1 := by
  intro fuel
  rw [Nat.add_comm 1 fuel,execute_ordinary_step _ _ _ _ _ _ f step,cost]

theorem lower_mask_run (s : MachineState) (left : Nat) (pc : s.pc=5036)
    (counter : s.getReg .x29=BitVec.ofNat 64 left) (bounded : left<2^64)
    (valid : accessValid (s.getReg .x23 + signExtend12 30) 2=true) :
    GroupHop s (lowerMask s left) (lowerMaskCost left) := by
  let a := s.setPC 5568
  let b := (a.setReg .x31 14).setPC 5572
  have h0 : GroupHop s a 1 := by
    apply one _ _ (.JAL .x0 532)
    · exact fetch_at s 235 _ (by decide) pc rfl
    · simp [a,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend21,pc,MachineState.setReg]
    · rfl
  have h1 : GroupHop a b 1 := by
    apply one _ _ (.ADDI .x31 .x0 14)
    · exact fetch_at a 368 _ (by decide) rfl rfl
    · simp [a,b,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend12,
        MachineState.getReg,MachineState.setReg,MachineState.setPC]
    · rfl
  have bit : (s.regs .x29).ult (14 : Word) = decide (left<14) := by
    change (s.getReg .x29).ult (14 : Word) = decide (left<14)
    rw [counter]
    change decide ((BitVec.ofNat 64 left).toNat<14)=decide (left<14)
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt bounded]
  by_cases full : 14≤left
  · let c := b.setPC 5580
    have h2 : GroupHop b c 1 := by
      apply one _ _ (.BGEU .x29 .x31 8)
      · exact fetch_at b 369 _ (by decide) rfl rfl
      · simp [a,b,c,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend13,
          MachineState.getReg,MachineState.setReg,MachineState.setPC]
        exact bit.trans (decide_eq_false (Nat.not_lt.mpr full))
      · rfl
    have h3 : GroupHop c (lowerMask s left) 1 := by
      apply one _ _ (.JAL .x0 2096612)
      · exact fetch_at c 371 _ (by decide) rfl rfl
      · simp [a,b,c,lowerMask,full,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,
          signExtend21,MachineState.setReg,MachineState.setPC]
      · rfl
    simpa only [lowerMaskCost,if_pos full] using ((h0.thenDo h1).thenDo h2).thenDo h3
  · let c := b.setPC 5576
    let d := (c.setHalfword (s.getReg .x23 + signExtend12 30) 0).setPC 5580
    have h2 : GroupHop b c 1 := by
      apply one _ _ (.BGEU .x29 .x31 8)
      · exact fetch_at b 369 _ (by decide) rfl rfl
      · simp [a,b,c,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend13,
          MachineState.getReg,MachineState.setReg,MachineState.setPC]
        exact bit.trans (decide_eq_true (Nat.lt_of_not_ge full))
      · rfl
    have h3 : GroupHop c d 1 := by
      apply one _ _ (.SH .x23 .x0 30)
      · exact fetch_at c 370 _ (by decide) rfl rfl
      · have validC : accessValid (c.getReg .x23 + signExtend12 30) 2=true := by
          simpa [a,b,c,MachineState.getReg,MachineState.setReg,MachineState.setPC] using valid
        simp only [ordinaryStep,memoryArgumentsValid,memAccess,validC,↓reduceIte]
        rfl
      · rfl
    have h4 : GroupHop d (lowerMask s left) 1 := by
      apply one _ _ (.JAL .x0 2096612)
      · exact fetch_at d 371 _ (by decide) rfl rfl
      · simp [a,b,c,d,lowerMask,full,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,
          signExtend21,MachineState.setHalfword,MachineState.setMem,MachineState.getMem,MachineState.setReg,MachineState.setPC]
      · rfl
    simpa only [lowerMaskCost,if_neg full] using (((h0.thenDo h1).thenDo h2).thenDo h3).thenDo h4

theorem lower_reply_register (s : MachineState) (answer : BitVec 256) (left : Nat) (r : Reg)
    (different : r≠.x31) : (lowerReply s answer left).getReg r=s.getReg r := by
  unfold lowerReply lowerMask
  split
  · rw [MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm different)]
    exact cap_compression_register s answer r
  · rw [MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm different)]
    have same (state : MachineState) (address : Word) :
        (state.setHalfword address 0).getReg r=state.getReg r := by cases r <;> rfl
    rw [same]
    exact cap_compression_register s answer r

theorem lower_reply_memory (s : MachineState) (answer : BitVec 256) (left target : Nat)
    (dst : s.getReg .x12=BitVec.ofNat 64 target) (mask : s.getReg .x23=s.getReg .x12)
    (aligned : target%8=0) (bound : target+32≤2^64) :
    (lowerReply s answer left).mem=(writeBits s (BitVec.ofNat 64 target)
      (if 14≤left then answer else padLow answer)).mem := by
  unfold lowerReply lowerMask
  split
  · simp only [MachineState.setPC,MachineState.setReg,capCompressionAnswer,dst]
  · simp only [MachineState.setPC,MachineState.setReg]
    rw [cap_compression_register,mask,dst]
    unfold capCompressionAnswer
    change ((writeBits s (s.getReg .x12) answer).setHalfword
      (BitVec.ofNat 64 target + BitVec.ofNat 64 30) 0).mem=_
    rw [dst,←BitVec.ofNat_add]
    exact masked_reply_memory s target answer aligned bound

theorem lower_hash_step (s : MachineState) (source target left : Nat)
    (pc : s.pc=5032) (src : s.getReg .x10=BitVec.ofNat 64 source)
    (dst : s.getReg .x12=BitVec.ofNat 64 target) (mask : s.getReg .x23=s.getReg .x12)
    (counter : s.getReg .x29=BitVec.ofNat 64 left) (bounded : left<2^64)
    (selector : s.getReg .x5=0 ∧ s.getReg .x11=64 ∧ s.getReg .x13=0)
    (srcRoom : source+64≤MEMORY_BYTES) (dstRoom : target+32≤MEMORY_BYTES)
    (srcAlign : source%8=0) (dstAlign : target%8=0) (fuel : Nat) :
    execute packedImage (1+lowerMaskCost left+fuel) s false = do
      let answer ← World.query (.inr (.inl (readBuffer s (source+32) 32 ++ readBuffer s source 32)))
      let result ← execute packedImage fuel (lowerReply s answer left) false
      return result.charge (8+lowerMaskCost left) 1 := by
  have lim : MEMORY_BYTES<2^64 := by decide
  have srcV : rangeValid (s.getReg .x10) 64=true := by
    simp only [src,rangeValid,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : source<2^64),decide_eq_true_eq];exact srcRoom
  have dstV : rangeValid (s.getReg .x12) 32=true := by
    simp only [dst,rangeValid,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : target<2^64),decide_eq_true_eq];exact dstRoom
  have asrc : (s.getReg .x10).toNat%8=0 := by simpa [src,Nat.mod_eq_of_lt (by omega : source<2^64)] using srcAlign
  have adst : (s.getReg .x12).toNat%8=0 := by simpa [dst,Nat.mod_eq_of_lt (by omega : target<2^64)] using dstAlign
  have hash := cap_compression_execute packedImage s (project_fetch .lower s pc) selector srcV dstV asrc adst
    (lowerMaskCost left+fuel) false
  change execute packedImage (1+(lowerMaskCost left+fuel)) s false = (do
    let answer ← World.query (.inr (.inl (readBuffer s (s.getReg .x10).toNat 64)))
    let result ← execute packedImage (lowerMaskCost left+fuel) (capCompressionAnswer s answer) false
    return result.charge 8 1) at hash
  rw [src,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : source<2^64),read_compression_halves s source srcAlign] at hash
  rw [Nat.add_assoc,hash]
  congr 1
  funext answer
  change BitVec 256 at answer
  let raw := capCompressionAnswer s answer
  have after : raw.pc=5036 := by
    have moved : raw.pc=s.pc+4 := by unfold raw capCompressionAnswer writeBits; rfl
    rw [moved,pc];rfl
  have cnt : raw.getReg .x29=BitVec.ofNat 64 left := (cap_compression_register _ _ _).trans counter
  have am : accessValid (raw.getReg .x23 + signExtend12 30) 2=true := by
    rw [show raw.getReg .x23=s.getReg .x23 from cap_compression_register _ _ _,mask,dst]
    change accessValid (BitVec.ofNat 64 target + BitVec.ofNat 64 30) 2=true
    rw [←BitVec.ofNat_add]
    simp only [accessValid,rangeValid,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : target+30<2^64),
      Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨by omega,by omega⟩
  rw [lower_mask_run raw left after cnt bounded am fuel]
  simp only [lowerReply,raw,bind_assoc,pure_bind,Execution.charge,Nat.zero_add,←Nat.add_assoc]

end TwoPermutationPrototype.Packed.Checker
