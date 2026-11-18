-- Pair-heads copy of QuartetCheckBlockCopy (stack/check/work/mkcopy.py); edits below are marked PAIR.
import CommitGolfCandidate.PairCheckQBlockCode
import CommitGolfCandidate.PairCheckNamespaces
import CommitGolfCandidate.QuartetCheckCopyKernel
import CommitGolfCandidate.TwoPermutationOpeningCopyBytes
import CommitGolfCandidate.ProjectedHalfwordMemory

/-! The four slot fills of the quartet block: the leaf digest by four doubleword moves (words 373–380)
and the three proof siblings by sixteen halfword moves each, stored 72 bytes above the slot base. -/

namespace TwoPermutationPrototype.PairCk.Packed.Checker
open  TwoPermutationPrototype.Packed TwoPermutationPrototype.Packed.Checker TwoPermutationPrototype.PairCk.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype

set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

/-! ### The leaf digest: four doubleword moves -/

def qLeafCopyCode : List Instr :=
  [.LD .x31 .x23 0, .SD .x28 .x31 72, .LD .x31 .x23 8, .SD .x28 .x31 80,
   .LD .x31 .x23 16, .SD .x28 .x31 88, .LD .x31 .x23 24, .SD .x28 .x31 96]

def qLeafCopied (s : MachineState) := straight qLeafCopyCode s 8

private theorem store_register (s : MachineState) (address value : Word) (r : Reg) :
    (s.setMem address value).getReg r = s.getReg r := by cases r <;> rfl

private theorem leaf_copy_keeps (s : MachineState) (count : Nat) (bounded : count ≤ 8)
    (reg : Reg) (notScratch : reg ≠ .x31) :
    (straight qLeafCopyCode s count).getReg reg = s.getReg reg := by
  interval_cases count <;>
    simp only [straight,qLeafCopyCode,List.take,List.foldl,execInstrBr,MachineState.getReg_setPC,
      store_register,MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm notScratch)]

theorem q_leaf_copied_register (s : MachineState) (r : Reg) (other : r ≠ .x31) :
    (qLeafCopied s).getReg r = s.getReg r :=
  leaf_copy_keeps s 8 (by decide) r other

theorem q_leaf_copied_pc (s : MachineState) : (qLeafCopied s).pc = s.pc+32 := by
  simp [qLeafCopied,straight,qLeafCopyCode,execInstrBr,MachineState.setPC,BitVec.add_assoc]

theorem execute_q_leaf_copy (s : MachineState) (pc : s.pc = BitVec.ofNat 64 (4096+4*373))
    (readable : ∀ j : Fin 4, accessValid (s.getReg .x23+BitVec.ofNat 64 (8*j.val)) 8 = true)
    (writable : ∀ j : Fin 4, accessValid (s.getReg .x28+BitVec.ofNat 64 (72+8*j.val)) 8 = true) :
    GroupHop s (qLeafCopied s) 8 := by
  intro fuel
  apply execute_unit_steps (states := straight qLeafCopyCode s)
  intro i bounded
  have src := leaf_copy_keeps s i (by omega) .x23 (by decide)
  have dst := leaf_copy_keeps s i (by omega) .x28 (by decide)
  have r0 := readable ⟨0,by decide⟩
  have r1 := readable ⟨1,by decide⟩
  have r2 := readable ⟨2,by decide⟩
  have r3 := readable ⟨3,by decide⟩
  have w0 := writable ⟨0,by decide⟩
  have w1 := writable ⟨1,by decide⟩
  have w2 := writable ⟨2,by decide⟩
  have w3 := writable ⟨3,by decide⟩
  have valid : memoryArgumentsValid (straight qLeafCopyCode s i) (qLeafCopyCode[i]?.getD .EBREAK) = true := by
    interval_cases i <;>
      simp only [qLeafCopyCode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
        memoryArgumentsValid,memAccess,src,dst] <;>
      first | exact r0 | exact r1 | exact r2 | exact r3 | exact w0 | exact w1 | exact w2 | exact w3
  refine ⟨.base (qLeafCopyCode[i]?.getD .EBREAK),fetch_at _ (373+i) _ (by omega) ?_ ?_,?_,?_⟩
  · interval_cases i <;> simp [straight,qLeafCopyCode,execInstrBr,pc,MachineState.setPC]
  · interval_cases i <;> rfl
  · simp only [ordinaryStep]
    interval_cases i <;> simp only [qLeafCopyCode,List.getElem?_cons_zero,List.getElem?_cons_succ,
      Option.getD_some] at valid ⊢ <;> simp only [valid, ite_true] <;> rfl
  · interval_cases i <;> rfl

attribute [local simp] Opening.getReg_setMem Opening.getReg_setReg MachineState.getReg_setPC

@[local simp] private theorem copy_mem_set_reg (s : MachineState) (reg : Reg) (value : Word) :
    (s.setReg reg value).mem = s.mem := by cases reg <;> rfl

@[local simp] private theorem copy_mem_set_pc (s : MachineState) (pc : Word) :
    (s.setPC pc).mem = s.mem := rfl

private theorem mem_store (s : MachineState) (address value : Word) :
    (s.setMem address value).mem = fun word => if word = address then value else s.mem word := by
  funext word
  simp [MachineState.setMem]

theorem q_leaf_copied_memory (s : MachineState)
    (separate : ∀ i j : Fin 4, s.getReg .x23+BitVec.ofNat 64 (8*i.val) ≠
      (s.getReg .x28+72#64)+BitVec.ofNat 64 (8*j.val)) :
    (qLeafCopied s).mem = (Opening.fourWordStore s (s.getReg .x23) (s.getReg .x28+72#64)).mem := by
  have h10 := separate 1 0
  have h20 := separate 2 0
  have h21 := separate 2 1
  have h30 := separate 3 0
  have h31 := separate 3 1
  have h32 := separate 3 2
  simp [qLeafCopied,straight,qLeafCopyCode,Opening.fourWordStore,execInstrBr,
    signExtend12,mem_store,MachineState.getMem,BitVec.add_assoc] at h10 h20 h21 h30 h31 h32 ⊢
  all_goals simp [h10,h20,h21,h30,h31,h32]

/-! ### The proof siblings: sixteen halfword moves per slot -/

theorem q_sibling_fetch_load (j : Nat) (valid : 1 ≤ j ∧ j ≤ 3) (k : Nat) (inside : k < 16) (s : MachineState)
    (pc : s.pc = BitVec.ofNat 64 (4096+4*(qHeadStart j+3+2*k))) :
    fetch pairImage s = some (.base (.LHU .x31 .x21 (BitVec.ofNat 12 (2*k)))) := by
  obtain ⟨lo,hi⟩ := valid
  refine fetch_at s _ _ (by unfold qHeadStart; omega) pc ?_
  interval_cases j <;> interval_cases k <;> rfl

theorem q_sibling_fetch_store (j : Nat) (valid : 1 ≤ j ∧ j ≤ 3) (k : Nat) (inside : k < 16) (s : MachineState)
    (pc : s.pc = BitVec.ofNat 64 (4096+4*(qHeadStart j+3+2*k+1))) :
    fetch pairImage s = some (.base (.SH .x28 .x31 (BitVec.ofNat 12 (72+2*k)))) := by
  obtain ⟨lo,hi⟩ := valid
  refine fetch_at s _ _ (by unfold qHeadStart; omega) pc ?_
  interval_cases j <;> interval_cases k <;> rfl

def qSiblingCode (j : Nat) (valid : 1 ≤ j ∧ j ≤ 3) : QuartetCheckCopy.CopyCode where
  image := pairImage
  start := qHeadStart j+3
  count := 16
  source := .x21
  dest := .x28
  destOffset := 72
  sourceTemp := by decide
  destTemp := by decide
  offsetBound := by decide
  load := fun k inside s pc => q_sibling_fetch_load j valid k inside s pc
  store := fun k inside s pc => q_sibling_fetch_store j valid k inside s pc

def qSiblingCopied (j : Nat) (valid : 1 ≤ j ∧ j ≤ 3) (s : MachineState) : MachineState :=
  QuartetCheckCopy.copyField (qSiblingCode j valid) s

theorem q_sibling_bytes (j : Nat) (valid : 1 ≤ j ∧ j ≤ 3) (s : MachineState) (source target : Nat)
    (ready : QuartetCheckCopy.CopyReady (qSiblingCode j valid) s source target 0) (order : target ≤ source) :
    let t := qSiblingCopied j valid s
    (∀ i<32, t.getByte (BitVec.ofNat 64 (target+i))=s.getByte (BitVec.ofNat 64 (source+i))) ∧
    (∀ q : Word, (∀ i<32, q≠BitVec.ofNat 64 (target+i)) → t.getByte q=s.getByte q) := by
  have sb : source+2*16≤MEMORY_BYTES := ready.srcBound
  have tb : target+2*16≤MEMORY_BYTES := ready.dstBound
  have lim : MEMORY_BYTES<2^64 := by decide
  have mem := QuartetCheckCopy.copy_field_memory _ _ _ _ ready
  have bytes := ProjectedHalfword.forward_memory 16 s source target order (by omega) (by omega)
        ready.srcAligned ready.dstAligned
  change (qSiblingCopied j valid s).mem=(ProjectedHalfword.copyLoopMemory false 16 s _ _).mem at mem
  simpa only [MachineState.getByte, MachineState.getMem,mem] using bytes

end TwoPermutationPrototype.PairCk.Packed.Checker
