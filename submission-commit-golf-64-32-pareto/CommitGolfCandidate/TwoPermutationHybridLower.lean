import CommitGolfCandidate.TwoPermutationWideParents
import CommitGolfCandidate.TwoPermutationPackedParentControl

namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] execute

abbrev hybridCut : Nat := 65535
abbrev fullSpan : Nat := 32768

def lowerNext (left : Nat) : Word := if left=0 then 610804 else 217580

structure HybridLowerCode (image : Image) where
  words : ∀ i < fullSpan, ParentWordsAt image (wideParentPC 217580 i)
  branch : ∀ s : MachineState, s.pc=610796 → fetch image s=some (.base (.BEQ .x12 .x18 8))
  back : ∀ s : MachineState, s.pc=610800 → fetch image s=some (.base (.JAL .x0 1703932))

theorem full_trace_frame (remaining count : Nat) (s : MachineState) (reg : Reg)
    (src : Reg.x10≠reg) (dst : Reg.x12≠reg) {out : MachineState}
    (hit : out ∈ support (parentsTrace remaining count s)) : out.getReg reg = s.getReg reg := by
  induction count generalizing s with
  | zero => simp only [parentsTrace,support_pure,Set.mem_singleton_iff] at hit;rw [hit]
  | succ count ih =>
    simp only [parentsTrace,mem_support_bind_iff] at hit
    obtain ⟨answer,_,tail⟩ := hit
    rw [ih _ tail]
    simp only [parentAfter,execInstrBr,MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ src,MachineState.getReg_setReg_ne _ _ _ _ dst,
      parentWritten,CommitGolfCandidate.writeBits_register]

theorem packed_trace_frame (remaining count : Nat) (s : MachineState) {out : MachineState}
    (hit : out ∈ support (packedParentsTrace remaining count s)) : out.getReg .x8=s.getReg .x8 := by
  induction count generalizing s with
  | zero => simp only [packedParentsTrace,support_pure,Set.mem_singleton_iff] at hit;rw [hit]
  | succ count ih =>
    simp only [packedParentsTrace,mem_support_bind_iff] at hit
    obtain ⟨answer,_,tail⟩ := hit
    exact (ih _ tail).trans (packed_parent_keeps_register s _ answer .x8 (by decide) (by decide))

theorem lower_latch (image : Image) (code : HybridLowerCode image) (left fuel : Nat) (s : MachineState)
    (bound : hybridCut+left<2^24) (regs : ParentRegs s (hybridCut+left))
    (cut : s.getReg .x18=wordAddress (treeWord hybridCut)) (pc : s.pc=610796) :
    execute image (longParentLatchCost left+fuel) s true =
      (do let y ← execute image fuel (s.setPC (lowerNext left)) true
          return y.charge (longParentLatchCost left) 0) := by
  have equal : s.getReg .x12=s.getReg .x18 ↔ left=0 := by
    rw [regs.target,cut]
    constructor
    · intro same
      have index := wordAddress_injective_of_bound (by unfold treeWord;omega)
        (by decide : treeWord hybridCut < 2^61) same
      unfold treeWord at index
      omega
    · rintro rfl; rfl
  by_cases last : left=0
  · have step : ordinaryStep s (.base (.BEQ .x12 .x18 8))=some (s.setPC 610804) := by
      simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,equal.mpr last,signExtend13]
    rw [longParentLatchCost,if_pos last,lowerNext,if_pos last,Nat.add_comm 1 fuel,
      CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (code.branch s pc) step]
    rfl
  · let mid := s.setPC 610800
    have diff : s.getReg .x12≠s.getReg .x18 := fun h => last (equal.mp h)
    have step : ordinaryStep s (.base (.BEQ .x12 .x18 8))=some mid := by
      simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,diff,mid]
    have jump : ordinaryStep mid (.base (.JAL .x0 1703932))=some (s.setPC 217580) := by
      simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,mid,MachineState.setReg,MachineState.setPC]
      rfl
    rw [longParentLatchCost,if_neg last,lowerNext,if_neg last,show 2+fuel=(fuel+1)+1 by omega,
      CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (code.branch s pc) step,
      CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (code.back mid rfl) jump]
    simp [instructionCycles,Execution.charge,←Nat.add_assoc]

def hybridLowerFor (span : Nat) : Nat → MachineState → OracleComp World MachineState
  | 0,s => pure s
  | n+1,s => do
    let mid ← parentsTrace (hybridCut+span*n) span s
    hybridLowerFor span n (mid.setPC (lowerNext (span*n)))

abbrev hybridLower := hybridLowerFor fullSpan

def lowerCost (rate n : Nat) := rate*fullSpan*n+(2*n-1)

private theorem lower_step (rate n : Nat) :
    lowerCost rate (n+1) = rate*fullSpan+longParentLatchCost (fullSpan*n)+lowerCost rate n := by
  cases n with
  | zero => simp [lowerCost,longParentLatchCost]
  | succ n =>
    have nz : fullSpan*(n+1)≠0 := by unfold fullSpan; omega
    simp only [lowerCost,longParentLatchCost,nz,ite_false]
    rw [Nat.mul_succ (rate*fullSpan) (n+1)];omega

theorem lower_run (image : Image) (code : HybridLowerCode image)
    (n fuel : Nat) (s : MachineState) (bound : hybridCut+fullSpan*n<2^24)
    (regs : ParentRegs s (hybridCut+fullSpan*n)) (pc : 0<n → s.pc=217580)
    (cut : s.getReg .x18=wordAddress (treeWord hybridCut)) :
    execute image (lowerCost 3 n+fuel) s true =
      (do let out ← hybridLower n s
          let res ← execute image fuel out true
          return res.charge (lowerCost 10 n) (fullSpan*n)) := by
  induction n generalizing s with
  | zero => simp [hybridLower,hybridLowerFor,lowerCost,Execution.charge]
  | succ n ih =>
    have amount : hybridCut+fullSpan*(n+1)=hybridCut+fullSpan*n+fullSpan := by rw [Nat.mul_succ,Nat.add_assoc]
    rw [amount] at regs bound
    have enter : s.pc=wideParentPC 217580 0 := pc (by omega)
    rw [lower_step 3,
      show 3*fullSpan+longParentLatchCost (fullSpan*n)+lowerCost 3 n+fuel=
        3*fullSpan+(longParentLatchCost (fullSpan*n)+(lowerCost 3 n+fuel)) by omega,
      wide_parent_segment image 217580 fullSpan code.words (hybridCut+fullSpan*n) fullSpan 0 _ s bound (by decide) regs enter]
    simp only [hybridLower,hybridLowerFor,bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro mid hit
    have post := wide_parent_segment_post 217580 (hybridCut+fullSpan*n) fullSpan 0 s regs enter hit
    have saved := (full_trace_frame _ _ s .x18 (by decide) (by decide) hit).trans cut
    rw [lower_latch image code (fullSpan*n) _ mid (by omega) post.1 saved post.2]
    let next := mid.setPC (lowerNext (fullSpan*n))
    have nr : ParentRegs next (hybridCut+fullSpan*n) :=
      ⟨post.1.source,post.1.target,post.1.selector,post.1.size,post.1.primitive,post.1.heap⟩
    have begin (h : 0<n) : next.pc=217580 := by
      change lowerNext (fullSpan*n)=_;rw [lowerNext,if_neg (by unfold fullSpan; omega)]
    rw [ih next (by omega) nr begin saved,lower_step 10]
    rw [Nat.mul_succ fullSpan n]
    simp [next,Execution.charge,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

theorem lower_post (n : Nat) (s : MachineState) (entry : 0<n → s.pc=217580)
    (regs : ParentRegs s (hybridCut+fullSpan*n)) {out : MachineState}
    (hit : out ∈ support (hybridLower n s)) :
    ParentRegs out hybridCut ∧ (0<n → out.pc=610804) ∧ out.getReg .x8=s.getReg .x8 := by
  induction n generalizing s with
  | zero => simp only [hybridLower,hybridLowerFor,support_pure,Set.mem_singleton_iff] at hit;subst out;exact ⟨regs,by omega,rfl⟩
  | succ n ih =>
    simp only [hybridLower,hybridLowerFor,mem_support_bind_iff] at hit
    obtain ⟨mid,path,tail⟩ := hit
    have enter : s.pc=wideParentPC 217580 0 := entry (by omega)
    have r : ParentRegs s (hybridCut+fullSpan*n+fullSpan) := by
      rw [show hybridCut+fullSpan*n+fullSpan=hybridCut+fullSpan*(n+1) by rw [Nat.mul_succ,Nat.add_assoc]];exact regs
    have post := wide_parent_segment_post 217580 (hybridCut+fullSpan*n) fullSpan 0 s r enter path
    let next := mid.setPC (lowerNext (fullSpan*n))
    have nr : ParentRegs next (hybridCut+fullSpan*n) :=
      ⟨post.1.source,post.1.target,post.1.selector,post.1.size,post.1.primitive,post.1.heap⟩
    have begin (h : 0<n) : next.pc=217580 := by
      change lowerNext (fullSpan*n)=_;rw [lowerNext,if_neg (by unfold fullSpan; omega)]
    have after := ih next begin nr tail
    refine ⟨after.1,?_,after.2.2.trans (full_trace_frame _ _ s .x8 (by decide) (by decide) (out:=mid) path)⟩
    intro _
    cases n with
    | zero => simp only [hybridLower,hybridLowerFor,support_pure,Set.mem_singleton_iff] at tail;rw [tail];rfl
    | succ n => exact after.2.1 (by omega)

end TwoPermutationPrototype.RV64
