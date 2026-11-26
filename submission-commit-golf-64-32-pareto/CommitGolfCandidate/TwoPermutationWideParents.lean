import CommitGolfCandidate.TwoPermutationParentLoop

namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] execute parentAfter

structure ParentWordsAt (image : Image) (pc : Word) : Prop where
  call : ∀ s : MachineState, s.pc=pc → fetch image s=some (.base .ECALL)
  source : ∀ s : MachineState, s.pc=pc+4 →
    fetch image s=some (.base (.ADDI .x10 .x10 4032))
  target : ∀ s : MachineState, s.pc=pc+8 →
    fetch image s=some (.base (.ADDI .x12 .x12 4064))

private theorem parent_call_at (image : Image) (s : MachineState) (n fuel : Nat)
    (bound : n < 2^24) (regs : ParentRegs s n)
    (fetched : fetch image s=some (.base .ECALL)) :
    execute image (fuel+1) s true =
      (do let answer ← (liftM (World.query (.inr (.inl (parentInput s n)))) : OracleComp World (BitVec 256))
          let result ← execute image fuel (parentWritten s n answer) true
          return result.charge 8 1) := by
  have source := word_address_value (word := treeWord (2*n)) (by unfold treeWord; omega)
  have target := word_address_value (word := treeWord n) (by unfold treeWord; omega)
  have inputRange : 8*treeWord (2*n)+64 ≤ MEMORY_BYTES := by unfold treeWord MEMORY_BYTES; omega
  have outputRange : 8*treeWord n+32 ≤ MEMORY_BYTES := by unfold treeWord MEMORY_BYTES; omega
  have query : oracleInput s=some (.inl (parentInput s n)) := by
    have kind : (s.getReg .x13).toNat=0 := by rw [regs.primitive]; rfl
    unfold oracleInput
    dsimp only
    rw [kind]
    simp [regs.source,regs.target,regs.size,COMPRESSION_INPUT_LENGTH,COMPRESSION_OUTPUT_LENGTH,
      rangeValid,source,target,inputRange,outputRange,parentInput]
  simp [execute,fetched,regs.selector,query,writeOracleAnswer,regs.target,parentWritten,
    oracleCycles,COMPRESSION_CYCLES]
  rfl

private theorem parent_triple_at (image : Image) (s : MachineState) (n fuel : Nat) (pc : Word)
    (here : s.pc=pc) (bound : n<2^24) (regs : ParentRegs s n)
    (fetched : ParentWordsAt image pc) :
    execute image (3+fuel) s true =
      (do let answer ← (liftM (World.query (.inr (.inl (parentInput s n)))) : OracleComp World (BitVec 256))
          let result ← execute image fuel (parentAfter s n answer) true
          return result.charge 10 1) := by
  rw [show 3+fuel=(fuel+2)+1 by omega,parent_call_at image s n _ bound regs (fetched.call s here)]
  apply bind_congr_of_forall_mem_support
  intro answer _
  let first := parentWritten s n answer
  let second := execInstrBr first (.ADDI .x10 .x10 4032)
  have firstPC : first.pc=pc+4 := by simp only [first,parentWritten,written_pc,here]
  have secondPC : second.pc=pc+8 := by
    change first.pc+4=_
    rw [firstPC,BitVec.add_assoc]
    rfl
  have advance : ordinaryStep second (.base (.ADDI .x12 .x12 4064))=some (parentAfter s n answer) := by
    unfold parentAfter
    rfl
  rw [CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (fetched.source first firstPC)
    (show ordinaryStep first _=some second from rfl),
    CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (fetched.target second secondPC) advance]
  simp [instructionCycles,Execution.charge,←Nat.add_assoc]

def wideParentPC (base : Word) (slot : Nat) : Word := base+BitVec.ofNat 64 (12*slot)

private theorem wide_parent_pc_succ (base : Word) (slot : Nat) :
    wideParentPC base slot+12=wideParentPC base (slot+1) := by
  change base+BitVec.ofNat 64 (12*slot)+BitVec.ofNat 64 12 =
    base+BitVec.ofNat 64 (12*(slot+1))
  rw [BitVec.add_assoc,←BitVec.ofNat_add]
  rw [show 12*slot+12=12*(slot+1) by omega]

theorem wide_parent_segment (image : Image) (base : Word) (span : Nat)
    (fetches : ∀ i < span, ParentWordsAt image (wideParentPC base i))
    (remaining count slot fuel : Nat) (s : MachineState)
    (bound : remaining+count<2^24) (inside : slot+count≤span)
    (regs : ParentRegs s (remaining+count)) (pc : s.pc=wideParentPC base slot) :
    execute image (3*count+fuel) s true =
      (do let mid ← parentsTrace remaining count s
          let result ← execute image fuel mid true
          return result.charge (10*count) count) := by
  induction count generalizing slot s with
  | zero => simp [parentsTrace,Execution.charge]
  | succ count ih =>
    rw [show 3*(count+1)+fuel=3+(3*count+fuel) by omega,
      parent_triple_at image s _ _ _ pc bound regs (fetches slot (by omega))]
    simp only [parentsTrace,bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro answer _
    have next := next_parent_regs s (remaining+count) answer (by simpa only [Nat.add_assoc] using regs)
    have atNext := (parent_pc s (remaining+(count+1)) answer).trans
      ((congrArg (·+12) pc).trans (wide_parent_pc_succ base slot))
    rw [ih (slot+1) _ (by omega) (by omega) (by simpa only [Nat.add_assoc] using next) atNext]
    simp [Execution.charge,Nat.mul_succ,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

theorem wide_parent_segment_post (base : Word) (remaining count slot : Nat)
    (s : MachineState) (regs : ParentRegs s (remaining+count)) (pc : s.pc=wideParentPC base slot)
    {out : MachineState} (reached : out ∈ support (parentsTrace remaining count s)) :
    ParentRegs out remaining ∧ out.pc=wideParentPC base (slot+count) := by
  induction count generalizing slot s with
  | zero =>
    simp only [parentsTrace,support_pure,Set.mem_singleton_iff] at reached
    subst out
    exact ⟨regs,pc⟩
  | succ count ih =>
    simp only [parentsTrace,mem_support_bind_iff] at reached
    obtain ⟨answer,_,tail⟩ := reached
    have next := next_parent_regs s (remaining+count) answer (by simpa only [Nat.add_assoc] using regs)
    have atNext := (parent_pc s (remaining+(count+1)) answer).trans
      ((congrArg (·+12) pc).trans (wide_parent_pc_succ base slot))
    rw [show slot+(count+1)=slot+1+count by omega]
    exact ih (slot+1) _ (by simpa only [Nat.add_assoc] using next) atNext tail

end TwoPermutationPrototype.RV64
