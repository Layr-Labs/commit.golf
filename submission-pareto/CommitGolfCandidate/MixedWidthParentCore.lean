import CommitGolfCandidate.TwoPermutationParentLoop

/-! Generic full-width parent execution for mixed-width tree phases.
This generalizes the incumbent three-instruction parent to an explicitly supplied
image and fetch evidence. It does not establish any candidate image or certificate.
-/
namespace TwoPermutationPrototype.RV64.FullWidth
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] execute

theorem parent_call (image : Image) (s : MachineState) (n fuel : Nat) (bound : n < 2^24) (r : ParentRegs s n)
    (fetched : fetch image s=some (.base .ECALL)) :
    execute image (fuel+1) s true =
      (do let answer ← (liftM (World.query (.inr (.inl (parentInput s n)))) : OracleComp World (BitVec 256))
          let result ← execute image fuel (parentWritten s n answer) true
          return result.charge 8 1) := by
  have src := word_address_value (word := treeWord (2*n)) (by unfold treeWord;omega)
  have dst := word_address_value (word := treeWord n) (by unfold treeWord;omega)
  have inRange : 8*treeWord (2*n)+64 ≤ MEMORY_BYTES := by unfold treeWord MEMORY_BYTES;omega
  have outRange : 8*treeWord n+32 ≤ MEMORY_BYTES := by unfold treeWord MEMORY_BYTES;omega
  have q : oracleInput s=some (.inl (parentInput s n)) := by
    have kind : (s.getReg .x13).toNat=0 := by rw [r.primitive];rfl
    unfold oracleInput
    dsimp only
    rw [kind]
    simp [r.source,r.target,r.size,COMPRESSION_INPUT_LENGTH,COMPRESSION_OUTPUT_LENGTH,
      rangeValid,src,dst,inRange,outRange,parentInput]

  simp [execute,fetched,r.selector,q,writeOracleAnswer,r.target,parentWritten,oracleCycles,COMPRESSION_CYCLES]
  rfl

def ParentFetched (image : Image) (pc : Word) : Prop :=
  ∀ s : MachineState,
    (s.pc=pc → fetch image s=some (.base .ECALL)) ∧
    (s.pc=pc+4 → fetch image s=some (.base (.ADDI .x10 .x10 4032))) ∧
    (s.pc=pc+8 → fetch image s=some (.base (.ADDI .x12 .x12 4064)))

theorem parent_triple (image : Image) (s : MachineState) (n fuel : Nat) (pc : Word) (here : s.pc=pc) (bound : n<2^24)
    (r : ParentRegs s n) (fetched : ParentFetched image pc) :
    execute image (3+fuel) s true =
      (do let answer ← (liftM (World.query (.inr (.inl (parentInput s n)))) : OracleComp World (BitVec 256))
          let result ← execute image fuel (parentAfter s n answer) true
          return result.charge 10 1) := by
  rw [show 3+fuel=(fuel+2)+1 by omega,parent_call image s n _ bound r ((fetched s).1 here)]
  apply bind_congr_of_forall_mem_support
  intro answer _
  let a := parentWritten s n answer
  let b := execInstrBr a (.ADDI .x10 .x10 4032)
  have p1 : a.pc=pc+4 := by simp only [a,parentWritten,written_pc,here]
  have p2 : b.pc=pc+8 := by change a.pc+4=_; rw [p1,BitVec.add_assoc];rfl
  rw [CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ ((fetched a).2.1 p1) (show ordinaryStep a _=some b from rfl),
    CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ ((fetched b).2.2 p2) (show ordinaryStep b _=some (parentAfter s n answer) from rfl)]
  simp [instructionCycles,Execution.charge,←Nat.add_assoc]

attribute [local irreducible] parentAfter

def parentPC (base : Word) (slot : Nat) : Word := base + BitVec.ofNat 64 (12*slot)

private theorem parent_pc_next (base : Word) (slot : Nat) :
    parentPC base slot + 12 = parentPC base (slot+1) := by
  change base + BitVec.ofNat 64 (12*slot) + BitVec.ofNat 64 12 =
    base + BitVec.ofNat 64 (12*(slot+1))
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [show 12*slot+12 = 12*(slot+1) by omega]

theorem parents_segment (image : Image) (base : Word) (span : Nat)
    (fetches : ∀ i < span, ParentFetched image (parentPC base i))
    (rem count slot fuel : Nat) (s : MachineState)
    (bound : rem+count < 2^24) (inside : slot+count ≤ span)
    (r : ParentRegs s (rem+count)) (pc : s.pc=parentPC base slot) :
    execute image (3*count+fuel) s true =
      (do let mid ← parentsTrace rem count s
          let result ← execute image fuel mid true
          return result.charge (10*count) count) := by
  induction count generalizing slot s with
  | zero => simp [parentsTrace,Execution.charge]
  | succ k ih =>
    rw [show 3*(k+1)+fuel=3+(3*k+fuel) by omega,parent_triple image s _ _ _ pc bound r (fetches slot (by omega))]
    simp only [parentsTrace,bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro answer _
    have r' := next_parent_regs s (rem+k) answer (by simpa only [Nat.add_assoc] using r)
    have pc' := (parent_pc s (rem+(k+1)) answer).trans ((congrArg (·+12) pc).trans (parent_pc_next base slot))
    rw [ih (slot+1) _ (by omega) (by omega) (by simpa only [Nat.add_assoc] using r') pc']
    simp [Execution.charge,Nat.mul_succ,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

theorem parents_post (base : Word) (rem count slot : Nat) (s : MachineState)
    (r : ParentRegs s (rem+count)) (pc : s.pc=parentPC base slot)
    {out : MachineState} (hit : out ∈ support (parentsTrace rem count s)) :
    ParentRegs out rem ∧ out.pc=parentPC base (slot+count) := by
  induction count generalizing slot s with
  | zero =>
    simp only [parentsTrace,support_pure,Set.mem_singleton_iff] at hit
    subst out; exact ⟨r,pc⟩
  | succ k ih =>
    simp only [parentsTrace,mem_support_bind_iff] at hit
    obtain ⟨answer,_,reach⟩ := hit
    have r' := next_parent_regs s (rem+k) answer (by simpa only [Nat.add_assoc] using r)
    have pc' := (parent_pc s (rem+(k+1)) answer).trans ((congrArg (·+12) pc).trans (parent_pc_next base slot))
    rw [show slot+(k+1)=slot+1+k by omega]
    exact ih (slot+1) _ (by simpa only [Nat.add_assoc] using r') pc' reach

end TwoPermutationPrototype.RV64.FullWidth
