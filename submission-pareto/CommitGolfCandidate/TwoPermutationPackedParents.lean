import CommitGolfCandidate.TwoPermutationParentLoop
import CommitGolfCandidate.ProjectedMask

namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] execute

/-- One unrolled parent: the compression call, a masked rewrite of the
reply's top word (keeping 238 digest bits), and both pointer decrements. -/
structure PackedParentWordsAt (image : Image) (pc : Word) : Prop where
  call : ∀ s : MachineState, s.pc=pc → fetch image s=some (.base .ECALL)
  load : ∀ s : MachineState, s.pc=pc+4 → fetch image s=some (.base (.LD .x31 .x12 24))
  mask : ∀ s : MachineState, s.pc=pc+8 → fetch image s=some (.base (.AND .x31 .x31 .x30))
  store : ∀ s : MachineState, s.pc=pc+12 → fetch image s=some (.base (.SD .x12 .x31 24))
  source : ∀ s : MachineState, s.pc=pc+16 →
    fetch image s=some (.base (.ADDI .x10 .x10 4032))
  target : ∀ s : MachineState, s.pc=pc+20 →
    fetch image s=some (.base (.ADDI .x12 .x12 4064))

def packedParentMask (s : MachineState) (n : Nat) (answer : BitVec 256) :=
  execInstrBr (execInstrBr (execInstrBr (parentWritten s n answer) (.LD .x31 .x12 24))
    (.AND .x31 .x31 .x30)) (.SD .x12 .x31 24)

def packedParentAfter (s : MachineState) (n : Nat) (answer : BitVec 256) :=
  execInstrBr (execInstrBr (packedParentMask s n answer) (.ADDI .x10 .x10 4032)) (.ADDI .x12 .x12 4064)

def packedParentsTrace (remaining : Nat) : Nat → MachineState → OracleComp World MachineState
  | 0, state => pure state
  | count+1, state => do
    let answer ← (liftM (World.query (.inr (.inl (parentInput state (remaining+(count+1)))))) : OracleComp World (BitVec 256))
    packedParentsTrace remaining count (packedParentAfter state (remaining+(count+1)) answer)

theorem packed_parent_pc (state : MachineState) (n : Nat) (answer : BitVec 256) :
    (packedParentAfter state n answer).pc=state.pc+24 := by
  change (parentWritten state n answer).pc+4+4+4+4+4=state.pc+24
  rw [parentWritten,written_pc,BitVec.add_assoc,BitVec.add_assoc,BitVec.add_assoc,BitVec.add_assoc,
    BitVec.add_assoc]
  rfl

private theorem register_after_store (s : MachineState) (a v : Word) (r : Reg) :
    (s.setMem a v).getReg r=s.getReg r := rfl

private theorem mask_register (state : MachineState) (n : Nat) (answer : BitVec 256) (reg : Reg)
    (kept : .x31≠reg) :
    (packedParentMask state n answer).getReg reg=(parentWritten state n answer).getReg reg := by
  simp only [packedParentMask,execInstrBr,MachineState.getReg_setPC,register_after_store,
    MachineState.getReg_setReg_ne _ _ _ _ kept]

private theorem packed_after_source (state : MachineState) (n : Nat) (answer : BitVec 256) :
    (packedParentAfter state n answer).getReg .x10=(parentWritten state n answer).getReg .x10+signExtend12 4032 := by
  simp only [packedParentAfter,execInstrBr,MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (show Reg.x12≠Reg.x10 by decide),MachineState.getReg_setReg_eq (show Reg.x10≠Reg.x0 by decide)]
  rw [mask_register _ _ _ _ (by decide)]

private theorem packed_after_target (state : MachineState) (n : Nat) (answer : BitVec 256) :
    (packedParentAfter state n answer).getReg .x12=(parentWritten state n answer).getReg .x12+signExtend12 4064 := by
  simp only [packedParentAfter,execInstrBr,MachineState.getReg_setPC,MachineState.getReg_setReg_eq (show Reg.x12≠Reg.x0 by decide),
    MachineState.getReg_setReg_ne _ _ _ _ (show Reg.x10≠Reg.x12 by decide)]
  rw [mask_register _ _ _ _ (by decide)]

private theorem parent_after_source (state : MachineState) (n : Nat) (answer : BitVec 256) :
    (parentAfter state n answer).getReg .x10=(parentWritten state n answer).getReg .x10+signExtend12 4032 := by
  simp only [parentAfter,execInstrBr,MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (show Reg.x12≠Reg.x10 by decide),MachineState.getReg_setReg_eq (show Reg.x10≠Reg.x0 by decide)]

private theorem parent_after_target (state : MachineState) (n : Nat) (answer : BitVec 256) :
    (parentAfter state n answer).getReg .x12=(parentWritten state n answer).getReg .x12+signExtend12 4064 := by
  simp only [parentAfter,execInstrBr,MachineState.getReg_setPC,MachineState.getReg_setReg_eq (show Reg.x12≠Reg.x0 by decide),
    MachineState.getReg_setReg_ne _ _ _ _ (show Reg.x10≠Reg.x12 by decide)]

attribute [local irreducible] parentWritten packedParentMask

theorem packed_parent_keeps_register (state : MachineState) (n : Nat) (answer : BitVec 256) (reg : Reg)
    (keptSource : .x10≠reg) (keptTarget : .x12≠reg) (keptScratch : .x31≠reg) :
    (packedParentAfter state n answer).getReg reg=state.getReg reg := by
  simp only [packedParentAfter,execInstrBr,MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ keptSource,MachineState.getReg_setReg_ne _ _ _ _ keptTarget]
  rw [mask_register _ _ _ _ keptScratch,parentWritten,CommitGolfCandidate.writeBits_register]

theorem packed_parent_keeps_mask (state : MachineState) (n : Nat) (answer : BitVec 256) :
    (packedParentAfter state n answer).getReg .x30=state.getReg .x30 :=
  packed_parent_keeps_register state n answer .x30 (by decide) (by decide) (by decide)

theorem packed_next_parent_regs (state : MachineState) (n : Nat) (answer : BitVec 256)
    (regs : ParentRegs state (n+1)) : ParentRegs (packedParentAfter state (n+1) answer) n := by
  have next := next_parent_regs state n answer regs
  constructor
  · rw [packed_after_source,← parent_after_source]
    exact next.source
  · rw [packed_after_target,← parent_after_target]
    exact next.target
  · exact (packed_parent_keeps_register state _ answer .x5 (by decide) (by decide) (by decide)).trans regs.selector
  · exact (packed_parent_keeps_register state _ answer .x11 (by decide) (by decide) (by decide)).trans regs.size
  · exact (packed_parent_keeps_register state _ answer .x13 (by decide) (by decide) (by decide)).trans regs.primitive
  · exact (packed_parent_keeps_register state _ answer .x9 (by decide) (by decide) (by decide)).trans regs.heap

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

private theorem packed_parent_step (image : Image) (s : MachineState) (n fuel : Nat) (pc : Word)
    (here : s.pc=pc) (bound : n<2^24) (regs : ParentRegs s n)
    (fetched : PackedParentWordsAt image pc) :
    execute image (6+fuel) s true =
      (do let answer ← (liftM (World.query (.inr (.inl (parentInput s n)))) : OracleComp World (BitVec 256))
          let result ← execute image fuel (packedParentAfter s n answer) true
          return result.charge 13 1) := by
  rw [show 6+fuel=(fuel+5)+1 by omega,parent_call_at image s n _ bound regs (fetched.call s here)]
  apply bind_congr_of_forall_mem_support
  intro answer _
  let first := parentWritten s n answer
  let loaded := execInstrBr first (.LD .x31 .x12 24)
  let anded := execInstrBr loaded (.AND .x31 .x31 .x30)
  let masked := packedParentMask s n answer
  let moved := execInstrBr masked (.ADDI .x10 .x10 4032)
  have firstPC : first.pc=pc+4 := by simp only [first,parentWritten,written_pc,here]
  have loadedPC : loaded.pc=pc+8 := by
    change first.pc+4=_
    rw [firstPC,BitVec.add_assoc]
    rfl
  have andedPC : anded.pc=pc+12 := by
    change loaded.pc+4=_
    rw [loadedPC,BitVec.add_assoc]
    rfl
  have maskPC : masked.pc=pc+16 := by
    unfold masked packedParentMask
    change anded.pc+4=_
    rw [andedPC,BitVec.add_assoc]
    rfl
  have movedPC : moved.pc=pc+20 := by
    change masked.pc+4=_
    rw [maskPC,BitVec.add_assoc]
    rfl
  have target : first.getReg .x12=wordAddress (treeWord n) := by
    unfold first parentWritten
    rw [CommitGolfCandidate.writeBits_register,regs.target]
  have address : first.getReg .x12 + signExtend12 24 = BitVec.ofNat 64 (8*treeWord n+24) := by
    rw [target]
    change BitVec.ofNat 64 (8*treeWord n)+BitVec.ofNat 64 24=_
    rw [←BitVec.ofNat_add]
  have address' : anded.getReg .x12 + signExtend12 24 = BitVec.ofNat 64 (8*treeWord n+24) := by
    have same : anded.getReg .x12=first.getReg .x12 := by
      simp only [anded,loaded,execInstrBr,MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ (show Reg.x31≠Reg.x12 by decide)]
    rw [same,address]
  have limit : 8*treeWord n+32 ≤ MEMORY_BYTES := by unfold MEMORY_BYTES treeWord; omega
  have address64 : 8*treeWord n+24<2^64 := by unfold MEMORY_BYTES at limit; omega
  have valid : accessValid (BitVec.ofNat 64 (8*treeWord n+24)) 8=true := by
    have nat : (BitVec.ofNat 64 (8*treeWord n+24)).toNat=8*treeWord n+24 := by
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt address64]
    simp only [accessValid,rangeValid,nat,Bool.and_eq_true,decide_eq_true_eq]
    constructor <;> omega
  have load : ordinaryStep first (.base (.LD .x31 .x12 24))=some loaded := by
    simp only [ordinaryStep,memoryArgumentsValid,memAccess,address,valid,↓reduceIte]
    rfl
  have store : ordinaryStep anded (.base (.SD .x12 .x31 24))=some masked := by
    simp only [ordinaryStep,memoryArgumentsValid,memAccess,address',valid,↓reduceIte]
    unfold masked packedParentMask
    rfl
  rw [CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (fetched.load first firstPC) load,
    CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (fetched.mask loaded loadedPC)
      (show ordinaryStep loaded _=some anded from rfl),
    CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (fetched.store anded andedPC) store,
    CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (fetched.source masked maskPC)
      (show ordinaryStep masked _=some moved from rfl),
    CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (fetched.target moved movedPC)
      (show ordinaryStep moved _=some (packedParentAfter s n answer) from rfl)]
  simp [instructionCycles,Execution.charge,←Nat.add_assoc]

def packedParentPC (base : Word) (slot : Nat) : Word := base+BitVec.ofNat 64 (24*slot)

private theorem packed_parent_pc_succ (base : Word) (slot : Nat) :
    packedParentPC base slot+24=packedParentPC base (slot+1) := by
  change base+BitVec.ofNat 64 (24*slot)+BitVec.ofNat 64 24 =
    base+BitVec.ofNat 64 (24*(slot+1))
  rw [BitVec.add_assoc,←BitVec.ofNat_add]
  rw [show 24*slot+24=24*(slot+1) by omega]

theorem packed_parent_segment (image : Image) (base : Word) (span : Nat)
    (fetches : ∀ i < span, PackedParentWordsAt image (packedParentPC base i))
    (remaining count slot fuel : Nat) (s : MachineState)
    (bound : remaining+count<2^24) (inside : slot+count ≤ span)
    (regs : ParentRegs s (remaining+count)) (pc : s.pc=packedParentPC base slot) :
    execute image (6*count+fuel) s true =
      (do let mid ← packedParentsTrace remaining count s
          let result ← execute image fuel mid true
          return result.charge (13*count) count) := by
  induction count generalizing slot s with
  | zero => simp [packedParentsTrace,Execution.charge]
  | succ count ih =>
    rw [show 6*(count+1)+fuel=6+(6*count+fuel) by omega,
      packed_parent_step image s _ _ _ pc bound regs (fetches slot (by omega))]
    simp only [packedParentsTrace,bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro answer _
    have next := packed_next_parent_regs s (remaining+count) answer (by simpa only [Nat.add_assoc] using regs)
    have atNext := (packed_parent_pc s (remaining+(count+1)) answer).trans
      ((congrArg (·+24) pc).trans (packed_parent_pc_succ base slot))
    rw [ih (slot+1) _ (by omega) (by omega) (by simpa only [Nat.add_assoc] using next) atNext]
    simp [Execution.charge,Nat.mul_succ,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

theorem packed_parent_segment_post (base : Word) (remaining count slot : Nat)
    (s : MachineState) (regs : ParentRegs s (remaining+count)) (pc : s.pc=packedParentPC base slot)
    {out : MachineState} (reached : out ∈ support (packedParentsTrace remaining count s)) :
    ParentRegs out remaining ∧ out.pc=packedParentPC base (slot+count) := by
  induction count generalizing slot s with
  | zero =>
    simp only [packedParentsTrace,support_pure,Set.mem_singleton_iff] at reached
    subst out
    exact ⟨regs,pc⟩
  | succ count ih =>
    simp only [packedParentsTrace,mem_support_bind_iff] at reached
    obtain ⟨answer,_,tail⟩ := reached
    have next := packed_next_parent_regs s (remaining+count) answer (by simpa only [Nat.add_assoc] using regs)
    have atNext := (packed_parent_pc s (remaining+(count+1)) answer).trans
      ((congrArg (·+24) pc).trans (packed_parent_pc_succ base slot))
    rw [show slot+(count+1)=slot+1+count by omega]
    exact ih (slot+1) _ (by simpa only [Nat.add_assoc] using next) atNext tail

end TwoPermutationPrototype.RV64
