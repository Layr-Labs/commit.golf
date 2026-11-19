import CommitGolfCandidate.K3CUMask
import CommitGolfCandidate.GroupedQMeaning

/-!
# Heap bands below level 21

The heap loop for levels 20..1 runs in bands. A band is `groups` passes of `span` identical parents
followed by the latch `beq x12,x7,+8; jal x0,<band>`; `x7` holds the address of the node the band
stops at, `x6 = 0x3fff` is the 238-bit mask. Two parent kinds:
* `recordKind`: `ecall; sh x0,30(x12); addi x10,x10,-64; addi x12,x12,-32` (node keeps 240 bits);
* `t238Kind`: `ecall; lhu x31,28(x12); and x31,x31,x6; sw x31,28(x12); addi x10,x10,-64; addi x12,x12,-32`
  (node keeps 238 bits).
-/

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open CommitGolfCandidate (writeBits_register checkEvaluation check_evaluation_bind check_evaluation_pure)
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] execute

/-- Registers of a band at position `n` (the next parent computes node `n`), stopping at node `stop`. -/
structure BandRegs (s : MachineState) (n stop : Nat) extends ParentRegs s n : Prop where
  stopReg : s.getReg .x7=wordAddress (treeWord stop)
  maskReg : s.getReg .x6=16383

structure ParentKind where
  width : Nat
  cost : Nat
  keepNode : BitVec 256 → BitVec 256
  after : MachineState → Nat → BitVec 256 → MachineState
  WordsAt : Image → Word → Prop
  step : ∀ (image : Image) (s : MachineState) (n fuel : Nat) (pc : Word), s.pc=pc → n<2^24 →
    ParentRegs s n → s.getReg .x6=16383 → WordsAt image pc →
    execute image (width+fuel) s true =
      (do let answer ← (liftM (World.query (.inr (.inl (parentInput s n)))) : OracleComp World (BitVec 256))
          let result ← execute image fuel (after s n answer) true
          return result.charge cost 1)
  pcAfter : ∀ s n a, (after s n a).pc=s.pc+BitVec.ofNat 64 (4*width)
  next : ∀ s n a, ParentRegs s (n+1) → ParentRegs (after s (n+1) a) n
  keep : ∀ s n a (reg : Reg), reg≠.x10 → reg≠.x12 → reg≠.x31 → (after s n a).getReg reg=s.getReg reg
  memory : ∀ s n a, ParentRegs s n → s.getReg .x6=16383 → n<2^24 → (after s n a).mem=(parentWritten s n (keepNode a)).mem

theorem band_call_at (image : Image) (s : MachineState) (n fuel : Nat)
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

/-- The node-relative address `x12 + off` of a parent's node. -/
theorem node_address (t : MachineState) (n : Nat) (off : BitVec 12) (k : Nat) (hk : signExtend12 off=BitVec.ofNat 64 k)
    (target : t.getReg .x12=wordAddress (treeWord n)) :
    t.getReg .x12+signExtend12 off=BitVec.ofNat 64 (8*treeWord n+k) := by
  rw [target,hk]; change BitVec.ofNat 64 (8*treeWord n)+BitVec.ofNat 64 k=_; rw [←BitVec.ofNat_add]

theorem node_valid (n k width : Nat) (bound : n<2^24) (fits : k+width ≤ 32) (aligned : k%width=0)
    (w4 : width=2 ∨ width=4 ∨ width=8) :
    accessValid (BitVec.ofNat 64 (8*treeWord n+k)) width=true := by
  have limit : 8*treeWord n+32 ≤ MEMORY_BYTES := by unfold MEMORY_BYTES treeWord; omega
  have small : 8*treeWord n+k<2^64 := by unfold MEMORY_BYTES at limit; omega
  have nat : (BitVec.ofNat 64 (8*treeWord n+k)).toNat=8*treeWord n+k := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
  have base32 : (8*treeWord n)%32=0 := by unfold treeWord; omega
  simp only [accessValid,rangeValid,nat,Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · omega
  · rcases w4 with h|h|h <;> subst h <;> omega

/-! ### The 238-bit parent -/

theorem t238_x12 (s : MachineState) (n : Nat) (answer : BitVec 256) (regs : ParentRegs s n) :
    (parentWritten s n answer).getReg .x12=wordAddress (treeWord n) := by
  rw [parentWritten,writeBits_register,regs.target]

theorem t238_parent_step (image : Image) (s : MachineState) (n fuel : Nat) (pc : Word)
    (here : s.pc=pc) (bound : n<2^24) (regs : ParentRegs s n) (maskReg : s.getReg .x6=16383)
    (fetched : T238WordsAt image pc) :
    execute image (6+fuel) s true =
      (do let answer ← (liftM (World.query (.inr (.inl (parentInput s n)))) : OracleComp World (BitVec 256))
          let result ← execute image fuel (t238After s n answer) true
          return result.charge 13 1) := by
  rw [show 6+fuel=(fuel+5)+1 by omega,band_call_at image s n _ bound regs (fetched.call s here)]
  apply bind_congr_of_forall_mem_support
  intro answer _
  let t := parentWritten s n answer
  let u := execInstrBr t (.LHU .x31 .x12 28)
  let v := execInstrBr u (.AND .x31 .x31 .x6)
  let w := execInstrBr v (.SW .x12 .x31 28)
  let y := execInstrBr w (.ADDI .x10 .x10 4032)
  have tpc : t.pc=pc+4 := by simp only [t,parentWritten,written_pc,here]
  have upc : u.pc=pc+8 := by change t.pc+4=_; rw [tpc,BitVec.add_assoc]; rfl
  have vpc : v.pc=pc+12 := by change u.pc+4=_; rw [upc,BitVec.add_assoc]; rfl
  have wpc : w.pc=pc+16 := by change v.pc+4=_; rw [vpc,BitVec.add_assoc]; rfl
  have ypc : y.pc=pc+20 := by change w.pc+4=_; rw [wpc,BitVec.add_assoc]; rfl
  have tx12 := t238_x12 s n answer regs
  have vx12 : v.getReg .x12=wordAddress (treeWord n) := by
    change ((u.setReg .x31 _).setPC _).getReg .x12=_
    rw [MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ (by decide)]
    change ((t.setReg .x31 _).setPC _).getReg .x12=_
    rw [MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ (by decide)]
    exact tx12
  have loadAddr := node_address t n 28 28 rfl tx12
  have storeAddr := node_address v n 28 28 rfl vx12
  have loadValid := node_valid n 28 2 bound (by decide) (by decide) (by decide)
  have storeValid := node_valid n 28 4 bound (by decide) (by decide) (by decide)
  have load : ordinaryStep t (.base (.LHU .x31 .x12 28))=some u := by
    simp only [ordinaryStep,memoryArgumentsValid,memAccess,loadAddr,loadValid,↓reduceIte]
    rfl
  have store : ordinaryStep v (.base (.SW .x12 .x31 28))=some w := by
    simp only [ordinaryStep,memoryArgumentsValid,memAccess,storeAddr,storeValid,↓reduceIte]
    rfl
  rw [CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (fetched.load t tpc) load,
    CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (fetched.mask u upc) (show ordinaryStep u _=some v from rfl),
    CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (fetched.store v vpc) store,
    CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (fetched.source w wpc) (show ordinaryStep w _=some y from rfl),
    CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (fetched.target y ypc)
      (show ordinaryStep y _=some (t238After s n answer) from rfl)]
  simp [instructionCycles,Execution.charge,←Nat.add_assoc]

theorem lhu_reg (t : MachineState) (reg : Reg) (h : reg≠.x31) :
    (execInstrBr t (.LHU .x31 .x12 28)).getReg reg=t.getReg reg := by
  simp only [execInstrBr,MachineState.getReg_setPC]
  exact MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h)

theorem and_reg (t : MachineState) (reg : Reg) (h : reg≠.x31) :
    (execInstrBr t (.AND .x31 .x31 .x6)).getReg reg=t.getReg reg := by
  simp only [execInstrBr,MachineState.getReg_setPC]
  exact MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h)

theorem sw_reg (t : MachineState) (reg : Reg) :
    (execInstrBr t (.SW .x12 .x31 28)).getReg reg=t.getReg reg := by
  simp only [execInstrBr,MachineState.getReg_setPC]
  cases reg <;> rfl

private theorem addi_reg (t : MachineState) (rd rs : Reg) (imm : BitVec 12) (reg : Reg) (h : reg≠rd) :
    (execInstrBr t (.ADDI rd rs imm)).getReg reg=t.getReg reg := by
  simp only [execInstrBr,MachineState.getReg_setPC]
  exact MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h)

private theorem addi_dest (t : MachineState) (rd rs : Reg) (imm : BitVec 12) (h : rd≠.x0) :
    (execInstrBr t (.ADDI rd rs imm)).getReg rd=t.getReg rs+signExtend12 imm := by
  simp only [execInstrBr,MachineState.getReg_setPC]
  exact MachineState.getReg_setReg_eq h

theorem mask_keeps_register (s : MachineState) (n : Nat) (answer : BitVec 256) (reg : Reg) (h : reg≠.x31) :
    (t238Mask s n answer).getReg reg=s.getReg reg := by
  unfold t238Mask
  rw [sw_reg,and_reg _ _ h,lhu_reg _ _ h,parentWritten,writeBits_register]

theorem step_pc (t : MachineState) (i : Instr)
    (h : i=.LHU .x31 .x12 28 ∨ i=.AND .x31 .x31 .x6 ∨ i=.SW .x12 .x31 28 ∨ i=.ADDI .x10 .x10 4032 ∨
      i=.ADDI .x12 .x12 4064) :
    (execInstrBr t i).pc=t.pc+4 := by
  rcases h with rfl|rfl|rfl|rfl|rfl <;> rfl

theorem t238_keeps_register (s : MachineState) (n : Nat) (answer : BitVec 256) (reg : Reg)
    (k10 : reg≠.x10) (k12 : reg≠.x12) (k31 : reg≠.x31) :
    (t238After s n answer).getReg reg=s.getReg reg := by
  unfold t238After
  rw [addi_reg _ _ _ _ _ k12,addi_reg _ _ _ _ _ k10,mask_keeps_register _ _ _ _ k31]

theorem t238_pc (s : MachineState) (n : Nat) (answer : BitVec 256) :
    (t238After s n answer).pc=s.pc+BitVec.ofNat 64 24 := by
  unfold t238After t238Mask
  rw [step_pc _ _ (by simp),step_pc _ _ (by simp),step_pc _ _ (by simp),step_pc _ _ (by simp),
    step_pc _ _ (by simp),parentWritten,written_pc]
  simp only [BitVec.add_assoc]
  rfl

theorem t238_next_regs (s : MachineState) (n : Nat) (answer : BitVec 256)
    (regs : ParentRegs s (n+1)) : ParentRegs (t238After s (n+1) answer) n := by
  have hold (reg : Reg) (k10 : reg≠.x10) (k12 : reg≠.x12) (k31 : reg≠.x31) :=
    t238_keeps_register s (n+1) answer reg k10 k12 k31
  have m10 := mask_keeps_register s (n+1) answer .x10 (by decide)
  have m12 := mask_keeps_register s (n+1) answer .x12 (by decide)
  constructor
  · unfold t238After
    rw [addi_reg _ _ _ _ _ (by decide),addi_dest _ _ _ _ (by decide),m10,regs.source]
    have advance : treeWord (2*(n+1))=treeWord (2*n)+8 := by unfold treeWord;omega
    rw [advance,wordAddress_add,BitVec.add_assoc,show wordAddress 8+signExtend12 4032=0 by decide]
    exact BitVec.add_zero _
  · unfold t238After
    rw [addi_dest _ _ _ _ (by decide),addi_reg _ _ _ _ _ (by decide),m12,regs.target]
    have advance : treeWord (n+1)=treeWord n+4 := by unfold treeWord;omega
    rw [advance,wordAddress_add,BitVec.add_assoc,show wordAddress 4+signExtend12 4064=0 by decide]
    exact BitVec.add_zero _
  · exact (hold .x5 (by decide) (by decide) (by decide)).trans regs.selector
  · exact (hold .x11 (by decide) (by decide) (by decide)).trans regs.size
  · exact (hold .x13 (by decide) (by decide) (by decide)).trans regs.primitive
  · exact (hold .x9 (by decide) (by decide) (by decide)).trans regs.heap

theorem t238_after_mem (s : MachineState) (n : Nat) (answer : BitVec 256) :
    (t238After s n answer).mem=(t238Mask s n answer).mem := rfl

theorem t238_memory (s : MachineState) (n : Nat) (answer : BitVec 256) (regs : ParentRegs s n)
    (maskReg : s.getReg .x6=16383) (bound : n<2^24) :
    (t238After s n answer).mem=(parentWritten s n (pad238 answer)).mem :=
  t238_mask_memory s n answer regs.target maskReg bound

def t238Kind : ParentKind where
  width := 6
  cost := 13
  keepNode := pad238
  after := t238After
  WordsAt := T238WordsAt
  step image s n fuel pc here bound regs mask fetched := t238_parent_step image s n fuel pc here bound regs mask fetched
  pcAfter := t238_pc
  next := t238_next_regs
  keep := t238_keeps_register
  memory s n a regs mask bound := t238_memory s n a regs mask bound

/-! ### The record (240-bit) parent -/

theorem record_parent_step (image : Image) (s : MachineState) (n fuel : Nat) (pc : Word)
    (here : s.pc=pc) (bound : n<2^24) (regs : ParentRegs s n) (fetched : PackedParentWordsAt image pc) :
    execute image (4+fuel) s true =
      (do let answer ← (liftM (World.query (.inr (.inl (parentInput s n)))) : OracleComp World (BitVec 256))
          let result ← execute image fuel (packedParentAfter s n answer) true
          return result.charge 11 1) := by
  rw [show 4+fuel=(fuel+3)+1 by omega,band_call_at image s n _ bound regs (fetched.call s here)]
  apply bind_congr_of_forall_mem_support
  intro answer _
  let first := parentWritten s n answer
  let masked := packedParentMask s n answer
  let moved := execInstrBr masked (.ADDI .x10 .x10 4032)
  have firstPC : first.pc=pc+4 := by simp only [first,parentWritten,written_pc,here]
  have maskPC : masked.pc=pc+8 := by
    unfold masked packedParentMask
    change first.pc+4=_
    rw [firstPC,BitVec.add_assoc]
    rfl
  have movedPC : moved.pc=pc+12 := by
    change masked.pc+4=_
    rw [maskPC,BitVec.add_assoc]
    rfl
  have target : first.getReg .x12=wordAddress (treeWord n) := t238_x12 s n answer regs
  have address := node_address first n 30 30 rfl target
  have valid := node_valid n 30 2 bound (by decide) (by decide) (by decide)
  have clear : ordinaryStep first (.base (.SH .x12 .x0 30))=some masked := by
    simp only [ordinaryStep,memoryArgumentsValid,memAccess,address,valid,↓reduceIte]
    unfold masked packedParentMask
    rfl
  rw [CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (fetched.mask first firstPC) clear,
    CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (fetched.source masked maskPC)
      (show ordinaryStep masked _=some moved from rfl),
    CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (fetched.target moved movedPC)
      (show ordinaryStep moved _=some (packedParentAfter s n answer) from rfl)]
  simp [instructionCycles,Execution.charge,←Nat.add_assoc]

def recordKind : ParentKind where
  width := 4
  cost := 11
  keepNode := projectReply
  after := packedParentAfter
  WordsAt := PackedParentWordsAt
  step image s n fuel pc here bound regs _ fetched := record_parent_step image s n fuel pc here bound regs fetched
  pcAfter s n a := packed_parent_pc s n a
  next := packed_next_parent_regs
  keep s n a reg k10 k12 _ := packed_parent_keeps_register s n a reg (Ne.symm k10) (Ne.symm k12)
  memory s n a regs _ bound := packed_parent_memory s n a regs bound

/-! ### Bands of one parent kind -/

def kindPC (K : ParentKind) (base : Word) (slot : Nat) : Word := base+BitVec.ofNat 64 (4*K.width*slot)

theorem kind_pc_succ (K : ParentKind) (base : Word) (slot : Nat) :
    kindPC K base slot+BitVec.ofNat 64 (4*K.width)=kindPC K base (slot+1) := by
  unfold kindPC
  rw [BitVec.add_assoc,←BitVec.ofNat_add]
  congr 2

def kindTrace (K : ParentKind) (remaining : Nat) : Nat → MachineState → OracleComp World MachineState
  | 0, state => pure state
  | count+1, state => do
    let answer ← (liftM (World.query (.inr (.inl (parentInput state (remaining+(count+1)))))) : OracleComp World (BitVec 256))
    kindTrace K remaining count (K.after state (remaining+(count+1)) answer)

theorem kind_keep (K : ParentKind) (remaining count : Nat) (s : MachineState) (reg : Reg)
    (k10 : reg≠.x10) (k12 : reg≠.x12) (k31 : reg≠.x31)
    {out : MachineState} (reached : out ∈ support (kindTrace K remaining count s)) :
    out.getReg reg=s.getReg reg := by
  induction count generalizing s with
  | zero =>
    simp only [kindTrace,support_pure,Set.mem_singleton_iff] at reached
    subst out; rfl
  | succ count ih =>
    simp only [kindTrace,mem_support_bind_iff] at reached
    obtain ⟨answer,_,tail⟩ := reached
    exact (ih _ tail).trans (K.keep s _ answer reg k10 k12 k31)

theorem kind_segment (K : ParentKind) (image : Image) (base : Word) (span : Nat)
    (fetches : ∀ i < span, K.WordsAt image (kindPC K base i))
    (remaining count slot fuel : Nat) (s : MachineState)
    (bound : remaining+count<2^24) (inside : slot+count≤span)
    (regs : ParentRegs s (remaining+count)) (mask : s.getReg .x6=16383) (pc : s.pc=kindPC K base slot) :
    execute image (K.width*count+fuel) s true =
      (do let mid ← kindTrace K remaining count s
          let result ← execute image fuel mid true
          return result.charge (K.cost*count) count) := by
  induction count generalizing slot s with
  | zero => simp [kindTrace,Execution.charge]
  | succ count ih =>
    rw [show K.width*(count+1)+fuel=K.width+(K.width*count+fuel) by rw [Nat.mul_succ];omega,
      K.step image s _ _ _ pc bound regs mask (fetches slot (by omega))]
    simp only [kindTrace,bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro answer _
    have next := K.next s (remaining+count) answer (by simpa only [Nat.add_assoc] using regs)
    have atNext := (K.pcAfter s (remaining+(count+1)) answer).trans
      ((congrArg (·+BitVec.ofNat 64 (4*K.width)) pc).trans (kind_pc_succ K base slot))
    have keepMask := (K.keep s (remaining+(count+1)) answer .x6 (by decide) (by decide) (by decide)).trans mask
    rw [ih (slot+1) _ (by omega) (by omega) (by simpa only [Nat.add_assoc] using next) keepMask atNext]
    simp [Execution.charge,Nat.mul_succ,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

theorem kind_segment_post (K : ParentKind) (base : Word) (remaining count slot : Nat)
    (s : MachineState) (regs : ParentRegs s (remaining+count)) (pc : s.pc=kindPC K base slot)
    {out : MachineState} (reached : out ∈ support (kindTrace K remaining count s)) :
    ParentRegs out remaining ∧ out.pc=kindPC K base (slot+count) := by
  induction count generalizing slot s with
  | zero =>
    simp only [kindTrace,support_pure,Set.mem_singleton_iff] at reached
    subst out
    exact ⟨regs,pc⟩
  | succ count ih =>
    simp only [kindTrace,mem_support_bind_iff] at reached
    obtain ⟨answer,_,tail⟩ := reached
    have next := K.next s (remaining+count) answer (by simpa only [Nat.add_assoc] using regs)
    have atNext := (K.pcAfter s (remaining+(count+1)) answer).trans
      ((congrArg (·+BitVec.ofNat 64 (4*K.width)) pc).trans (kind_pc_succ K base slot))
    rw [show slot+(count+1)=slot+1+count by omega]
    exact ih (slot+1) _ (by simpa only [Nat.add_assoc] using next) atNext tail

structure BandControl (image : Image) (K : ParentKind) (base : Word) (span : Nat) where
  backOffset : BitVec 21
  backTarget : kindPC K base span+4+signExtend21 backOffset=base
  branch : ∀ state : MachineState, state.pc=kindPC K base span →
    fetch image state=some (.base (.BEQ .x12 .x7 8))
  jump : ∀ state : MachineState, state.pc=kindPC K base span+4 →
    fetch image state=some (.base (.JAL .x0 backOffset))

def bandNextPC (K : ParentKind) (base : Word) (span remaining : Nat) : Word :=
  if remaining=0 then kindPC K base span+8 else base

theorem band_latch (K : ParentKind) (image : Image) (base : Word) (span : Nat)
    (control : BandControl image K base span) (stop r fuel : Nat) (state : MachineState)
    (bound : stop+r<2^24) (regs : BandRegs state (stop+r) stop) (pc : state.pc=kindPC K base span) :
    execute image (longParentLatchCost r+fuel) state true =
      (do let result ← execute image fuel (state.setPC (bandNextPC K base span r)) true
          return result.charge (longParentLatchCost r) 0) := by
  have equal : state.getReg .x12=state.getReg .x7 ↔ r=0 := by
    rw [regs.target,regs.stopReg]
    constructor
    · intro same
      have index := wordAddress_injective_of_bound (a := treeWord (stop+r)) (b := treeWord stop)
        (by unfold treeWord; omega) (by unfold treeWord; omega) same
      unfold treeWord at index
      omega
    · intro zero; rw [zero,Nat.add_zero]
  by_cases last : r=0
  · have hit : state.getReg .x12=state.getReg .x7 := equal.mpr last
    have branch : ordinaryStep state (.base (.BEQ .x12 .x7 8)) =
        some (state.setPC (kindPC K base span+8)) := by
      simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,hit,signExtend13]
    rw [longParentLatchCost,if_pos last,bandNextPC,if_pos last,Nat.add_comm 1 fuel,
      CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (control.branch state pc) branch]
    rfl
  · let branchState := state.setPC (kindPC K base span+4)
    have different : state.getReg .x12≠state.getReg .x7 := fun same => last (equal.mp same)
    have branch : ordinaryStep state (.base (.BEQ .x12 .x7 8))=some branchState := by
      simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,different,branchState]
    have jump : ordinaryStep branchState (.base (.JAL .x0 control.backOffset)) =
        some (state.setPC base) := by
      simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,branchState,
        MachineState.setReg,MachineState.setPC]
      exact control.backTarget
    have branchPC : branchState.pc=kindPC K base span+4 := rfl
    rw [longParentLatchCost,if_neg last,bandNextPC,if_neg last,
      show 2+fuel=(fuel+1)+1 by omega,
      CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (control.branch state pc) branch,
      CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (control.jump branchState branchPC) jump]
    simp [instructionCycles,Execution.charge,←Nat.add_assoc]

def bandGroups (K : ParentKind) (base : Word) (span stop : Nat) :
    Nat → MachineState → OracleComp World MachineState
  | 0, state => pure state
  | groups+1, state => do
    let body ← kindTrace K (stop+span*groups) span state
    bandGroups K base span stop groups (body.setPC (bandNextPC K base span (span*groups)))

theorem band_execution (K : ParentKind) (image : Image) (base : Word) (span : Nat)
    (fetches : ∀ i < span, K.WordsAt image (kindPC K base i))
    (control : BandControl image K base span) (positive : 0<span)
    (stop groups fuel : Nat) (state : MachineState) (bound : stop+span*groups<2^24)
    (regs : BandRegs state (stop+span*groups) stop) (pc : 0<groups → state.pc=base) :
    execute image (loopCount K.width span groups+fuel) state true =
      (do let out ← bandGroups K base span stop groups state
          let result ← execute image fuel out true
          return result.charge (loopCount K.cost span groups) (span*groups)) := by
  induction groups generalizing state with
  | zero => simp [bandGroups,loopCount,Execution.charge]
  | succ groups ih =>
    have enter : state.pc=kindPC K base 0 := by
      rw [pc (by omega)]
      simp [kindPC]
    have ready : ParentRegs state ((stop+span*groups)+span) := by
      simpa only [Nat.mul_succ,Nat.add_assoc] using regs.toParentRegs
    rw [loop_count_step K.width span groups positive,
      show K.width*span+longParentLatchCost (span*groups)+loopCount K.width span groups+fuel =
        K.width*span+(longParentLatchCost (span*groups)+(loopCount K.width span groups+fuel)) by omega,
      kind_segment K image base span fetches (stop+span*groups) span 0 _ state (by rw [Nat.mul_succ] at bound; omega)
        (by omega) ready regs.maskReg enter]
    simp only [bandGroups,bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro body reached
    have after := kind_segment_post K base (stop+span*groups) span 0 state ready enter reached
    have ending : body.pc=kindPC K base span := by simpa only [Nat.zero_add] using after.2
    have k7 := kind_keep K _ _ _ .x7 (by decide) (by decide) (by decide) reached
    have k6 := kind_keep K _ _ _ .x6 (by decide) (by decide) (by decide) reached
    have bregs : BandRegs body (stop+span*groups) stop := ⟨after.1,k7.trans regs.stopReg,k6.trans regs.maskReg⟩
    rw [band_latch K image base span control stop (span*groups) _ body (by rw [Nat.mul_succ] at bound; omega) bregs ending]
    let next := body.setPC (bandNextPC K base span (span*groups))
    have continued : BandRegs next (stop+span*groups) stop :=
      ⟨⟨bregs.source,bregs.target,bregs.selector,bregs.size,bregs.primitive,bregs.heap⟩,bregs.stopReg,bregs.maskReg⟩
    have again (notLast : 0<groups) : next.pc=base := by
      have notZero : span*groups≠0 := Nat.ne_of_gt (Nat.mul_pos positive notLast)
      simp only [next,MachineState.setPC,bandNextPC,notZero,ite_false]
    rw [show body.setPC (bandNextPC K base span (span*groups))=next from rfl,
      ih next (by rw [Nat.mul_succ] at bound; omega) continued again,loop_count_step K.cost span groups positive]
    simp [Execution.charge,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm,Nat.mul_succ]

theorem band_post (K : ParentKind) (base : Word) (span stop groups : Nat) (state : MachineState)
    (positive : 0<span) (entry : 0<groups → state.pc=base) (regs : BandRegs state (stop+span*groups) stop)
    {out : MachineState} (reached : out ∈ support (bandGroups K base span stop groups state)) :
    BandRegs out stop stop ∧ (0<groups → out.pc=kindPC K base span+8) := by
  induction groups generalizing state with
  | zero =>
    simp only [bandGroups,support_pure,Set.mem_singleton_iff] at reached
    subst out
    exact ⟨by simpa only [Nat.mul_zero,Nat.add_zero] using regs,by omega⟩
  | succ groups ih =>
    simp only [bandGroups,mem_support_bind_iff] at reached
    obtain ⟨body,path,tail⟩ := reached
    have start : state.pc=kindPC K base 0 := by
      rw [entry (by omega)]
      simp [kindPC]
    have ready : ParentRegs state ((stop+span*groups)+span) := by
      simpa only [Nat.mul_succ,Nat.add_assoc] using regs.toParentRegs
    have after := kind_segment_post K base (stop+span*groups) span 0 state ready start path
    have k7 := kind_keep K _ _ _ .x7 (by decide) (by decide) (by decide) path
    have k6 := kind_keep K _ _ _ .x6 (by decide) (by decide) (by decide) path
    let next := body.setPC (bandNextPC K base span (span*groups))
    have stillReady : BandRegs next (stop+span*groups) stop :=
      ⟨⟨after.1.source,after.1.target,after.1.selector,after.1.size,after.1.primitive,after.1.heap⟩,
        k7.trans regs.stopReg,k6.trans regs.maskReg⟩
    have again (notLast : 0<groups) : next.pc=base := by
      have notZero : span*groups≠0 := Nat.ne_of_gt (Nat.mul_pos positive notLast)
      simp only [next,MachineState.setPC,bandNextPC,notZero,ite_false]
    have rest := ih next again stillReady tail
    refine ⟨rest.1,fun _ => ?_⟩
    by_cases last : groups=0
    · subst groups
      simp only [bandGroups,support_pure,Set.mem_singleton_iff] at tail
      rw [tail]
      simp [bandNextPC,MachineState.setPC]
    · exact rest.2 (Nat.pos_of_ne_zero last)

theorem band_keep (K : ParentKind) (base : Word) (span stop groups : Nat) (state : MachineState) (reg : Reg)
    (k10 : reg≠.x10) (k12 : reg≠.x12) (k31 : reg≠.x31)
    {out : MachineState} (reached : out ∈ support (bandGroups K base span stop groups state)) :
    out.getReg reg=state.getReg reg := by
  induction groups generalizing state with
  | zero =>
    simp only [bandGroups,support_pure,Set.mem_singleton_iff] at reached
    subst out; rfl
  | succ groups ih =>
    simp only [bandGroups,mem_support_bind_iff] at reached
    obtain ⟨body,path,tail⟩ := reached
    have rest := ih _ tail
    rw [MachineState.getReg_setPC] at rest
    exact rest.trans (kind_keep K _ _ _ reg k10 k12 k31 path)

theorem counted_kind_trace (K : ParentKind) (oracle : Oracle) (state : MachineState) (remaining count : Nat) :
    RunPublic oracle (kindTrace K remaining count state) count := by
  induction count generalizing state with
  | zero => exact run_pure_public oracle state
  | succ count ih =>
    rw [kindTrace]
    simpa only [Nat.add_comm 1 count] using
      (run_bind_public oracle (liftM (World.query (.inr (.inl (parentInput state (remaining+(count+1)))))) :
        OracleComp World (BitVec 256))
        (fun answer => kindTrace K remaining count (K.after state (remaining+(count+1)) answer))
        1 count (run_query_public ..) (fun _ => ih _))

theorem counted_band (K : ParentKind) (oracle : Oracle) (base : Word) (span stop groups : Nat)
    (state : MachineState) :
    RunPublic oracle (bandGroups K base span stop groups state) (span*groups) := by
  induction groups generalizing state with
  | zero => exact run_pure_public oracle state
  | succ groups ih =>
    rw [bandGroups, show span*(groups+1)=span+span*groups by rw [Nat.mul_succ,Nat.add_comm]]
    exact run_bind_public oracle _ _ span (span*groups) (counted_kind_trace ..) (fun out => ih _)

/-! ### What a band computes -/

theorem kind_content_step (K : ParentKind) (oracle : Oracle) (s : MachineState) (heap : Nat → BitVec 256)
    (before : Memory) (n : Nat) (inside : n+1<4194304)
    (tree : heap (n+1)=K.keepNode (oracle.compression (heap (2*(n+1)+1) ++ heap (2*(n+1)))))
    (prior : TailContent s heap before (n+1)) (regs : ParentRegs s (n+1)) (mask : s.getReg .x6=16383)
    (wide : 2*(n+1)+1<4194304) :
    TailContent (K.after s (n+1) (oracle.compression (parentInput s (n+1)))) heap before n := by
  have memory := K.memory s (n+1) (oracle.compression (parentInput s (n+1))) regs mask (by omega)
  have step := node_write_frame s _ heap before (n+1) _ (by omega) memory prior (by
    rw [child_pair,prior.nodes (2*(n+1)+1) (by omega) wide,prior.nodes (2*(n+1)) (by omega) (by omega),tree])
  simpa only [Nat.add_sub_cancel] using step

theorem kind_sequence_semantics (K : ParentKind) (oracle : Oracle) (state : MachineState) (heap : Nat → BitVec 256)
    (before : Memory) (remaining count : Nat) (inside : 2*(remaining+count)+1<4194304)
    (tree : ∀ node, remaining<node → node≤remaining+count →
      heap node=K.keepNode (oracle.compression (heap (2*node+1) ++ heap (2*node))))
    (prior : TailContent state heap before (remaining+count))
    (regs : ParentRegs state (remaining+count)) (mask : state.getReg .x6=16383) :
    let result := (checkEvaluation oracle (kindTrace K remaining count state)).1
    TailContent result heap before remaining ∧ ParentRegs result remaining ∧ result.getReg .x6=16383 := by
  induction count generalizing state with
  | zero =>
    simpa only [kindTrace,check_evaluation_pure,Nat.add_zero] using And.intro prior (And.intro regs mask)
  | succ count ih =>
    rw [kindTrace,check_evaluation_bind]
    have evaluated : checkEvaluation oracle (liftM
        (World.query (.inr (.inl (parentInput state (remaining+(count+1)))))) : OracleComp World (BitVec 256)) =
          (oracle.compression (parentInput state (remaining+(count+1))),1) :=
      CommitGolfCandidate.check_evaluation_public oracle _
    rw [evaluated]
    apply ih _ (by omega) (fun node lo hi => tree node lo (by omega))
    · exact kind_content_step K oracle state heap before (remaining+count) (by omega)
        (tree _ (by omega) (by omega)) prior regs mask (by omega)
    · exact K.next state (remaining+count) _ regs
    · exact (K.keep state _ _ .x6 (by decide) (by decide) (by decide)).trans mask

theorem band_semantics (K : ParentKind) (oracle : Oracle) (base : Word) (span stop groups : Nat)
    (state : MachineState) (heap : Nat → BitVec 256) (before : Memory)
    (inside : 2*(stop+span*groups)+1<4194304)
    (tree : ∀ node, stop<node → node≤stop+span*groups →
      heap node=K.keepNode (oracle.compression (heap (2*node+1) ++ heap (2*node))))
    (prior : TailContent state heap before (stop+span*groups)) (regs : ParentRegs state (stop+span*groups))
    (mask : state.getReg .x6=16383) :
    TailContent (checkEvaluation oracle (bandGroups K base span stop groups state)).1 heap before stop := by
  induction groups generalizing state with
  | zero => simpa only [bandGroups,check_evaluation_pure,Nat.mul_zero,Nat.add_zero] using prior
  | succ groups ih =>
    rw [Nat.mul_succ,←Nat.add_assoc] at inside prior regs
    have body := kind_sequence_semantics K oracle state heap before (stop+span*groups) span inside
      (fun node lo hi => tree node (by omega) (by rw [Nat.mul_succ]; omega)) prior regs mask
    rw [bandGroups,check_evaluation_bind]
    apply ih _ (by omega) (fun node lo hi => tree node lo (by rw [Nat.mul_succ]; omega))
    · exact tail_content_setpc _ _ _ _ _ body.1
    · exact ⟨body.2.1.source,body.2.1.target,body.2.1.selector,body.2.1.size,body.2.1.primitive,body.2.1.heap⟩
    · exact body.2.2

end TwoPermutationPrototype.Grouped
