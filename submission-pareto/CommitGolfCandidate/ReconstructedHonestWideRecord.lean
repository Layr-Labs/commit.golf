import CommitGolfCandidate.ReconstructedHonestNameKernel
import CommitGolfCandidate.ReconstructedHonestNested

namespace CommitGolfCandidate.Reconstruction.HonestWideRecord
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp HonestProtected HonestNames HonestNameKernel
open HonestWideMemory (context start finish)
open HonestWideKernel (image)
open CommitBlocks (addr)

set_option maxRecDepth 32768
set_option maxHeartbeats 2500000
attribute [local irreducible] ArtifactEncoding.decode

def Numeric := ∀ i, i∈HonestWideShapes.points → HonestWideKernel.checked i=true
def Symbolic := ∀ i, i∈HonestWideShapes.points → HonestNameKernel.checked i=true

private theorem member (k : Nat) (a : Shape) (p : HonestWideShapes.current k=some a) : k∈HonestWideShapes.points := by
  unfold HonestWideShapes.current at p
  split at p <;> first | decide +kernel | cases p

private theorem read_at (i : Fin 1660) : HonestBlocks.readOp Artifact.openingCode (addr i.val) =
    decodeInstruction (Artifact.openingCode.get 32 i) := by
  have bound := i.isLt
  have exactIdx : HonestBinaryRank.index (addr i.val) = i.val := by
    unfold HonestBinaryRank.index addr
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    omega
  unfold HonestBlocks.readOp
  simp only [exactIdx,beq_self_eq_true,ite_true,dite_eq_left bound]

private theorem at_guard {coins : Bool} {s t : MachineState} (whereAt : s.pc=addr 141)
    (walk : HonestWideKernel.Path coins s t) : t.pc=if s.getReg .x12=0#64 then addr 142 else addr 143 := by
  have op : HonestBlocks.readOp Artifact.openingCode (addr 141)=some (.base (.BNE .x12 .x0 8)) := by
    rw [read_at (i:=⟨141,by decide⟩)]
    rw [show Artifact.openingCode.get 32 ⟨141,by decide⟩=0x61463 by decide +kernel]; rfl
  have read := HonestBlocks.fetch_op Artifact.openingCode image (Eq.refl (ArtifactEncoding.decode 32 _)) (by decide)
    s (.base (.BNE .x12 .x0 8)) (whereAt ▸ op)
  have target (out : Execution) (run : out∈support (execute image 1 s coins)) (alive : out.exit=.unfinished) :
      out.state.pc=if s.getReg .x12=0#64 then addr 142 else addr 143 := by
    have step := HonestAbstract.continued_step _ s _ coins read (by simp) out run alive
    simp only [ordinaryStep,memoryArgumentsValid,memAccess,ite_true,Option.some.injEq] at step
    rw [←step]
    simp only [execInstrBr,show s.getReg .x0=0 from rfl,bne_iff_ne]
    by_cases zero : s.getReg .x12=0#64
    · simp [zero,MachineState.setPC,whereAt,addr]
    · simp [zero,MachineState.setPC,whereAt,addr,signExtend13]
  cases walk with
  | hit run alive _ => exact target _ run alive
  | more run alive inside _ =>
    rw [target _ run alive] at inside
    split at inside <;> cases inside

def Recorded (e : Values) (origin t : MachineState) :=
  Holds context finish t ∧ holds e HonestNameShapes.expect t ∧
    ((t.pc=addr 143 ∧ e.count≠1) ∨ (t.pc=addr 1429 ∧ e.count=1)) ∧
    HonestFlagEffect.Effect origin t (some (markAddr e)) ∧
    ∀ q, protects context q=true → t.getMem q=origin.getMem q

private def Mid (e : Values) (origin s : MachineState) :=
  ∃ k a, s.pc=addr k ∧ HonestWideShapes.current k=some a ∧ Holds context a s ∧
    holds e (HonestNameShapes.current k) s ∧ HonestFlagEffect.Effect origin s (event e (seen k)) ∧
    (k=142 → e.count=1) ∧ ∀ q, protects context q=true → s.getMem q=origin.getMem q

private theorem guard_regs {s : MachineState} {v : Values} (h : holds v (HonestNameShapes.current 141) s) :
    s.getReg .x12=0#64 ↔ v.count=1 := by
  have r := h.1 .x12 ⟨.count,18446744073709551615⟩ (by decide)
  change s.getReg .x12=v.count+18446744073709551615#64 at r
  rw [r]
  generalize v.count=w
  bv_decide

theorem record (numeric : Numeric) (symbolic : Symbolic) (e : Values) (s t : MachineState) (coins : Bool)
    (whereAt : s.pc=addr 143) (ready : Holds context start s) (names : holds e (HonestNameShapes.current 143) s)
    (inside : protects context e.indices=true) (loaded : s.getMem e.indices=e.position)
    (path : HonestCuts.Reaches image coins HonestRecordCost.cut s t) : Recorded e s t := by
  have finer (p : Word) (h : HonestRecordCost.cut p=true) : HonestWideShapes.cut p=true := by
    simp only [HonestRecordCost.cut,Bool.or_eq_true,beq_iff_eq] at h
    rcases h with rfl|rfl <;> decide
  apply HonestNested.carry finer (Mid e s) (Recorded e s) _ ⟨143,start,whereAt,rfl,ready,names,
    HonestFlagEffect.reflexive _,(by intro h; cases h),fun _ _ => rfl⟩ path
  intro u v init walk
  obtain ⟨k,a,pc,shape,source,named,flags,via,frame⟩ := init
  have active := member _ _ shape
  have cc := numeric _ active; have ss := symbolic _ active
  simp only [HonestWideKernel.checked,shape] at cc
  simp only [HonestNameKernel.checked,shape] at ss
  obtain ⟨⟨b,target,mem⟩,same⟩ := HonestWideKernel.sound _ _ _ cc u v coins pc (models_shape source)
    (fun q h => by simp only [Shape.model,h,ite_true]) walk
  obtain ⟨names',flags',guard⟩ := HonestNameKernel.sound _ _ _ _ _ e _ ss s u v coins pc
    (models_shape source) (model named) source.2.2 inside ((frame _ inside).trans loaded) flags walk
  have combine (q : Word) (h : protects context q=true) := (same q h).trans (frame q h)
  let j := HonestBinaryRank.index v.pc
  have aligned : v.pc=addr j := by
    by_contra no
    simp only [HonestWideShapes.target,show HonestBinaryRank.index v.pc=j from rfl,ite_eq_left no,reduceCtorEq] at target
  have accept := not_not_intro aligned
  simp only [HonestWideShapes.target,show HonestBinaryRank.index v.pc=j from rfl,ite_eq_right accept] at target
  change (if j=143 ∨ j=142 then decide (k=141) else if j=1429 then decide (k=142) else true)=true at guard
  constructor
  · intro ended
    simp only [HonestRecordCost.cut,Bool.or_eq_true,beq_iff_eq] at ended
    rcases ended with again|done_
    · have i : j=143 := by change HonestBinaryRank.index v.pc=143; rw [again]; rfl
      simp only [i,true_or,ite_true,Option.some.injEq] at target
      obtain rfl := target
      have fromGuard : k=141 := by simpa only [i,true_or,ite_true,decide_eq_true_eq] using guard
      subst k
      have branch := at_guard pc walk
      have varies : e.count≠1 := by
        intro h; rw [ite_eq_left ((guard_regs named).2 h),again] at branch; exact (by decide : addr 143≠addr 142) branch
      rw [again] at names' flags'
      exact ⟨mem,names',Or.inl ⟨again,varies⟩,flags',combine⟩
    · have i : j=1429 := by change HonestBinaryRank.index v.pc=1429; rw [done_]; rfl
      simp only [i,or_true,ite_true,Option.some.injEq] at target
      obtain rfl := target
      have fromJump : k=142 := by simpa [i] using guard
      rw [done_] at names' flags'
      exact ⟨mem,names',Or.inr ⟨done_,via fromJump⟩,flags',combine⟩
  · intro more
    have notOne : j≠143 := by intro e; rw [aligned,e] at more; cases more
    have notEnd : j≠1429 := by intro e; rw [aligned,e] at more; cases more
    have live : ¬(j=143 ∨ j=1429) := not_or_intro notOne notEnd
    rw [ite_eq_right live] at target
    refine ⟨j,b,aligned,target,mem,?_,?_,?_,combine⟩
    · simpa only [HonestNameShapes.target,show HonestBinaryRank.index v.pc=j from rfl,ite_eq_right live] using names'
    · simpa only [doneAt,show HonestBinaryRank.index v.pc=j from rfl,beq_eq_false_iff_ne.mpr notOne,
        beq_eq_false_iff_ne.mpr notEnd,Bool.false_or] using flags'
    · intro at142
      have on : j=143 ∨ j=142 := Or.inr at142
      have fromGuard : k=141 := by simpa only [ite_eq_left on,decide_eq_true_eq] using guard
      subst k
      have branch := at_guard pc walk
      by_contra no
      rw [ite_eq_right (fun h => no ((guard_regs named).1 h)),aligned,at142] at branch
      exact (by decide : addr 142≠addr 143) branch

end CommitGolfCandidate.Reconstruction.HonestWideRecord
