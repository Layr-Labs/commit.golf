import CommitGolfCandidate.ReconstructedCheckParentGeometry

namespace CommitGolfCandidate.Reconstruction.CheckParent
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding Binding.Machine
open CheckValues CheckOrdinary CheckParentImage CheckParentRun CheckParentPlan CheckParentCall CheckParentWords CheckParentExecution CheckOracleMemory CheckRecorded CheckParentGeometry
set_option maxRecDepth 18000
set_option maxHeartbeats 1300000
attribute [local irreducible] readBuffer

def Cost (d : Nat) := steps d 0 (work d) (start d)+1

def Called (s : MachineState) (d : Fin 24) (g : Geometry) :=
  s.pc=CommitBlocks.addr 674 ∧ s.getReg .x2=BitVec.ofNat 64 (g.stack+144) ∧
  s.getReg .x10=BitVec.ofNat 64 g.out ∧ s.getReg .x11=BitVec.ofNat 64 d ∧ s.getReg .x12=BitVec.ofNat 64 g.pair

structure Post (o : Oracle) (g : Geometry) (d : Nat) (l r : Binding.Digest) (s t : MachineState) : Prop where
  output : CommitParents.cell t g.out = parent (oracleCompression o) d l r
  returnPC : t.pc=((s.getReg .x1 + signExtend12 0) &&& ~~~1#64)
  stack : t.getReg .x2=s.getReg .x2
  framePointer : t.getReg .x8=s.getReg .x8
  returnAddress : t.getReg .x1=s.getReg .x1
  calleeSaved : ∀ v∈CheckParentPlan.preserved, t.getReg v=s.getReg v
  memory : ∀ p, (∀ i : Fin 18, p≠BitVec.ofNat 64 (g.stack+8*i.val)) →
    (∀ i : Fin 4, p≠BitVec.ofNat 64 (g.out+8*i.val)) → t.getMem p=s.getMem p

private theorem as_digest (s : MachineState) (dst : Nat) (x : Binding.Digest) (align : dst%8=0)
    (words : ∀ i : Fin 4, s.getMem (BitVec.ofNat 64 (dst+8*i.val))=digWord x i) : CommitParents.cell s dst=x := by
  have read := read_words_eq s dst 4 (pack x) align (fun i hi => words ⟨i,hi⟩)
  change (readBuffer s dst 32).cast _ = pack x at read
  rw [BitVec.cast_eq] at read
  exact (congrArg unpack read).trans (Binding.unpack_pack x)

/-- Exact compiled checker parent, for both the individual-record and the
shared-cap calling conventions. It records every paid hash and returns the
reference projection while retaining caller-owned memory and registers. -/
theorem positive (o : Oracle) (g : Geometry) (placed : Placed g) (s : MachineState) (d : Fin 24)
    (call : Called s d g) (rodata : constants s) (l r : Binding.Digest)
    (left : CommitParents.cell s g.pair=l) (right : CommitParents.cell s (g.pair+32)=r) :
    ∃ t, Segment o (Cost d) s t (rows o (pairKey (d.val+1) l r) 0 (work d)) ∧ Post o g d l r s t := by
  let seed := pairKey (d.val+1) l r
  let e := env g s o seed
  have lay := CheckParentGeometry.layout g placed s rodata o seed
  have pars := parameters g placed s o d l r left right
  obtain ⟨pc,sp,out,depth,pair⟩ := call
  have args : initialArgs s e d := by
    refine ⟨rfl,pc,?_,?_,depth,?_⟩
    · rw [phys_loc _ _ _ _ 1 144 (by decide)];exact sp
    · rw [phys_loc _ _ _ _ 3 0 (by decide)];exact out
    · rw [phys_loc _ _ _ _ 2 0 (by decide)];exact pair
  obtain ⟨t,sg,post⟩ := execute_parent o e lay d seed pars s args
  refine ⟨t,sg,⟨?_,post.pc,post.sp,post.fp,post.ra,post.preserved,?_⟩⟩
  · apply as_digest t g.out _ (placed.align 3)
    intro i
    have value := post.output i
    rw [phys_loc _ _ _ _ 3 _ (by have := i.isLt;omega)] at value
    exact value.trans (output_word o e d l r (fun _ _ _ _=>rfl) i)
  · intro p st ou
    apply post.frame
    intro a safe writable
    obtain ⟨reg,offset⟩ := a
    rcases writable with rw₁|rw₃
    · change reg=1 at rw₁;subst reg
      change decide (offset.toNat%8=0) && decide (offset.toNat<144)=true at safe
      simp only [Bool.and_eq_true,decide_eq_true_eq] at safe
      have k : offset.toNat/8<18 := by omega
      rw [physical_nat];change p≠BitVec.ofNat 64 (g.stack+offset.toNat)
      have eq : offset.toNat=8*(offset.toNat/8) := by omega
      conv_rhs => rw [eq]
      exact st ⟨_,k⟩
    · change reg=3 at rw₃;subst reg
      change decide (offset.toNat%8=0) && decide (offset.toNat<32)=true at safe
      simp only [Bool.and_eq_true,decide_eq_true_eq] at safe
      have k : offset.toNat/8<4 := by omega
      rw [physical_nat];change p≠BitVec.ofNat 64 (g.out+offset.toNat)
      have eq : offset.toNat=8*(offset.toNat/8) := by omega
      conv_rhs => rw [eq]
      exact ou ⟨_,k⟩

end CommitGolfCandidate.Reconstruction.CheckParent
