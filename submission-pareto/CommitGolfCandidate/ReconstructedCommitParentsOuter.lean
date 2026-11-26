import CommitGolfCandidate.ReconstructedCommitParentsGroup

namespace CommitGolfCandidate.Reconstruction.CommitParents.Outer
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding CommitExact
set_option maxHeartbeats 1100000
set_option maxRecDepth 12000

def tailPC (d : Nat) := Image.start d (Image.unroll d)
def back (d : Nat) := BitVec.ofNat 21 (2^21-4*(tailPC d+4-Image.levelStart d))

def ops (d : Nat) : List Instr := [.ADD .x18 .x18 .x22, .ADD .x19 .x19 .x22,
  .ADDI .x20 .x20 4095,.BEQ .x20 .x0 8,.JAL .x0 (back d)]

private def baseOp : Option Instruction → Option Instr
  | some (.base i) => some i
  | _ => none

private theorem code : ∀ d : Fin 24, 10 ≤ d.val → ((ops d).zipIdx).all (fun row =>
    baseOp (decodeInstruction (Image.readAt (tailPC d+row.2))) == some row.1) = true := by decide

theorem fetch_control (d : Fin 24) (hd : 10≤d.val) (i : Fin 5) (s : MachineState)
    (pc : s.pc=CommitBlocks.addr (tailPC d+i.val)) :
    fetch CommitSetup.im s=some (.base ((ops d)[i.val]'i.isLt)) := by
  have member : ((ops d)[i.val]'i.isLt,i.val) ∈ (ops d).zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.2 (List.getElem?_eq_getElem i.isLt)
  have word := beq_iff_eq.1 (List.all_eq_true.1 (code d hd) _ member)
  have lim : ∀ e : Fin 24, tailPC e+5≤150132 := by decide
  have small : tailPC d+i.val <150132 := by have := lim d;have := i.isLt;omega
  change baseOp (decodeInstruction (Image.readAt (tailPC d+i.val)))=some (ops d)[i.val] at word
  rw [Image.readAt,dif_pos small] at word
  apply CommitSetup.fetch_at ⟨_,small⟩ _ _ s pc
  generalize h : decodeInstruction (Artifact.commitCode.get 32 ⟨_,small⟩) = x at word ⊢
  cases x <;> simp_all [baseOp]
  rename_i instr
  cases instr <;> simp_all [baseOp] <;> rfl

private theorem pcadd (i n : Nat) :
    CommitBlocks.addr i+BitVec.ofNat 64 (4*n)=CommitBlocks.addr (i+n) := by
  unfold CommitBlocks.addr;rw [←BitVec.ofNat_add];congr 1;omega

structure EndRegs (s t : MachineState) (n : Nat) : Prop where
  src : t.getReg .x18=s.getReg .x18+s.getReg .x22
  dst : t.getReg .x19=s.getReg .x19+s.getReg .x22
  count : t.getReg .x20=BitVec.ofNat 64 n
  keep : ∀ r, r≠.x18 → r≠.x19 → r≠.x20 → t.getReg r=s.getReg r

private theorem jump_mem (s : MachineState) (off : BitVec 21) : (execInstrBr s (.JAL .x0 off)).mem=s.mem := rfl
private theorem jump_reg (s : MachineState) (off : BitVec 21) (r : Reg) : (execInstrBr s (.JAL .x0 off)).getReg r=s.getReg r := rfl

theorem suffix (o : Oracle) (d : Fin 24) (hd : 10≤d.val) (s : MachineState)
    (start : s.pc=CommitBlocks.addr (tailPC d)) (n : Nat) (small : n < 2^64)
    (count : s.getReg .x20=BitVec.ofNat 64 (n+1)) :
    ∃ t, Segment o CommitSetup.im (if n=0 then 4 else 5) s t ∧
      t.pc=CommitBlocks.addr (if n=0 then tailPC d+5 else Image.start d 0) ∧ t.mem=s.mem ∧ EndRegs s t n := by
  let a := execInstrBr s (.ADD .x18 .x18 .x22)
  let b := execInstrBr a (.ADD .x19 .x19 .x22)
  let c := execInstrBr b (.ADDI .x20 .x20 4095)
  let e := execInstrBr c (.BEQ .x20 .x0 8)
  have sa : Segment o CommitSetup.im 1 s a :=
    plain o _ s a _ (fetch_control d hd 0 s (by simpa using start)) rfl
  have ap : a.pc=CommitBlocks.addr (tailPC d+1) := by rw [CommitBlocks.addr_next,←start];rfl
  have sb : Segment o CommitSetup.im 1 a b := plain o _ a b _ (fetch_control d hd 1 a ap) rfl
  have bp : b.pc=CommitBlocks.addr (tailPC d+2) := by rw [CommitBlocks.addr_next (tailPC d+1),←ap];rfl
  have sc : Segment o CommitSetup.im 1 b c := plain o _ b c _ (fetch_control d hd 2 b bp) rfl
  have cp : c.pc=CommitBlocks.addr (tailPC d+3) := by rw [CommitBlocks.addr_next (tailPC d+2),←bp];rfl
  have se : Segment o CommitSetup.im 1 c e := plain o _ c e _ (fetch_control d hd 3 c cp) rfl
  have s4 := compose (compose (compose sa sb) sc) se
  have word : c.getReg .x20=BitVec.ofNat 64 n := by
    change s.getReg .x20+0xffffffffffffffff#64=_
    rw [count,BitVec.ofNat_add,BitVec.add_assoc,show BitVec.ofNat 64 1+0xffffffffffffffff#64=0 by rfl]
    exact BitVec.add_zero _
  have old : EndRegs s c n := by
    refine ⟨rfl,rfl,word,?_⟩
    intro r x y z
    simp [c,b,a,execInstrBr,MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ x.symm,
      MachineState.getReg_setReg_ne _ _ _ _ y.symm,MachineState.getReg_setReg_ne _ _ _ _ z.symm]
  have proj (t : MachineState) (keep : ∀ r, t.getReg r=c.getReg r) : EndRegs s t n :=
    ⟨(keep _).trans old.src,(keep _).trans old.dst,(keep _).trans old.count,fun r x y z => (keep _).trans (old.keep r x y z)⟩
  have eDecl : e = if c.getReg .x20 == 0 then c.setPC (c.pc+8) else c.setPC (c.pc+4) := rfl
  by_cases z : n=0
  · subst n
    have eq : e=c.setPC (c.pc+8) := by rw [eDecl,word];rfl
    refine ⟨e,by simpa using s4,?_,by rw [eq];rfl,proj e (fun _=>by rw [eq];rfl)⟩
    rw [eq];change c.pc+8=CommitBlocks.addr (tailPC d+5)
    rw [cp];exact pcadd (tailPC d+3) 2
  · have nz : BitVec.ofNat 64 n≠0 := by
      intro h; have g := congrArg BitVec.toNat h
      change n%2^64=0 at g;rw [Nat.mod_eq_of_lt small] at g;exact z g
    have eq : e=c.setPC (c.pc+4) := by
      rw [eDecl,word,beq_eq_false_iff_ne.mpr nz];rfl
    have ep : e.pc=CommitBlocks.addr (tailPC d+4) := by
      rw [eq];change c.pc+4=_;rw [cp];exact pcadd (tailPC d+3) 1
    let u := execInstrBr e (.JAL .x0 (back d))
    have su : Segment o CommitSetup.im 1 e u := plain o _ e u _ (fetch_control d hd 4 e ep) rfl
    have backPC : ∀ f : Fin 24, 10≤f.val →
        CommitBlocks.addr (tailPC f+4)+signExtend21 (back f)=CommitBlocks.addr (Image.start f 0) := by decide
    refine ⟨u,by simpa [z] using compose s4 su,?_,?_,?_⟩
    · change e.pc+signExtend21 (back d)=_
      exact (congrArg (·+signExtend21 (back d)) ep).trans ((backPC d hd).trans (by rw [ite_eq_right z]))
    · apply (jump_mem e (back d)).trans
      rw [eq];rfl
    · apply proj
      intro r;apply (jump_reg e (back d) r).trans
      rw [eq];rfl

end CommitGolfCandidate.Reconstruction.CommitParents.Outer
