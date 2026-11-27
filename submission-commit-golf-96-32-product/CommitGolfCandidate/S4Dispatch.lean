import CommitGolfCandidate.S4Header
import CommitGolfCandidate.S4BranchRun

set_option Elab.async false
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt)

theorem boundedCount (i : CheckInput) : i.positions.card≤16777216 := by
  have b : i.positions.card≤LENGTH:=by simpa using Finset.card_le_univ i.positions
  exact b

def modeState (i : CheckInput) := (entered i).setPC (pcAt (if i.positions.card=BATCH then 2657 else 15))
theorem dispatch (i : CheckInput) (o : Oracle) :
    let n:=if i.positions.card=BATCH then 15 else 14
    CheckRuns o (initial i) (modeState i) n 0 ∧ Header i (modeState i) ∧ (modeState i).mem=(initial i).mem := by
  obtain ⟨pre,pc,header,mem⟩:=initialRegisters i o
  have edge:=alternate .check 13 15 2657 .x16 .x6 false (by decide) (by decide) rfl (entered i) pc
  have flag : (((entered i).getReg .x16==(entered i).getReg .x6)==false)=decide (i.positions.card≠BATCH):=by
    rw [header.rawCount,header.batch]
    change ((W i.positions.card==W BATCH)==false)=_
    rw [eqNatural _ _ (by have:=boundedCount i;omega) (by decide)]
    by_cases b : i.positions.card=BATCH <;> simp [b]
  rw [flag] at edge
  have unchanged (s : MachineState) (n : Nat) (h : Header i s) : Header i (s.setPC (pcAt n)) :=
    ⟨⟨h.mode,h.kind,h.width,h.three,h.root,h.data.regs rfl⟩,⟨h.index,h.value,h.proof,h.count⟩,h.rawCount,h.proofLen,h.batch⟩
  refine ⟨?_,unchanged _ _ header,mem⟩
  by_cases b : i.positions.card=BATCH
  · rw [decide_eq_false (not_not_intro b)] at edge
    rw [if_pos b]
    change CheckRuns o (initial i) ((entered i).setPC _) 15 0
    rw [if_pos b];exact pre.trans (ofRuns o edge)
  · rw [decide_eq_true b] at edge
    rw [if_neg b]
    change CheckRuns o (initial i) ((entered i).setPC _) 14 0
    rw [if_neg b];exact pre.trans (ofRuns o edge)

structure NormalStart (i : CheckInput) (s : MachineState) extends Env i s,Cursor i s 0 : Prop where
  pc : s.pc=pcAt 21
  len : i.proof.length=824*i.positions.card
  positive : 0 < i.positions.card

attribute [local irreducible] entered normalGuard initial
set_option maxRecDepth 4000 in
theorem normalDispatch (o : Oracle) (i : CheckInput) (normal : i.positions.card≠BATCH)
    (sized : i.proof.length≤Late.submission.sizes.proof) :
    (i.proof.length≠824*i.positions.card ∧ ∃ n≤24,Finishes o (initial i) n 0 .failure) ∨
    (i.proof.length=824*i.positions.card ∧ i.positions.card=0 ∧ ∃ n≤24,Finishes o (initial i) n 0 .success) ∨
    ∃ s,NormalStart i s ∧ ∃ n≤24,CheckRuns o (initial i) s n 0 := by
  obtain ⟨base,hdr,_⟩:=dispatch i o
  simp only [if_neg normal] at base
  let s:=modeState i
  have pc : s.pc=pcAt 15:=by simp only [s,modeState,if_neg normal];rfl
  obtain ⟨guard,at17,product,keep,mem⟩:=normalSize s o pc
  let t:=normalGuard s
  have count : t.getReg .x16=W i.positions.card:=(keep _ (by decide) (by decide)).trans hdr.rawCount
  have len : t.getReg .x17=W i.proof.length:=(keep _ (by decide) (by decide)).trans hdr.proofLen
  have val : t.getReg .x7=W (824*i.positions.card):=by
    rw [product,hdr.rawCount];change W _*W 824=_
    rw [←BitVec.ofNat_mul,Nat.mul_comm]
  have price:=alternate .check 17 19 4855 .x7 .x17 true (by decide) (by decide) rfl t at17
  have nlim:=boundedCount i
  change i.proof.length≤17179869184 at sized
  have eqv : ((t.getReg .x7==t.getReg .x17)==true)=decide (824*i.positions.card=i.proof.length):=by
    rw [val,len,eqNatural _ _ (by omega) (by omega)];simp
  rw [eqv] at price
  by_cases good : i.proof.length=824*i.positions.card
  · rw [decide_eq_true good.symm] at price
    let u:=t.setPC (pcAt 19)
    have enteredOk : CheckRuns o (initial i) u 17 0:= (base.trans guard).trans (ofRuns o price)
    have checkZero:=alternate .check 19 21 4852 .x16 .x0 false (by decide) (by decide) rfl u rfl
    have zero : ((u.getReg .x16==u.getReg .x0)==false)=decide (i.positions.card≠0):=by
      change ((t.getReg .x16==W 0)==false)=_
      rw [count,eqNatural _ _ (by omega) (by decide)];by_cases z : i.positions.card=0 <;> simp [z]
    rw [zero] at checkZero
    by_cases empty : i.positions.card=0
    · rw [decide_eq_false (not_not_intro empty)] at checkZero
      exact Or.inr (Or.inl ⟨good,empty,22,by decide,((enteredOk.trans (ofRuns o checkZero)).finish (verdict true _ o rfl))⟩)
    · rw [decide_eq_true empty] at checkZero
      let z:=u.setPC (pcAt 21)
      refine Or.inr (Or.inr ⟨z,?_,18,by decide,enteredOk.trans (ofRuns o checkZero)⟩)
      have stable (r : Reg) (a : r≠.x7) (b : r≠.x6) : z.getReg r=s.getReg r:=(MachineState.getReg_setPC.trans MachineState.getReg_setPC).trans (keep r a b)
      have data : InputsStill i z:=@InputsStill.regs i s z hdr.data (show z.mem=s.mem from mem)
      exact ⟨⟨(stable _ (by decide) (by decide)).trans hdr.mode,(stable _ (by decide) (by decide)).trans hdr.kind,
        (stable _ (by decide) (by decide)).trans hdr.width,(stable _ (by decide) (by decide)).trans hdr.three,
        (stable _ (by decide) (by decide)).trans hdr.root,data⟩,
        ⟨(stable _ (by decide) (by decide)).trans hdr.index,(stable _ (by decide) (by decide)).trans hdr.value,
        (stable _ (by decide) (by decide)).trans hdr.proof,(stable _ (by decide) (by decide)).trans hdr.count⟩,rfl,good,by omega⟩
  · rw [decide_eq_false (Ne.symm good)] at price
    exact Or.inl ⟨good,21,by decide,((base.trans guard).trans (ofRuns o price)).finish (verdict false _ o rfl)⟩
end CommitGolfCandidate.S4.Machine
