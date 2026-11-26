import CommitGolfCandidate.ReconstructedCheckWalk
import CommitGolfCandidate.ReconstructedCheckRecordABI

namespace CommitGolfCandidate.Reconstruction.CheckInitLower
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningOps CheckRecorded CheckLayout
open TwoPermutationPrototype.RV64
set_option maxRecDepth 12000
set_option maxHeartbeats 1300000
abbrev W:=BitVec.ofNat 64

def code : List Op := [
  .reg .x26 (.addi .x0 24),.reg .x21 (.addi .x0 23),.reg .x10 (.lui 1),.reg .x10 (.sub .x8 .x10),
  .ld .x9 .x10 1688 ((CheckLayout.fp-2408)/8),.reg .x22 (.lui 512),.reg .x22 (.addi .x22 400)]

def saved : List Reg := [.x2,.x8,.x19,.x23,.x24,.x18,.x27,.x25,.x20,.x12,.x13,.x14,.x11]

theorem positive (o : Oracle) (s : MachineState) (pc : s.pc=CommitBlocks.addr 238)
    (fp : s.getReg .x8=W CheckLayout.fp) (widths : s.getMem (W (CheckLayout.fp-2408))=W 2097352) :
    ∃ t, Segment o 8 s t [] ∧ t.pc=CommitBlocks.addr 280 ∧
      t.getReg .x26=24 ∧ t.getReg .x21=23 ∧ t.getReg .x9=W 2097352 ∧ t.getReg .x22=W 2097552 ∧
      (∀ r∈saved,t.getReg r=s.getReg r) ∧ ∀ p,p<2^33→t.getMem (wordAddress p)=s.getMem (wordAddress p) := by
  let m:=CheckRecordHeader.model s
  have ok : Checked m code:=by
    simp only [code,Checked,Op.Valid,Op.apply,true_and,and_true]
    refine ⟨by decide,?_⟩
    change s.getReg .x8-4096#64+1688#64=_
    rw [fp];decide
  have list : CheckStraight.Listed 238 (code.map Op.instr):=⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
  obtain ⟨u,seg,pos,fit⟩:=CheckStraight.block o m code 238 (by decide) list ok s pc (CheckRecordHeader.fits s)
  have jump:=CheckBranch.jump o u 245 280 140 (by decide) pos rfl (by decide)
  refine ⟨_,by simpa only [List.nil_append,show code.length=7 by decide] using compose seg jump,rfl,?_,?_,?_,?_,?_,?_⟩
  · change u.getReg .x26=_;rw [fit.registers];rfl
  · change u.getReg .x21=_;rw [fit.registers];rfl
  · change u.getReg .x9=_;rw [fit.registers];exact widths
  · change u.getReg .x22=_;rw [fit.registers];rfl
  · intro r hr; change u.getReg r=_;rw [fit.registers];cases r <;> first | rfl | cases (by simpa [saved] using hr : False)
  · exact fit.memory

end CommitGolfCandidate.Reconstruction.CheckInitLower
