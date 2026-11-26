import CommitGolfCandidate.ReconstructedCheckStraight
import CommitGolfCandidate.ReconstructedOpeningQuery

namespace CommitGolfCandidate.Reconstruction.CheckEntry
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningOps OpeningQuery TwoPermutationPrototype.RV64
open CommitBlocks (addr)
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000

abbrev W := BitVec.ofNat 64

def indexBase := 738198020
def valuesBase := 754975244

def ops (fp i : Nat) : List Op := [
  .reg .x13 (.slli .x17 3), .reg .x15 (.lui 1), .reg .x15 (.sub .x8 .x15),
  .ld .x15 .x15 1704 (fp-299), .reg .x13 (.add .x13 .x15), .ld .x16 .x13 0 (indexBase+i),
  .reg .x23 (.lui 4096), .reg .x23 (.add .x16 .x23), .reg .x10 (.slli .x10 8),
  .reg .x15 (.srli .x10 8), .reg .x24 (.addi .x24 222), .reg .x20 (.srli .x11 32),
  .reg .x10 (.srli .x12 32), .reg .x13 (.lui 1), .reg .x13 (.sub .x8 .x13), .sd .x13 .x17 1720 (fp-297),
  .reg .x13 (.slli .x17 8), .reg .x17 (.lui 1), .reg .x17 (.sub .x8 .x17), .ld .x17 .x17 1696 (fp-300),
  .reg .x13 (.add .x13 .x17), .reg .x17 (.addi .x6 0)]

private theorem listed (fp i : Nat) : CheckStraight.Listed 175 ((ops fp i).map Op.instr) := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩

structure Entry (m : Model) (fp i : Nat) : Prop where
  fpRoom : 512≤fp ∧ fp<2^33
  slot : i<2^24
  frame : m.reg .x8=wordAddress fp
  ordinal : m.reg .x17=W i
  indexRegion : m.mem (fp-299)=wordAddress indexBase
  valuesRegion : m.mem (fp-300)=wordAddress valuesBase

private theorem shift_nat (i n : Nat) : W i <<< n = W (i*2^n) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,Nat.shiftLeft_eq,Nat.mul_mod]

private theorem ptr (fp off k : Nat) (room : 512≤fp ∧ fp<2^33) (enough : k≤fp) (offset : 8*k+off=4096) :
    wordAddress fp-4096#64+W off=wordAddress (fp-k) := by
  have subWord (a b : Nat) (h : b≤a) (room : a<2^64) : W a-W b=W (a-b) := by
    apply BitVec.eq_of_toNat_eq;simp [BitVec.toNat_sub];omega
  change W (8*fp)-W 4096+W off = W (8*(fp-k))
  rw [subWord _ _ (by omega) (by omega)]
  exact (BitVec.ofNat_add ..).symm.trans (congrArg W (by omega))

private theorem index_addr (i : Nat) : (W i <<< (3 : Nat))+wordAddress indexBase + signExtend12 0=wordAddress (indexBase+i) := by
  have ptrWord : W i <<< (3 : Nat)=wordAddress i := by
    rw [shift_nat];change W (i*8)=W (8*i);congr 1;omega
  rw [ptrWord,show signExtend12 0=0#64 by decide,BitVec.add_zero,BitVec.add_comm (wordAddress i),←wordAddress_add]

private theorem value_addr (i : Nat) : (W i <<< (8 : Nat))+wordAddress valuesBase=wordAddress (valuesBase+32*i) := by
  rw [shift_nat,wordAddress_add,BitVec.add_comm]
  congr 1;change W (i*256)=W (8*(32*i));congr 1;omega

theorem valid (m : Model) (fp i : Nat) (h : Entry m fp i) : Checked m (ops fp i) := by
  simp only [ops,Checked,Op.Valid,Op.apply,true_and,and_true]
  have a:=h.fpRoom;have b:=h.slot
  refine ⟨⟨by omega,?_⟩,⟨by unfold indexBase;omega,?_⟩,⟨by omega,?_⟩,by omega,?_⟩
  · change m.reg .x8-4096#64+1704#64=_
    rw [h.frame];exact ptr fp 1704 299 h.fpRoom (by omega) (by decide)
  · change (m.reg .x17 <<< (3 : Nat))+m.mem (fp-299)+signExtend12 0=_
    rw [h.ordinal,h.indexRegion];exact index_addr i
  · change m.reg .x8-4096#64+1720#64=_
    rw [h.frame];exact ptr fp 1720 297 h.fpRoom (by omega) (by decide)
  · change m.reg .x8-4096#64+1696#64=_
    rw [h.frame];exact ptr fp 1696 300 h.fpRoom (by omega) (by decide)

theorem positive (o : Oracle) (m : Model) (fp i : Nat) (h : Entry m fp i) (s : MachineState)
    (pc : s.pc=addr 175) (fits : Fits s m) :
    let v:=after m (ops fp i)
    ∃ t, CheckRecorded.Segment o 22 s t [] ∧ t.pc=addr 197 ∧ Fits t v ∧
      v.reg .x13=wordAddress (valuesBase+32*i) ∧ v.reg .x16=m.mem (indexBase+i) ∧
      v.reg .x23=m.mem (indexBase+i)+16777216#64 ∧ v.reg .x15=(m.reg .x10 <<< (8 : Nat)) >>> (8 : Nat) ∧
      v.reg .x24=m.reg .x24+222 ∧ v.reg .x17=m.reg .x6 ∧
      v.reg .x20=m.reg .x11 >>> (32 : Nat) ∧ v.reg .x10=m.reg .x12 >>> (32 : Nat) ∧
      v.mem=TwoPermutationPrototype.writeWord m.mem (fp-297) (m.reg .x17) := by
  obtain ⟨t,seg,pt,ht⟩:=CheckStraight.block o m (ops fp i) 175 (by change 175+22≤796;decide) (listed fp i) (valid m fp i h) s pc fits
  refine ⟨t,seg,pt,ht,?_,rfl,rfl,rfl,rfl,?_,rfl,rfl,rfl⟩
  · change (m.reg .x17 <<< (8 : Nat)) + TwoPermutationPrototype.writeWord m.mem (fp-297) (m.reg .x17) (fp-300)=_
    have diff : fp-300≠fp-297:=by have:=h.fpRoom;omega
    rw [TwoPermutationPrototype.writeWord,ite_eq_right diff,h.valuesRegion,h.ordinal,value_addr]
  · change m.reg .x6+0=m.reg .x6;exact BitVec.add_zero _

end CommitGolfCandidate.Reconstruction.CheckEntry
