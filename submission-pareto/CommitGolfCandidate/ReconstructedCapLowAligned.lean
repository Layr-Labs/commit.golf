import CommitGolfCandidate.ReconstructedCapLowCore

namespace CommitGolfCandidate.Reconstruction.CapLowAligned
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningOps OpeningQuery OpeningCursor OpeningPut CapLowCore
open TwoPermutationPrototype (writeWord)
open TwoPermutationPrototype.RV64
open CommitBlocks (addr)
set_option maxRecDepth 16000
set_option maxHeartbeats 1800000

def ops (c : Nat) : List Op := [.sd .x6 .x14 0 (cell c),.reg .x15 (.srli .x15 3),.reg .x15 (.add .x15 .x17),
  .sd .x15 .x1 0 (cell (c+64)),.reg .x14 (.srli .x30 3),.reg .x14 (.add .x14 .x17),
  .sd .x14 .x16 0 (cell (c+128)),.reg .x7 (.addi .x7 192),.reg .x16 (.srli .x7 3),
  .reg .x30 (.and .x27 .x22),.reg .x16 (.add .x16 .x17),.reg .x14 (.addi .x30 0)]

theorem checks (m : Model) (c : Nat) (room : (c+192)/64<capacity) (pre : Before m c) (align : c%64=0) : Checked m (ops c) := by
  have limit : c+192<2^64 := by unfold capacity at room;omega
  have a64 := CapWriter.byte_at_boundary (c+64) (by omega) (by omega)
  have a128 := CapWriter.byte_at_boundary (c+128) (by omega) (by omega)
  simp only [ops,Checked,Op.Valid,Op.apply,true_and,and_true]
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩
  · have h := CapLowCore.room c room 0 (by decide);simpa only [Nat.add_zero] using (Nat.lt_of_succ_lt h)
  · change m.reg .x6+0#64=wordAddress (cell c);rw [pre.firstAddr,BitVec.add_zero]
  · exact Nat.lt_of_succ_lt (CapLowCore.room c room 64 (by decide))
  · change (m.reg .x15 >>> (3:Nat))+m.reg .x17+0#64=_
    rw [BitVec.add_zero,pre.secondCursor,pre.baseReg,a64]
  · exact Nat.lt_of_succ_lt (CapLowCore.room c room 128 (by decide))
  · change (m.reg .x30 >>> (3:Nat))+m.reg .x17+0#64=_
    rw [BitVec.add_zero,pre.thirdCursor,pre.baseReg,a128]

theorem prepared (m : Model) (c : Nat) (room : (c+192)/64<capacity) (pre : Before m c) (align : c%64=0) :
    Prepared m (after m (ops c)) c := by
  have limit : c+192<2^64 := by unfold capacity at room;omega
  have cursor : m.reg .x7+signExtend12 192=W (c+192) := by rw [pre.cursor];exact (BitVec.ofNat_add ..).symm
  constructor
  · change writeWord (writeWord (writeWord m.mem (cell c) (m.reg .x14)) (cell (c+64)) (m.reg .x1)) (cell (c+128)) (m.reg .x16)=_
    rw [CapWriter.aligned_store _ c 64 _ align (by decide),CapWriter.aligned_store _ (c+64) 64 _ (by omega) (by decide),
      CapWriter.aligned_store _ (c+128) 64 _ (by omega) (by decide)]
    rfl
  · rfl
  · change top m+0#64=_
    rw [BitVec.add_zero,first,ite_eq_left (show (c+192)%64=0 by omega)]
  · change ((m.reg .x7+signExtend12 192) >>> (3:Nat))+m.reg .x17=_
    rw [cursor,pre.baseReg,CapWriter.byte_at_boundary _ limit (by omega)]
  · exact cursor
  · exact pre.offset
  · intro r membership
    apply sameReg
    simp only [fixed,List.mem_cons,List.not_mem_nil,or_false] at membership
    rcases membership with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> cases h <;> rfl

theorem run (o : Oracle) (m : Model) (c : Nat) (room : (c+192)/64<capacity) (pre : Before m c)
    (align : c%64=0) (s : MachineState) (pc : s.pc=addr 1562) (fit : Fits s m) :
    ∃ t, CommitExact.Segment o OpeningStraight.image 12 s t ∧ t.pc=addr 1574 ∧ Fits t (after m (ops c)) ∧ Prepared m (after m (ops c)) c := by
  obtain ⟨t,result,loc,f⟩ := OpeningStraight.block o m (ops c) 1562 (by change 1562+12≤1660;decide)
    ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩ (checks m c room pre align) s pc fit
  exact ⟨t,result,loc,f,prepared m c room pre align⟩

end CommitGolfCandidate.Reconstruction.CapLowAligned
