import CommitGolfCandidate.ReconstructedCapLowMergedWords

namespace CommitGolfCandidate.Reconstruction.CapLowMerged
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningOps OpeningQuery OpeningCursor OpeningPut CapLowCore
open CapLowMergedWords (aOps bOps cOps)
open TwoPermutationPrototype.RV64
open CommitBlocks (addr)
set_option maxRecDepth 24000
set_option maxHeartbeats 2300000

def endOps (c : Nat) : List Op := [.reg .x12 (.srli .x7 3),.reg .x12 (.andi .x12 4088),.reg .x16 (.add .x12 .x17),
  .ld .x12 .x16 0 (cell c),.reg .x30 (.and .x27 .x22),.reg .x14 (.sll .x30 .x26),.reg .x14 (.or .x12 .x14)]

def allOps (c : Nat) := aOps c ++ bOps (c+64) ++ cOps (c+128) ++ endOps (c+192)

theorem append_checks (m : Model) (a b : List Op) (h : Checked m a) (g : Checked (after m a) b) : Checked m (a++b) := by
  induction a generalizing m with
  | nil => exact g
  | cons op ops ih => exact ⟨h.1,ih _ h.2 g⟩

theorem final (m : Model) (c : Nat) (room : (c+192)/64<capacity) (pre : Before m c)
    (nz : c%64≠0) (zero : m.reg .x0=0) : Checked m (allOps c) ∧ Prepared m (after m (allOps c)) c := by
  let a := after m (aOps c)
  let b := after a (bOps (c+64))
  let v := after b (cOps (c+128))
  let t := after v (endOps (c+192))
  have limit : c+192<2^64 := by unfold capacity at room;omega
  have room' := CapLowCore.room c room
  have r0 : cell c+1<2^33 := by simpa only [Nat.add_zero] using room' 0 (by decide : 0≤192)
  obtain ⟨ha,ma,neg⟩ := CapLowMergedWords.a m c r0 pre.firstAddr zero pre.offset nz
  have aBase : a.reg .x17=wordAddress base := pre.baseReg
  have aOff : a.reg .x26=W ((c+64)%64) := by rw [show (c+64)%64=c%64 by omega];exact pre.offset
  have negB : (a.reg .x29).toNat%64=64-(c+64)%64 := by rw [show (c+64)%64=c%64 by omega];exact neg
  obtain ⟨hb,mb⟩ := CapLowMergedWords.b a (c+64) (room' 64 (by decide)) (by omega) pre.secondCursor aBase negB aOff (by omega)
  have bOff : b.reg .x26=W ((c+128)%64) := by rw [show (c+128)%64=c%64 by omega];exact pre.offset
  have negC : (b.reg .x29).toNat%64=64-(c+128)%64 := by rw [show (c+128)%64=c%64 by omega];exact neg
  obtain ⟨hc,mc⟩ := CapLowMergedWords.third b (c+128) (room' 128 (by decide)) (by omega) pre.thirdCursor aBase negC bOff (by omega)
  have newCursor : v.reg .x7=W (c+192) := by
    change m.reg .x7+signExtend12 192=_;rw [pre.cursor];exact (BitVec.ofNat_add ..).symm
  have dest : ((v.reg .x7 >>> (3:Nat)) &&& signExtend12 4088)+v.reg .x17=wordAddress (cell (c+192)) := by
    rw [newCursor,show v.reg .x17=wordAddress base from pre.baseReg,word_address _ limit]
  have hd : Checked v (endOps (c+192)) := by
    simp only [endOps,Checked,Op.Valid,Op.apply,true_and,and_true]
    refine ⟨Nat.lt_of_succ_lt (room' 192 (by decide)),?_⟩
    change (((v.reg .x7 >>> (3:Nat)) &&& signExtend12 4088)+v.reg .x17)+0#64=_
    rw [BitVec.add_zero,dest]
  constructor
  · apply append_checks
    · apply append_checks
      · exact append_checks _ _ _ ha hb
      · exact hc
    · exact hd
  change Prepared m t c
  constructor
  · change v.mem=_
    change v.mem=put b.mem (c+128) 64 (b.reg .x16) at mc
    change b.mem=put a.mem (c+64) 64 (a.reg .x1) at mb
    change a.mem=put m.mem c 64 (m.reg .x14) at ma
    rw [mc,mb,ma];rfl
  · rfl
  · change v.mem (cell (c+192)) ||| (top m <<< ((v.reg .x26).toNat%64))=first v.mem (c+192) (top m)
    have off : v.reg .x26=W (c%64) := pre.offset
    rw [off,CapLowMergedWords.amount,first,ite_eq_right (show (c+192)%64≠0 by omega),show (c+192)%64=c%64 by omega]
  · exact dest
  · exact newCursor
  · exact pre.offset
  · intro r mem
    change (after m (allOps c)).reg r=m.reg r
    apply sameReg
    simp only [fixed,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> cases h <;> rfl

theorem run (o : Oracle) (m : Model) (c : Nat) (room : (c+192)/64<capacity) (pre : Before m c)
    (nz : c%64≠0) (zero : m.reg .x0=0) (s : MachineState) (pc : s.pc=addr 1528) (fit : Fits s m) :
    ∃ t, CommitExact.Segment o OpeningStraight.image 34 s t ∧ t.pc=addr 1574 ∧ Fits t (after m (allOps c)) ∧
      Prepared m (after m (allOps c)) c := by
  obtain ⟨checked,model⟩ := final m c room pre nz zero
  have table : OpeningStraight.Listed 1528 ((allOps c).map Op.instr) := by
    repeat' apply And.intro
    all_goals first | rfl | exact True.intro
  obtain ⟨u,a,p,f⟩ := OpeningStraight.block o m (allOps c) 1528 (by change 1528+33≤1660;decide) table checked s pc fit
  have branch : CommitExact.Segment o OpeningStraight.image 1 u (u.setPC (addr 1574)) := by
    apply CommitExact.plain o _ _ _ (.base (.JAL .x0 52)) (OpeningStraight.fetched 1561 _ (by decide) rfl u p)
    change some (u.setPC (u.pc+signExtend21 52))=_;rw [p];rfl
  exact ⟨_,CommitExact.compose a branch,rfl,f.pc _,model⟩

end CommitGolfCandidate.Reconstruction.CapLowMerged
