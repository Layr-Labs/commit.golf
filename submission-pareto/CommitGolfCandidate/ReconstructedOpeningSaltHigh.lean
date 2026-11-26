import CommitGolfCandidate.ReconstructedOpeningSaltLow

namespace CommitGolfCandidate.Reconstruction.OpeningSaltHigh
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningOps OpeningQuery OpeningLane
open TwoPermutationPrototype.RV64 OpeningPut OpeningCursor OpeningReply
open TwoPermutationPrototype (writeWord)
open CommitBlocks (addr)
set_option maxRecDepth 14000
set_option maxHeartbeats 1400000

def loadOps (l : Fin 12) : List Op := [
  .reg .x12 (.addi .x7 64), .reg .x11 (.addi .x11 1), .reg .x11 (.slli .x11 32),
  .reg .x11 (.srli .x11 29), .reg .x11 (.add .x6 .x11), .ld .x13 .x11 0 (replyBase+(LeafNonce.nextWord l).val),
  .reg .x12 (.srli .x12 3), .reg .x11 (.andi .x12 4088), .reg .x11 (.add .x11 .x25),
  .reg .x12 (.slli .x13 8), .reg .x12 (.srli .x12 8)]

private theorem loadTable (l : Fin 12) : OpeningStraight.Listed 214 ((loadOps l).map Op.instr) :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩

def clip (w : Word) := W (w.toNat%2^56)
theorem clipped (w : Word) : (w <<< (8 : Nat)) >>> (8 : Nat) = clip w := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight,BitVec.toNat_shiftLeft,Nat.shiftRight_eq_div_pow,Nat.shiftLeft_eq,
    clip,W,BitVec.toNat_ofNat]
  omega

private theorem loadChecks (m : Model) (l : Fin 12) (stack : m.reg .x6=wordAddress replyBase)
    (index : m.reg .x11=W (LeafNonce.firstWord l).val) :
    Checked m (loadOps l) := by
  simp only [loadOps,Checked,Op.Valid,true_and,and_true]
  refine ⟨by have := (LeafNonce.nextWord l).isLt;unfold replyBase;omega,?_⟩
  change m.reg .x6+((((m.reg .x11+1) <<< (32 : Nat)) >>> (29 : Nat)))+signExtend12 0=_
  rw [stack,index];fin_cases l <;> rfl

theorem loaded (m : Model) (c : Nat) (l : Fin 12) (fit : c+64<2^64)
    (cursor : m.reg .x7=W c) (baseReg : m.reg .x25=wordAddress base) :
    let t := after m (loadOps l)
    t.reg .x12=clip (m.mem (replyBase+(LeafNonce.nextWord l).val)) ∧
      t.reg .x11=wordAddress (cell (c+64)) ∧ t.mem=m.mem ∧
      (∀ r, r≠.x11 → r≠.x12 → r≠.x13 → t.reg r=m.reg r) := by
  refine ⟨clipped _,?_,rfl,?_⟩
  · change (((m.reg .x7+64) >>> (3 : Nat)) &&& signExtend12 4088)+m.reg .x25=_
    rw [cursor,baseReg]
    have add : W c+64=W (c+64) := (BitVec.ofNat_add ..).symm
    rw [add,word_address (c+64) fit]
  · intro r x y z;simp [after,loadOps,Op.apply,Model.set,x.symm,y.symm,z.symm]

theorem load_run (o : Oracle) (m : Model) (l : Fin 12) (s : MachineState) (pc : s.pc=addr 214)
    (h : Fits s m) (stack : m.reg .x6=wordAddress replyBase) (index : m.reg .x11=W (LeafNonce.firstWord l).val) :
    ∃ t, CommitExact.Segment o OpeningStraight.image 11 s t ∧ t.pc=addr 225 ∧ Fits t (after m (loadOps l)) :=
  OpeningStraight.block o m (loadOps l) 214 (by change 214+11≤1660;decide) (loadTable l)
    (loadChecks m l stack index) s pc h

def directOps (atBit : Nat) : List Op := [.sd .x11 .x12 0 (cell atBit)]
def mergeOps (atBit : Nat) : List Op := [
  .ld .x13 .x11 0 (cell atBit),.reg .x14 (.sll .x12 .x10),.reg .x13 (.or .x13 .x14),
  .sd .x11 .x13 0 (cell atBit),.reg .x13 (.addi .x0 9)]
def spillOps (atBit : Nat) : List Op := [
  .reg .x10 (.subw .x0 .x10),.reg .x10 (.srl .x12 .x10),.sd .x11 .x10 8 (cell atBit+1)]

private theorem directTable (c : Nat) : OpeningStraight.Listed 236 ((directOps c).map Op.instr) := ⟨rfl,True.intro⟩
private theorem mergeTable (c : Nat) : OpeningStraight.Listed 226 ((mergeOps c).map Op.instr) :=
  ⟨rfl,rfl,rfl,rfl,rfl,True.intro⟩
private theorem spillTable (c : Nat) : OpeningStraight.Listed 232 ((spillOps c).map Op.instr) :=
  ⟨rfl,rfl,rfl,True.intro⟩

private theorem checked_direct (m : Model) (c : Nat) (room : cell c+1<2^33) (dst : m.reg .x11=wordAddress (cell c)) :
    Checked m (directOps c) := ⟨⟨by omega,by rw [dst];exact BitVec.add_zero _⟩,True.intro⟩
private theorem checked_merge (m : Model) (c : Nat) (room : cell c+1<2^33) (dst : m.reg .x11=wordAddress (cell c)) :
    Checked m (mergeOps c) := by
  simp only [mergeOps,Checked,Op.Valid,true_and,and_true]
  have addrOk : m.reg .x11+signExtend12 0=wordAddress (cell c) := by rw [dst];exact BitVec.add_zero _
  exact ⟨⟨by omega,addrOk⟩,⟨by omega,addrOk⟩⟩
private theorem checked_spill (m : Model) (c : Nat) (room : cell c+1<2^33) (dst : m.reg .x11=wordAddress (cell c)) :
    Checked m (spillOps c) := by
  simp only [spillOps,Checked,Op.Valid,true_and,and_true]
  refine ⟨room,?_⟩;change m.reg .x11+signExtend12 8=_
  rw [dst,wordAddress_add];rfl

private theorem offset_test (o : Oracle) (s : MachineState) (pc : s.pc=addr 231)
    (off : Fin 64) (reg : s.getReg .x10=W off.val) (nine : s.getReg .x13=9) :
    CommitExact.Segment o OpeningStraight.image 1 s (s.setPC (if off.val<9 then addr 237 else addr 232)) := by
  have f := OpeningStraight.fetched 231 (.base (.BLTU .x10 .x13 24)) (by decide) rfl s pc
  apply CommitExact.plain o _ _ _ _ f
  change some (if (s.getReg .x10).ult (s.getReg .x13) then s.setPC (s.pc+signExtend13 24) else s.setPC (s.pc+4)) = _
  rw [pc,reg,nine]
  fin_cases off <;> rfl

private theorem jump (o : Oracle) (s : MachineState) (pc : s.pc=addr 235) :
    CommitExact.Segment o OpeningStraight.image 1 s (s.setPC (addr 237)) := by
  apply CommitExact.plain o _ _ _ (.base (.JAL .x0 8)) (OpeningStraight.fetched _ _ (by decide) rfl s pc)
  change some (s.setPC (s.pc+signExtend21 8))=_
  rw [pc];rfl

def output (m : Model) (c : Nat) := if c%64=0 then after m (directOps c) else
  let a := after m (mergeOps c)
  if c%64<9 then a else after a (spillOps c)

def steps (c : Nat) := if c%64=0 then 2 else if c%64<9 then 7 else 11

theorem write_run (o : Oracle) (m : Model) (c : Nat) (room : cell c+1<2^33) (s : MachineState)
    (pc : s.pc=addr 225) (fits : Fits s m) (zero : m.reg .x0=0)
    (off : m.reg .x10=W (c%64)) (dst : m.reg .x11=wordAddress (cell c)) :
    ∃ t, CommitExact.Segment o OpeningStraight.image (steps c) s t ∧ t.pc=addr 237 ∧ Fits t (output m c) := by
  have g := zero_branch o s 225 226 236 .x10 44 pc (by decide) rfl rfl rfl (W (c%64)) ((fits.registers _).trans off)
  have ziff : W (c%64)=0 ↔ c%64=0 := by
    constructor
    · intro z;have n := congrArg BitVec.toNat z
      change (c%64)%2^64=0 at n;omega
    · intro z;rw [z];rfl
  simp only [ziff] at g
  unfold steps output
  by_cases z : c%64=0
  · simp only [z,ite_true] at g ⊢
    obtain ⟨t,r,p,h⟩ := OpeningStraight.block o m (directOps c) 236 (by change 236+1≤1660;decide)
      (directTable c) (checked_direct m c room dst) (s.setPC _) rfl (fits.pc _)
    exact ⟨t,CommitExact.compose g r,p,h⟩
  · simp only [z,ite_false] at g ⊢
    let a := after m (mergeOps c)
    obtain ⟨v,r,p,h⟩ := OpeningStraight.block o m (mergeOps c) 226 (by change 226+5≤1660;decide)
      (mergeTable c) (checked_merge m c room dst) (s.setPC _) rfl (fits.pc _)
    have off' : v.getReg .x10=W (c%64) := (h.registers _).trans off
    have n9 : a.reg .x13=9 := by change m.reg .x0+9=9;rw [zero];rfl
    have nine : v.getReg .x13=9 := (h.registers _).trans n9
    have test := offset_test o v p ⟨c%64,by omega⟩ off' nine
    by_cases small : c%64<9
    · simp only [small,ite_true] at test ⊢
      exact ⟨_,CommitExact.compose (CommitExact.compose g r) test,rfl,h.pc _⟩
    · simp only [small,ite_false] at test ⊢
      obtain ⟨w,rw,pw,hw⟩ := OpeningStraight.block o a (spillOps c) 232 (by change 232+3≤1660;decide)
        (spillTable c) (checked_spill a c room dst) (v.setPC _) rfl (h.pc _)
      exact ⟨_,CommitExact.compose (CommitExact.compose (CommitExact.compose (CommitExact.compose g r) test) rw)
        (jump o w pw),rfl,hw.pc _⟩

theorem memory (m : Model) (c : Nat) (zero : m.reg .x0=0) (off : m.reg .x10=W (c%64)) :
    (output m c).mem=put m.mem c 56 (m.reg .x12) := by
  have ord : (m.reg .x10).toNat%64=c%64 := by rw [off];change ((c%64)%2^64)%64=c%64;omega
  unfold output put
  by_cases align : c%64=0
  · simp [align,first];rfl
  · simp only [align,ite_false]
    have merged : (after m (mergeOps c)).mem =
        writeWord m.mem (cell c) (first m.mem c (m.reg .x12)) := by
      change writeWord m.mem _ (m.mem (cell c) ||| (m.reg .x12 <<< ((m.reg .x10).toNat%64)))=_
      rw [ord,first,ite_eq_right align]
    by_cases little : c%64<9
    · rw [ite_eq_left little,ite_eq_right (by omega : ¬c%64+56>64)]
      exact merged
    · rw [ite_eq_right little,ite_eq_left (by omega : c%64+56>64)]
      let a := after m (mergeOps c)
      change writeWord a.mem (cell c+1) (m.reg .x12 >>> ((((m.reg .x0).truncate 32 -
        (m.reg .x10).truncate 32).signExtend 64).toNat%64)) = _
      rw [show a.mem=_ from merged,zero,off]
      have sh := negative_shift ⟨c%64,Nat.mod_lt _ (by decide)⟩ (Nat.pos_of_ne_zero align)
      exact congrArg (fun n : Nat => writeWord _ (cell c+1) (m.reg .x12 >>> n)) sh

theorem frame (m : Model) (c : Nat) (r : Reg) (x : r≠.x10) (y : r≠.x13) (z : r≠.x14) :
    (output m c).reg r=m.reg r := by
  unfold output
  split
  · rfl
  · split
    · simp [after,mergeOps,Op.apply,Model.set,Model.store,y.symm,z.symm]
    · simp [after,spillOps,mergeOps,Op.apply,Model.set,Model.store,x.symm,y.symm,z.symm]

end CommitGolfCandidate.Reconstruction.OpeningSaltHigh
