import CommitGolfCandidate.ReconstructedOpeningBranch
import CommitGolfCandidate.ReconstructedOpeningSaltLow

namespace CommitGolfCandidate.Reconstruction.OpeningHeaderWrite
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningOps OpeningQuery
open TwoPermutationPrototype.RV64 OpeningPut OpeningCursor TwoPermutationPrototype
open CommitBlocks (addr)
set_option maxRecDepth 12000

def clip (w : Word) := W (w.toNat%2^38)
theorem clipped (w : Word) : (w <<< (26 : Nat)) >>> (26 : Nat)=clip w := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight,BitVec.toNat_shiftLeft,Nat.shiftRight_eq_div_pow,Nat.shiftLeft_eq,
    clip,W,BitVec.toNat_ofNat]
  omega

def prepare : List Op := [.reg .x11 (.addi .x7 184),.reg .x12 (.andi .x11 63),
  .reg .x11 (.srli .x11 3),.reg .x11 (.andi .x11 4088),.reg .x11 (.add .x11 .x25),
  .reg .x13 (.slli .x13 26),.reg .x14 (.srli .x13 26)]

def direct (c : Nat) : List Op := [.sd .x11 .x14 0 (cell c),.reg .x11 (.lui 1),.reg .x11 (.sub .x8 .x11),
  .ld .x9 .x11 1848 8589934261,.reg .x18 (.addi .x0 64)]
def merge (c : Nat) : List Op := [.ld .x13 .x11 0 (cell c),.reg .x16 (.sll .x14 .x12),.reg .x13 (.or .x13 .x16),
  .sd .x11 .x13 0 (cell c),.reg .x13 (.lui 1),.reg .x13 (.sub .x8 .x13),.ld .x9 .x13 1848 8589934261,
  .reg .x18 (.addi .x0 64),.reg .x13 (.addi .x0 27)]
def spill (c : Nat) : List Op := [.reg .x12 (.subw .x0 .x12),.reg .x12 (.srl .x14 .x12),.sd .x11 .x12 8 (cell c+1)]

private theorem prepareTable : OpeningStraight.Listed 389 ((prepare).map Op.instr) := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
private theorem directTable (c : Nat) : OpeningStraight.Listed 411 ((direct c).map Op.instr) := ⟨rfl,rfl,rfl,rfl,rfl,True.intro⟩
private theorem mergeTable (c : Nat) : OpeningStraight.Listed 397 ((merge c).map Op.instr) := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
private theorem spillTable (c : Nat) : OpeningStraight.Listed 407 ((spill c).map Op.instr) := ⟨rfl,rfl,rfl,True.intro⟩

private theorem checks (m : Model) (c : Nat) (room : cell c+1<2^33) (ptr : m.reg .x11=wordAddress (cell c))
    (stack : m.reg .x8=68719476336) :
    Checked m (direct c) ∧ Checked m (merge c) ∧ Checked m (spill c) := by
  have dst : m.reg .x11+signExtend12 0=wordAddress (cell c) := by rw [ptr];exact BitVec.add_zero _
  have next : m.reg .x11+signExtend12 8=wordAddress (cell c+1) := by rw [ptr,wordAddress_add];rfl
  have save : (m.reg .x8-(((1 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64))+ signExtend12 1848=wordAddress 8589934261 := by
    rw [stack];decide
  simp only [direct,merge,spill,Checked,Op.Valid,Op.apply,true_and,and_true]
  exact ⟨⟨⟨by omega,dst⟩,by exact ⟨by decide,save⟩⟩,
    ⟨⟨by omega,dst⟩,⟨by omega,dst⟩,by exact ⟨by decide,save⟩⟩,⟨room,next⟩⟩

def output (m : Model) (c : Nat) := if c%64=0 then after m (direct c) else
  let a := after m (merge c)
  if c%64<27 then a else after a (spill c)

def steps (c : Nat) := if c%64=0 then 6 else if c%64<27 then 11 else 15

theorem run (o : Oracle) (m : Model) (c : Nat) (room : cell c+1<2^33) (s : MachineState) (pc : s.pc=addr 396)
    (fits : Fits s m) (zero : m.reg .x0=0) (base : m.reg .x8=68719476336)
    (off : m.reg .x12=W (c%64)) (ptr : m.reg .x11=wordAddress (cell c)) :
    ∃ t, CommitExact.Segment o OpeningStraight.image (steps c) s t ∧ t.pc=addr 416 ∧ Fits t (output m c) := by
  have b := zero_branch o s 396 397 411 .x12 60 pc (by decide) rfl rfl rfl (W (c%64)) ((fits.registers _).trans off)
  simp only [OpeningBranch.word_zero] at b
  obtain ⟨chk₁,chk₂,_⟩ := checks m c room ptr base
  unfold steps output
  by_cases z : c%64=0
  · simp only [z,ite_true] at b ⊢
    obtain ⟨t,rt,pt,ht⟩ := OpeningStraight.block o m (direct c) 411 (by change 411+5≤1660;decide)
      (directTable c) chk₁ (s.setPC _) rfl (fits.pc _)
    exact ⟨t,CommitExact.compose b rt,pt,ht⟩
  · simp only [z,ite_false] at b ⊢
    let a := after m (merge c)
    obtain ⟨u,ru,pu,hu⟩ := OpeningStraight.block o m (merge c) 397 (by change 397+9≤1660;decide)
      (mergeTable c) chk₂ (s.setPC _) rfl (fits.pc _)
    have compare : a.reg .x13=W 27 := by change m.reg .x0+27=W 27;rw [zero];rfl
    have test := OpeningBranch.less o u .x12 .x13 406 416 40 pu (by decide) rfl rfl (c%64) 27
      (by omega) (by decide) ((hu.registers _).trans off) ((hu.registers _).trans compare)
    by_cases fitsWord : c%64<27
    · simp only [fitsWord,ite_true] at test ⊢
      exact ⟨_,CommitExact.compose (CommitExact.compose b ru) test,rfl,hu.pc _⟩
    · simp only [fitsWord,ite_false] at test ⊢
      obtain ⟨v,rv,pv,hv⟩ := OpeningStraight.block o a (spill c) 407 (by change 407+3≤1660;decide)
        (spillTable c) (checks a c room ptr base).2.2 (u.setPC _) rfl (hu.pc _)
      exact ⟨_,CommitExact.compose (CommitExact.compose (CommitExact.compose (CommitExact.compose b ru) test) rv)
        (OpeningBranch.jump o v 410 416 24 pv (by decide) rfl rfl),rfl,hv.pc _⟩

theorem memory (m : Model) (c : Nat) (zero : m.reg .x0=0) (off : m.reg .x12=W (c%64)) :
    (output m c).mem=put m.mem c 38 (m.reg .x14) := by
  have ord : (m.reg .x12).toNat%64=c%64 := by rw [off];change ((c%64)%2^64)%64=c%64;omega
  unfold output put
  by_cases align : c%64=0
  · simp [align,first];rfl
  · simp only [align,ite_false]
    have merged : (after m (merge c)).mem=writeWord m.mem (cell c) (first m.mem c (m.reg .x14)) := by
      change writeWord m.mem _ (m.mem (cell c) ||| (m.reg .x14 <<< ((m.reg .x12).toNat%64)))=_
      rw [ord,first,ite_eq_right align]
    by_cases little : c%64<27
    · rw [ite_eq_left little,ite_eq_right (by omega : ¬c%64+38>64)];exact merged
    · rw [ite_eq_right little,ite_eq_left (by omega : c%64+38>64)]
      let a := after m (merge c)
      change writeWord a.mem (cell c+1) (m.reg .x14 >>> ((((m.reg .x0).truncate 32-
        (m.reg .x12).truncate 32).signExtend 64).toNat%64))=_
      rw [show a.mem=_ from merged,zero,off]
      exact congrArg (fun n : Nat => writeWord _ (cell c+1) (m.reg .x14 >>> n))
        (negative_shift ⟨c%64,by omega⟩ (Nat.pos_of_ne_zero align))

theorem prepared (m : Model) (c : Nat) (room : c+184<2^64) (atBit : m.reg .x7=W c)
    (out : m.reg .x25=wordAddress base) :
    let a := after m prepare
    a.reg .x12=W ((c+184)%64) ∧ a.reg .x11=wordAddress (cell (c+184)) ∧ a.reg .x14=clip (m.reg .x13) := by
  have add : m.reg .x7+signExtend12 184=W (c+184) := by rw [atBit];exact (BitVec.ofNat_add ..).symm
  refine ⟨?_,?_,clipped _⟩
  · change (m.reg .x7+signExtend12 184) &&& signExtend12 63=_;rw [add,offset]
  · change (((m.reg .x7+signExtend12 184) >>> (3 : Nat)) &&& signExtend12 4088)+m.reg .x25=_
    rw [add,out,word_address _ room]

theorem prepareRun (o : Oracle) (m : Model) (s : MachineState) (pc : s.pc=addr 389) (h : Fits s m) :
    ∃ t, CommitExact.Segment o OpeningStraight.image 7 s t ∧ t.pc=addr 396 ∧ Fits t (after m prepare) :=
  OpeningStraight.block o m prepare 389 (by decide) prepareTable (by simp [prepare,Checked,Op.Valid]) s pc h

theorem frame (m : Model) (c : Nat) (r : Reg)
    (h : r≠.x9 ∧ r≠.x11 ∧ r≠.x12 ∧ r≠.x13 ∧ r≠.x16 ∧ r≠.x18) : (output m c).reg r=m.reg r := by
  obtain ⟨a,b,d,e,f,g⟩ := h
  unfold output;split
  · simp [after,direct,Op.apply,Model.set,Model.store,a.symm,b.symm,g.symm]
  · split
    · simp [after,merge,Op.apply,Model.set,Model.store,a.symm,e.symm,f.symm,g.symm]
    · simp [after,merge,spill,Op.apply,Model.set,Model.store,a.symm,d.symm,e.symm,f.symm,g.symm]

theorem saved (m : Model) (c : Nat) (bound : c/64<capacity) (zero : m.reg .x0=0) :
    (output m c).reg .x9=m.mem 8589934261 ∧ (output m c).reg .x18=64 := by
  have sep : 8589934261≠cell c := by unfold cell base capacity at *;omega
  unfold output;split
  · constructor
    · change (if 8589934261=cell c then _ else _)=_;rw [ite_eq_right sep] <;> rfl
    · change m.reg .x0+64=64;rw [zero];rfl
  · split <;> constructor
    all_goals first
      | change (if 8589934261=cell c then _ else _)=_;rw [ite_eq_right sep] <;> rfl
      | change m.reg .x0+64=64;rw [zero];rfl

end CommitGolfCandidate.Reconstruction.OpeningHeaderWrite
