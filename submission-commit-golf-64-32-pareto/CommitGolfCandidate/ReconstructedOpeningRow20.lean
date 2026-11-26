import CommitGolfCandidate.ReconstructedOpeningRowOps

namespace CommitGolfCandidate.Reconstruction.OpeningRow20
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningOps OpeningCursor OpeningPut OpeningRowData
open TwoPermutationPrototype.RV64
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000

abbrev I := OpeningRowOps.Input 1176 44
def entry (x : I) : Model := ⟨fun
  | .x0 => W 0
  | .x6 => W (atBit x.data 2)
  | .x11 => W (atBit x.data 3)
  | .x12 => x.word 1
  | .x14 => x.word 2
  | .x16 => W (off x.data)
  | .x17 => x.word 3
  | .x18 => W 64
  | .x25 => wordAddress OpeningPut.base
  | .x29 => x.word 0
  | .x30 => W (atBit x.data 1)
  | .x31 => OpeningRowData.addr x.data 0
  | r => x.initial.reg r, x.initial.mem⟩

def a746 (x : I) := withMem (entry x) (before x.data 1)
def a747 (x : I) := (a746 x).set .x13 (W (atBit x.data 1) >>> (3 : Nat))
def a748 (x : I) := (a747 x).set .x13 (OpeningRowData.addr x.data 1)
def a749 (x : I) := withMem (a748 x) (before x.data 2)
def a750 (x : I) := (a749 x).set .x12 (W (atBit x.data 2) >>> (3 : Nat))
def a751 (x : I) := (a750 x).set .x12 (OpeningRowData.addr x.data 2)
def a752 (x : I) := withMem (a751 x) (before x.data 3)
def a753 (x : I) := (a752 x).set .x11 (W (atBit x.data 3) >>> (3 : Nat))
def a754 (x : I) := (a753 x).set .x11 (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088))
def a755 (x : I) := (a754 x).set .x11 (OpeningRowData.addr x.data 3)
def a756 (x : I) := withMem (a755 x) (before x.data 4)

def codea : List Instr := [
  .SD .x31 .x29 0,
  Expr.instr .x13 (.srli .x30 3),
  Expr.instr .x13 (.add .x13 .x25),
  .SD .x13 .x12 0,
  Expr.instr .x12 (.srli .x6 3),
  Expr.instr .x12 (.add .x12 .x25),
  .SD .x12 .x14 0,
  Expr.instr .x11 (.srli .x11 3),
  Expr.instr .x11 (.andi .x11 4088),
  Expr.instr .x11 (.add .x11 .x25),
  .SD .x11 .x17 0]
theorem tablea : OpeningStraight.Listed 745 codea := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem spana (o : Oracle) (x : I) (align : off x.data=0) : Contract o codea (entry x) (a756 x) := by
  have h745 := OpeningRowData.storeAs o (entry x) .x31 .x29 0 (cell (atBit x.data 0)) (x.word 0) (before x.data 1) (by have := within x.data 0 (by decide);omega) (OpeningRowOps.current x.data 0) rfl (OpeningRowData.aligned x.data 0 align)
  have h746 := OpeningLinear.register o (a746 x) .x13 (.srli .x30 3) (W (atBit x.data 1) >>> (3 : Nat)) rfl
  have h747 := OpeningLinear.register o (a747 x) .x13 (.add .x13 .x25) (OpeningRowData.addr x.data 1) (OpeningRowOps.bare x.data 1 (by decide) align)
  have h748 := OpeningRowData.storeAs o (a748 x) .x13 .x12 0 (cell (atBit x.data 1)) (x.word 1) (before x.data 2) (by have := within x.data 1 (by decide);omega) (OpeningRowOps.current x.data 1) rfl (OpeningRowData.aligned x.data 1 align)
  have h749 := OpeningLinear.register o (a749 x) .x12 (.srli .x6 3) (W (atBit x.data 2) >>> (3 : Nat)) rfl
  have h750 := OpeningLinear.register o (a750 x) .x12 (.add .x12 .x25) (OpeningRowData.addr x.data 2) (OpeningRowOps.bare x.data 2 (by decide) align)
  have h751 := OpeningRowData.storeAs o (a751 x) .x12 .x14 0 (cell (atBit x.data 2)) (x.word 2) (before x.data 3) (by have := within x.data 2 (by decide);omega) (OpeningRowOps.current x.data 2) rfl (OpeningRowData.aligned x.data 2 align)
  have h752 := OpeningLinear.register o (a752 x) .x11 (.srli .x11 3) (W (atBit x.data 3) >>> (3 : Nat)) rfl
  have h753 := OpeningLinear.register o (a753 x) .x11 (.andi .x11 4088) (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h754 := OpeningLinear.register o (a754 x) .x11 (.add .x11 .x25) (OpeningRowData.addr x.data 3) (OpeningRowOps.pointer x.data 3 (by decide))
  have h755 := OpeningRowData.storeAs o (a755 x) .x11 .x17 0 (cell (atBit x.data 3)) (x.word 3) (before x.data 4) (by have := within x.data 3 (by decide);omega) (OpeningRowOps.current x.data 3) rfl (OpeningRowData.aligned x.data 3 align)
  exact LeafModel.combine h745 (LeafModel.combine h746 (LeafModel.combine h747 (LeafModel.combine h748 (LeafModel.combine h749 (LeafModel.combine h750 (LeafModel.combine h751 (LeafModel.combine h752 (LeafModel.combine h753 (LeafModel.combine h754 (LeafModel.combine h755 (LeafModel.empty _ _)))))))))))

def m708 (x : I) := (entry x).set .x13 (old x.data 0)
def m709 (x : I) := (m708 x).set .x5 (x.word 0 <<< off x.data)
def m710 (x : I) := (m709 x).set .x13 (merged x.data 0)
def m711 (x : I) := (m710 x).set .x5 (((0 : BitVec 32)-(W (off x.data)).truncate 32).signExtend 64)
def m712 (x : I) := (m711 x).set .x29 (high x.data 0)
def m713 (x : I) := withMem (m712 x) (tailMem x.data 0)
def m714 (x : I) := withMem (m713 x) (before x.data 1)
def m715 (x : I) := (m714 x).set .x13 (W (atBit x.data 1) >>> (3 : Nat))
def m716 (x : I) := (m715 x).set .x13 (((W (atBit x.data 1) >>> (3 : Nat)) &&& signExtend12 4088))
def m717 (x : I) := (m716 x).set .x13 (OpeningRowData.addr x.data 1)
def m718 (x : I) := (m717 x).set .x29 (old x.data 1)
def m719 (x : I) := (m718 x).set .x30 (x.word 1 <<< off x.data)
def m720 (x : I) := (m719 x).set .x29 (merged x.data 1)
def m721 (x : I) := (m720 x).set .x12 (high x.data 1)
def m722 (x : I) := withMem (m721 x) (tailMem x.data 1)
def m723 (x : I) := withMem (m722 x) (before x.data 2)
def m724 (x : I) := (m723 x).set .x12 (W (atBit x.data 2) >>> (3 : Nat))
def m725 (x : I) := (m724 x).set .x12 (((W (atBit x.data 2) >>> (3 : Nat)) &&& signExtend12 4088))
def m726 (x : I) := (m725 x).set .x12 (OpeningRowData.addr x.data 2)
def m727 (x : I) := (m726 x).set .x13 (old x.data 2)
def m728 (x : I) := (m727 x).set .x6 (x.word 2 <<< off x.data)
def m729 (x : I) := (m728 x).set .x13 (merged x.data 2)
def m730 (x : I) := (m729 x).set .x14 (high x.data 2)
def m731 (x : I) := withMem (m730 x) (tailMem x.data 2)
def m732 (x : I) := withMem (m731 x) (before x.data 3)
def m733 (x : I) := (m732 x).set .x11 (W (atBit x.data 3) >>> (3 : Nat))
def m734 (x : I) := (m733 x).set .x11 (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088))
def m735 (x : I) := (m734 x).set .x11 (OpeningRowData.addr x.data 3)
def m736 (x : I) := (m735 x).set .x12 (old x.data 3)
def m737 (x : I) := (m736 x).set .x13 (x.word 3 <<< off x.data)
def m738 (x : I) := (m737 x).set .x12 (merged x.data 3)
def m739 (x : I) := withMem (m738 x) (headMem x.data 3)
def m740 (x : I) := (m739 x).set .x12 (W 21)

def codem : List Instr := [
  .LD .x13 .x31 0,
  Expr.instr .x5 (.sll .x29 .x16),
  Expr.instr .x13 (.or .x13 .x5),
  Expr.instr .x5 (.subw .x0 .x16),
  Expr.instr .x29 (.srl .x29 .x5),
  .SD .x31 .x29 8,
  .SD .x31 .x13 0,
  Expr.instr .x13 (.srli .x30 3),
  Expr.instr .x13 (.andi .x13 4088),
  Expr.instr .x13 (.add .x13 .x25),
  .LD .x29 .x13 0,
  Expr.instr .x30 (.sll .x12 .x16),
  Expr.instr .x29 (.or .x29 .x30),
  Expr.instr .x12 (.srl .x12 .x5),
  .SD .x13 .x12 8,
  .SD .x13 .x29 0,
  Expr.instr .x12 (.srli .x6 3),
  Expr.instr .x12 (.andi .x12 4088),
  Expr.instr .x12 (.add .x12 .x25),
  .LD .x13 .x12 0,
  Expr.instr .x6 (.sll .x14 .x16),
  Expr.instr .x13 (.or .x13 .x6),
  Expr.instr .x14 (.srl .x14 .x5),
  .SD .x12 .x14 8,
  .SD .x12 .x13 0,
  Expr.instr .x11 (.srli .x11 3),
  Expr.instr .x11 (.andi .x11 4088),
  Expr.instr .x11 (.add .x11 .x25),
  .LD .x12 .x11 0,
  Expr.instr .x13 (.sll .x17 .x16),
  Expr.instr .x12 (.or .x12 .x13),
  .SD .x11 .x12 0,
  Expr.instr .x12 (.addi .x0 21)]
theorem tablem : OpeningStraight.Listed 707 codem := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem spanm (o : Oracle) (x : I) (nz : off x.data≠0) : Contract o codem (entry x) (m740 x) := by
  have h707 := OpeningLinear.read o (entry x) .x13 .x31 0 (cell (atBit x.data 0)) (old x.data 0) (by have := within x.data 0 (by decide);omega) (OpeningRowOps.current x.data 0) rfl
  have h708 := OpeningLinear.register o (m708 x) .x5 (.sll .x29 .x16) (x.word 0 <<< off x.data) (OpeningRowOps.left x.data 0)
  have h709 := OpeningLinear.register o (m709 x) .x13 (.or .x13 .x5) (merged x.data 0) rfl
  have h710 := OpeningLinear.register o (m710 x) .x5 (.subw .x0 .x16) (((0 : BitVec 32)-(W (off x.data)).truncate 32).signExtend 64) rfl
  have h711 := OpeningLinear.register o (m711 x) .x29 (.srl .x29 .x5) (high x.data 0) (OpeningRowOps.rightNeg x.data 0 nz)
  have h712 := OpeningRowData.storeAs o (m712 x) .x31 .x29 8 (cell (atBit x.data 0)+1) (high x.data 0) (tailMem x.data 0) (within x.data 0 (by decide)) (OpeningRowOps.following x.data 0) rfl rfl
  have h713 := OpeningRowData.storeAs o (m713 x) .x31 .x13 0 (cell (atBit x.data 0)) (merged x.data 0) (before x.data 1) (by have := within x.data 0 (by decide);omega) (OpeningRowOps.current x.data 0) rfl (full x.data 0 (by decide) nz)
  have h714 := OpeningLinear.register o (m714 x) .x13 (.srli .x30 3) (W (atBit x.data 1) >>> (3 : Nat)) rfl
  have h715 := OpeningLinear.register o (m715 x) .x13 (.andi .x13 4088) (((W (atBit x.data 1) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h716 := OpeningLinear.register o (m716 x) .x13 (.add .x13 .x25) (OpeningRowData.addr x.data 1) (OpeningRowOps.pointer x.data 1 (by decide))
  have h717 := OpeningLinear.read o (m717 x) .x29 .x13 0 (cell (atBit x.data 1)) (old x.data 1) (by have := within x.data 1 (by decide);omega) (OpeningRowOps.current x.data 1) rfl
  have h718 := OpeningLinear.register o (m718 x) .x30 (.sll .x12 .x16) (x.word 1 <<< off x.data) (OpeningRowOps.left x.data 1)
  have h719 := OpeningLinear.register o (m719 x) .x29 (.or .x29 .x30) (merged x.data 1) rfl
  have h720 := OpeningLinear.register o (m720 x) .x12 (.srl .x12 .x5) (high x.data 1) (OpeningRowOps.rightNeg x.data 1 nz)
  have h721 := OpeningRowData.storeAs o (m721 x) .x13 .x12 8 (cell (atBit x.data 1)+1) (high x.data 1) (tailMem x.data 1) (within x.data 1 (by decide)) (OpeningRowOps.following x.data 1) rfl rfl
  have h722 := OpeningRowData.storeAs o (m722 x) .x13 .x29 0 (cell (atBit x.data 1)) (merged x.data 1) (before x.data 2) (by have := within x.data 1 (by decide);omega) (OpeningRowOps.current x.data 1) rfl (full x.data 1 (by decide) nz)
  have h723 := OpeningLinear.register o (m723 x) .x12 (.srli .x6 3) (W (atBit x.data 2) >>> (3 : Nat)) rfl
  have h724 := OpeningLinear.register o (m724 x) .x12 (.andi .x12 4088) (((W (atBit x.data 2) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h725 := OpeningLinear.register o (m725 x) .x12 (.add .x12 .x25) (OpeningRowData.addr x.data 2) (OpeningRowOps.pointer x.data 2 (by decide))
  have h726 := OpeningLinear.read o (m726 x) .x13 .x12 0 (cell (atBit x.data 2)) (old x.data 2) (by have := within x.data 2 (by decide);omega) (OpeningRowOps.current x.data 2) rfl
  have h727 := OpeningLinear.register o (m727 x) .x6 (.sll .x14 .x16) (x.word 2 <<< off x.data) (OpeningRowOps.left x.data 2)
  have h728 := OpeningLinear.register o (m728 x) .x13 (.or .x13 .x6) (merged x.data 2) rfl
  have h729 := OpeningLinear.register o (m729 x) .x14 (.srl .x14 .x5) (high x.data 2) (OpeningRowOps.rightNeg x.data 2 nz)
  have h730 := OpeningRowData.storeAs o (m730 x) .x12 .x14 8 (cell (atBit x.data 2)+1) (high x.data 2) (tailMem x.data 2) (within x.data 2 (by decide)) (OpeningRowOps.following x.data 2) rfl rfl
  have h731 := OpeningRowData.storeAs o (m731 x) .x12 .x13 0 (cell (atBit x.data 2)) (merged x.data 2) (before x.data 3) (by have := within x.data 2 (by decide);omega) (OpeningRowOps.current x.data 2) rfl (full x.data 2 (by decide) nz)
  have h732 := OpeningLinear.register o (m732 x) .x11 (.srli .x11 3) (W (atBit x.data 3) >>> (3 : Nat)) rfl
  have h733 := OpeningLinear.register o (m733 x) .x11 (.andi .x11 4088) (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h734 := OpeningLinear.register o (m734 x) .x11 (.add .x11 .x25) (OpeningRowData.addr x.data 3) (OpeningRowOps.pointer x.data 3 (by decide))
  have h735 := OpeningLinear.read o (m735 x) .x12 .x11 0 (cell (atBit x.data 3)) (old x.data 3) (by have := within x.data 3 (by decide);omega) (OpeningRowOps.current x.data 3) rfl
  have h736 := OpeningLinear.register o (m736 x) .x13 (.sll .x17 .x16) (x.word 3 <<< off x.data) (OpeningRowOps.left x.data 3)
  have h737 := OpeningLinear.register o (m737 x) .x12 (.or .x12 .x13) (merged x.data 3) rfl
  have h738 := OpeningRowData.storeAs o (m738 x) .x11 .x12 0 (cell (atBit x.data 3)) (merged x.data 3) (headMem x.data 3) (by have := within x.data 3 (by decide);omega) (OpeningRowOps.current x.data 3) rfl rfl
  have h739 := OpeningLinear.register o (m739 x) .x12 (.addi .x0 21) (W 21) rfl
  exact LeafModel.combine h707 (LeafModel.combine h708 (LeafModel.combine h709 (LeafModel.combine h710 (LeafModel.combine h711 (LeafModel.combine h712 (LeafModel.combine h713 (LeafModel.combine h714 (LeafModel.combine h715 (LeafModel.combine h716 (LeafModel.combine h717 (LeafModel.combine h718 (LeafModel.combine h719 (LeafModel.combine h720 (LeafModel.combine h721 (LeafModel.combine h722 (LeafModel.combine h723 (LeafModel.combine h724 (LeafModel.combine h725 (LeafModel.combine h726 (LeafModel.combine h727 (LeafModel.combine h728 (LeafModel.combine h729 (LeafModel.combine h730 (LeafModel.combine h731 (LeafModel.combine h732 (LeafModel.combine h733 (LeafModel.combine h734 (LeafModel.combine h735 (LeafModel.combine h736 (LeafModel.combine h737 (LeafModel.combine h738 (LeafModel.combine h739 (LeafModel.empty _ _)))))))))))))))))))))))))))))))))

def s742 (x : I) := (m740 x).set .x12 ((64 : Word)-W (off x.data))
def s743 (x : I) := (s742 x).set .x12 (high x.data 3)
def s744 (x : I) := withMem (s743 x) (before x.data 4)

def codes : List Instr := [
  Expr.instr .x12 (.sub .x18 .x16),
  Expr.instr .x12 (.srl .x17 .x12),
  .SD .x11 .x12 8]
theorem tables : OpeningStraight.Listed 741 codes := ⟨rfl,rfl,rfl,True.intro⟩
theorem spans (o : Oracle) (x : I) (nz : off x.data≠0) (cross : 64<off x.data+x.data.bits) : Contract o codes (m740 x) (s744 x) := by
  have h741 := OpeningLinear.register o (m740 x) .x12 (.sub .x18 .x16) ((64 : Word)-W (off x.data)) rfl
  have h742 := OpeningLinear.register o (s742 x) .x12 (.srl .x17 .x12) (high x.data 3) (OpeningRowOps.rightSub x.data 3 nz)
  have h743 := OpeningRowData.storeAs o (s743 x) .x11 .x12 8 (cell (atBit x.data 3)+1) (high x.data 3) (before x.data 4) (within x.data 3 (by decide)) (OpeningRowOps.following x.data 3) rfl (crosses x.data nz cross)
  exact LeafModel.combine h741 (LeafModel.combine h742 (LeafModel.combine h743 (LeafModel.empty _ _)))


def output (x : I) := if off x.data=0 then a756 x else if off x.data<21 then m740 x else s744 x

theorem run (o : Oracle) (x : I) (u : MachineState) (pc : u.pc=CommitBlocks.addr 706) (fit : Fits u (entry x)) :
    ∃ t n, n≤64 ∧ CommitExact.Segment o OpeningStraight.image n u t ∧ t.pc=CommitBlocks.addr 756 ∧
      Fits t (output x) := by
  have zstep := zero_branch o u 706 707 745 .x16 156 pc (by decide) rfl rfl rfl
    (W (off x.data)) (fit.registers _)
  have eqv : W (off x.data)=0 ↔ off x.data=0 := OpeningBranch.word_zero _
  simp only [eqv] at zstep
  unfold output
  by_cases z : off x.data=0
  · simp only [z,ite_true] at zstep ⊢
    obtain ⟨v,rv,pv,hv⟩ := OpeningLinear.block (spana o x z) (i:=745) (by decide) tablea
      (u.setPC _) rfl (fit.pc _)
    exact ⟨v,1+codea.length,by change 12≤64;decide,CommitExact.compose zstep rv,pv,hv⟩
  · simp only [z,ite_false] at zstep ⊢
    obtain ⟨v,rv,pv,hv⟩ := OpeningLinear.block (spanm o x z) (i:=707) (by decide) tablem (u.setPC _) rfl (fit.pc _)
    have branch := OpeningBranch.less o v .x16 .x12 740 756 64 pv (by decide) rfl rfl
      (off x.data) 21 (by unfold off;omega) (by decide) (hv.registers _) (hv.registers _)
    by_cases little : off x.data<21
    · simp only [little,ite_true] at branch ⊢
      exact ⟨_,1+codem.length+1,by change 35≤64;decide,CommitExact.compose (CommitExact.compose zstep rv) branch,rfl,hv.pc _⟩
    · simp only [little,ite_false] at branch ⊢
      have cross : 64<off x.data+x.data.bits := by change 64<off x.data+44;omega
      obtain ⟨w,rw,pw,hw⟩ := OpeningLinear.block (spans o x z cross) (i:=741) (by decide) tables
        (v.setPC _) rfl (hv.pc _)
      have jump := OpeningBranch.jump o w 744 756 48 pw (by decide) rfl rfl
      exact ⟨_,1+codem.length+1+codes.length+1,by change 39≤64;decide,CommitExact.compose (CommitExact.compose (CommitExact.compose
        (CommitExact.compose zstep rv) branch) rw) jump,rfl,hw.pc _⟩

theorem memory (x : I) : (output x).mem=before x.data 4 := by
  unfold output
  split
  · rfl
  · rename_i nz;split
    · rename_i little
      exact short x.data nz (by change off x.data+44≤64;omega)
    · rfl

def changed : List Reg := [.x5,.x6,.x11,.x12,.x13,.x14,.x29,.x30]

theorem frame (x : I) (r : Reg) (h : r∉changed) : (output x).reg r=(entry x).reg r := by
  unfold output
  split
  · cases r <;> first | rfl | exact False.elim (h (by decide))
  · split <;> cases r <;> first | rfl | exact False.elim (h (by decide))

end CommitGolfCandidate.Reconstruction.OpeningRow20
