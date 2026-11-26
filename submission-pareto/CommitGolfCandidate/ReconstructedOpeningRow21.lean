import CommitGolfCandidate.ReconstructedOpeningRowOps

namespace CommitGolfCandidate.Reconstruction.OpeningRow21
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningOps OpeningCursor OpeningPut OpeningRowData
open TwoPermutationPrototype.RV64
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000

abbrev I := OpeningRowOps.Input 938 46
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

def a676 (x : I) := withMem (entry x) (before x.data 1)
def a677 (x : I) := (a676 x).set .x13 (W (atBit x.data 1) >>> (3 : Nat))
def a678 (x : I) := (a677 x).set .x13 (OpeningRowData.addr x.data 1)
def a679 (x : I) := withMem (a678 x) (before x.data 2)
def a680 (x : I) := (a679 x).set .x12 (W (atBit x.data 2) >>> (3 : Nat))
def a681 (x : I) := (a680 x).set .x12 (OpeningRowData.addr x.data 2)
def a682 (x : I) := withMem (a681 x) (before x.data 3)
def a683 (x : I) := (a682 x).set .x11 (W (atBit x.data 3) >>> (3 : Nat))
def a684 (x : I) := (a683 x).set .x11 (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088))
def a685 (x : I) := (a684 x).set .x11 (OpeningRowData.addr x.data 3)
def a686 (x : I) := withMem (a685 x) (before x.data 4)

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
theorem tablea : OpeningStraight.Listed 675 codea := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem spana (o : Oracle) (x : I) (align : off x.data=0) : Contract o codea (entry x) (a686 x) := by
  have h675 := OpeningRowData.storeAs o (entry x) .x31 .x29 0 (cell (atBit x.data 0)) (x.word 0) (before x.data 1) (by have := within x.data 0 (by decide);omega) (OpeningRowOps.current x.data 0) rfl (OpeningRowData.aligned x.data 0 align)
  have h676 := OpeningLinear.register o (a676 x) .x13 (.srli .x30 3) (W (atBit x.data 1) >>> (3 : Nat)) rfl
  have h677 := OpeningLinear.register o (a677 x) .x13 (.add .x13 .x25) (OpeningRowData.addr x.data 1) (OpeningRowOps.bare x.data 1 (by decide) align)
  have h678 := OpeningRowData.storeAs o (a678 x) .x13 .x12 0 (cell (atBit x.data 1)) (x.word 1) (before x.data 2) (by have := within x.data 1 (by decide);omega) (OpeningRowOps.current x.data 1) rfl (OpeningRowData.aligned x.data 1 align)
  have h679 := OpeningLinear.register o (a679 x) .x12 (.srli .x6 3) (W (atBit x.data 2) >>> (3 : Nat)) rfl
  have h680 := OpeningLinear.register o (a680 x) .x12 (.add .x12 .x25) (OpeningRowData.addr x.data 2) (OpeningRowOps.bare x.data 2 (by decide) align)
  have h681 := OpeningRowData.storeAs o (a681 x) .x12 .x14 0 (cell (atBit x.data 2)) (x.word 2) (before x.data 3) (by have := within x.data 2 (by decide);omega) (OpeningRowOps.current x.data 2) rfl (OpeningRowData.aligned x.data 2 align)
  have h682 := OpeningLinear.register o (a682 x) .x11 (.srli .x11 3) (W (atBit x.data 3) >>> (3 : Nat)) rfl
  have h683 := OpeningLinear.register o (a683 x) .x11 (.andi .x11 4088) (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h684 := OpeningLinear.register o (a684 x) .x11 (.add .x11 .x25) (OpeningRowData.addr x.data 3) (OpeningRowOps.pointer x.data 3 (by decide))
  have h685 := OpeningRowData.storeAs o (a685 x) .x11 .x17 0 (cell (atBit x.data 3)) (x.word 3) (before x.data 4) (by have := within x.data 3 (by decide);omega) (OpeningRowOps.current x.data 3) rfl (OpeningRowData.aligned x.data 3 align)
  exact LeafModel.combine h675 (LeafModel.combine h676 (LeafModel.combine h677 (LeafModel.combine h678 (LeafModel.combine h679 (LeafModel.combine h680 (LeafModel.combine h681 (LeafModel.combine h682 (LeafModel.combine h683 (LeafModel.combine h684 (LeafModel.combine h685 (LeafModel.empty _ _)))))))))))

def m638 (x : I) := (entry x).set .x13 (old x.data 0)
def m639 (x : I) := (m638 x).set .x5 (x.word 0 <<< off x.data)
def m640 (x : I) := (m639 x).set .x13 (merged x.data 0)
def m641 (x : I) := (m640 x).set .x5 (((0 : BitVec 32)-(W (off x.data)).truncate 32).signExtend 64)
def m642 (x : I) := (m641 x).set .x29 (high x.data 0)
def m643 (x : I) := withMem (m642 x) (tailMem x.data 0)
def m644 (x : I) := withMem (m643 x) (before x.data 1)
def m645 (x : I) := (m644 x).set .x13 (W (atBit x.data 1) >>> (3 : Nat))
def m646 (x : I) := (m645 x).set .x13 (((W (atBit x.data 1) >>> (3 : Nat)) &&& signExtend12 4088))
def m647 (x : I) := (m646 x).set .x13 (OpeningRowData.addr x.data 1)
def m648 (x : I) := (m647 x).set .x29 (old x.data 1)
def m649 (x : I) := (m648 x).set .x30 (x.word 1 <<< off x.data)
def m650 (x : I) := (m649 x).set .x29 (merged x.data 1)
def m651 (x : I) := (m650 x).set .x12 (high x.data 1)
def m652 (x : I) := withMem (m651 x) (tailMem x.data 1)
def m653 (x : I) := withMem (m652 x) (before x.data 2)
def m654 (x : I) := (m653 x).set .x12 (W (atBit x.data 2) >>> (3 : Nat))
def m655 (x : I) := (m654 x).set .x12 (((W (atBit x.data 2) >>> (3 : Nat)) &&& signExtend12 4088))
def m656 (x : I) := (m655 x).set .x12 (OpeningRowData.addr x.data 2)
def m657 (x : I) := (m656 x).set .x13 (old x.data 2)
def m658 (x : I) := (m657 x).set .x6 (x.word 2 <<< off x.data)
def m659 (x : I) := (m658 x).set .x13 (merged x.data 2)
def m660 (x : I) := (m659 x).set .x14 (high x.data 2)
def m661 (x : I) := withMem (m660 x) (tailMem x.data 2)
def m662 (x : I) := withMem (m661 x) (before x.data 3)
def m663 (x : I) := (m662 x).set .x11 (W (atBit x.data 3) >>> (3 : Nat))
def m664 (x : I) := (m663 x).set .x11 (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088))
def m665 (x : I) := (m664 x).set .x11 (OpeningRowData.addr x.data 3)
def m666 (x : I) := (m665 x).set .x12 (old x.data 3)
def m667 (x : I) := (m666 x).set .x13 (x.word 3 <<< off x.data)
def m668 (x : I) := (m667 x).set .x12 (merged x.data 3)
def m669 (x : I) := withMem (m668 x) (headMem x.data 3)
def m670 (x : I) := (m669 x).set .x12 (W 19)

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
  Expr.instr .x12 (.addi .x0 19)]
theorem tablem : OpeningStraight.Listed 637 codem := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem spanm (o : Oracle) (x : I) (nz : off x.data≠0) : Contract o codem (entry x) (m670 x) := by
  have h637 := OpeningLinear.read o (entry x) .x13 .x31 0 (cell (atBit x.data 0)) (old x.data 0) (by have := within x.data 0 (by decide);omega) (OpeningRowOps.current x.data 0) rfl
  have h638 := OpeningLinear.register o (m638 x) .x5 (.sll .x29 .x16) (x.word 0 <<< off x.data) (OpeningRowOps.left x.data 0)
  have h639 := OpeningLinear.register o (m639 x) .x13 (.or .x13 .x5) (merged x.data 0) rfl
  have h640 := OpeningLinear.register o (m640 x) .x5 (.subw .x0 .x16) (((0 : BitVec 32)-(W (off x.data)).truncate 32).signExtend 64) rfl
  have h641 := OpeningLinear.register o (m641 x) .x29 (.srl .x29 .x5) (high x.data 0) (OpeningRowOps.rightNeg x.data 0 nz)
  have h642 := OpeningRowData.storeAs o (m642 x) .x31 .x29 8 (cell (atBit x.data 0)+1) (high x.data 0) (tailMem x.data 0) (within x.data 0 (by decide)) (OpeningRowOps.following x.data 0) rfl rfl
  have h643 := OpeningRowData.storeAs o (m643 x) .x31 .x13 0 (cell (atBit x.data 0)) (merged x.data 0) (before x.data 1) (by have := within x.data 0 (by decide);omega) (OpeningRowOps.current x.data 0) rfl (full x.data 0 (by decide) nz)
  have h644 := OpeningLinear.register o (m644 x) .x13 (.srli .x30 3) (W (atBit x.data 1) >>> (3 : Nat)) rfl
  have h645 := OpeningLinear.register o (m645 x) .x13 (.andi .x13 4088) (((W (atBit x.data 1) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h646 := OpeningLinear.register o (m646 x) .x13 (.add .x13 .x25) (OpeningRowData.addr x.data 1) (OpeningRowOps.pointer x.data 1 (by decide))
  have h647 := OpeningLinear.read o (m647 x) .x29 .x13 0 (cell (atBit x.data 1)) (old x.data 1) (by have := within x.data 1 (by decide);omega) (OpeningRowOps.current x.data 1) rfl
  have h648 := OpeningLinear.register o (m648 x) .x30 (.sll .x12 .x16) (x.word 1 <<< off x.data) (OpeningRowOps.left x.data 1)
  have h649 := OpeningLinear.register o (m649 x) .x29 (.or .x29 .x30) (merged x.data 1) rfl
  have h650 := OpeningLinear.register o (m650 x) .x12 (.srl .x12 .x5) (high x.data 1) (OpeningRowOps.rightNeg x.data 1 nz)
  have h651 := OpeningRowData.storeAs o (m651 x) .x13 .x12 8 (cell (atBit x.data 1)+1) (high x.data 1) (tailMem x.data 1) (within x.data 1 (by decide)) (OpeningRowOps.following x.data 1) rfl rfl
  have h652 := OpeningRowData.storeAs o (m652 x) .x13 .x29 0 (cell (atBit x.data 1)) (merged x.data 1) (before x.data 2) (by have := within x.data 1 (by decide);omega) (OpeningRowOps.current x.data 1) rfl (full x.data 1 (by decide) nz)
  have h653 := OpeningLinear.register o (m653 x) .x12 (.srli .x6 3) (W (atBit x.data 2) >>> (3 : Nat)) rfl
  have h654 := OpeningLinear.register o (m654 x) .x12 (.andi .x12 4088) (((W (atBit x.data 2) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h655 := OpeningLinear.register o (m655 x) .x12 (.add .x12 .x25) (OpeningRowData.addr x.data 2) (OpeningRowOps.pointer x.data 2 (by decide))
  have h656 := OpeningLinear.read o (m656 x) .x13 .x12 0 (cell (atBit x.data 2)) (old x.data 2) (by have := within x.data 2 (by decide);omega) (OpeningRowOps.current x.data 2) rfl
  have h657 := OpeningLinear.register o (m657 x) .x6 (.sll .x14 .x16) (x.word 2 <<< off x.data) (OpeningRowOps.left x.data 2)
  have h658 := OpeningLinear.register o (m658 x) .x13 (.or .x13 .x6) (merged x.data 2) rfl
  have h659 := OpeningLinear.register o (m659 x) .x14 (.srl .x14 .x5) (high x.data 2) (OpeningRowOps.rightNeg x.data 2 nz)
  have h660 := OpeningRowData.storeAs o (m660 x) .x12 .x14 8 (cell (atBit x.data 2)+1) (high x.data 2) (tailMem x.data 2) (within x.data 2 (by decide)) (OpeningRowOps.following x.data 2) rfl rfl
  have h661 := OpeningRowData.storeAs o (m661 x) .x12 .x13 0 (cell (atBit x.data 2)) (merged x.data 2) (before x.data 3) (by have := within x.data 2 (by decide);omega) (OpeningRowOps.current x.data 2) rfl (full x.data 2 (by decide) nz)
  have h662 := OpeningLinear.register o (m662 x) .x11 (.srli .x11 3) (W (atBit x.data 3) >>> (3 : Nat)) rfl
  have h663 := OpeningLinear.register o (m663 x) .x11 (.andi .x11 4088) (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h664 := OpeningLinear.register o (m664 x) .x11 (.add .x11 .x25) (OpeningRowData.addr x.data 3) (OpeningRowOps.pointer x.data 3 (by decide))
  have h665 := OpeningLinear.read o (m665 x) .x12 .x11 0 (cell (atBit x.data 3)) (old x.data 3) (by have := within x.data 3 (by decide);omega) (OpeningRowOps.current x.data 3) rfl
  have h666 := OpeningLinear.register o (m666 x) .x13 (.sll .x17 .x16) (x.word 3 <<< off x.data) (OpeningRowOps.left x.data 3)
  have h667 := OpeningLinear.register o (m667 x) .x12 (.or .x12 .x13) (merged x.data 3) rfl
  have h668 := OpeningRowData.storeAs o (m668 x) .x11 .x12 0 (cell (atBit x.data 3)) (merged x.data 3) (headMem x.data 3) (by have := within x.data 3 (by decide);omega) (OpeningRowOps.current x.data 3) rfl rfl
  have h669 := OpeningLinear.register o (m669 x) .x12 (.addi .x0 19) (W 19) rfl
  exact LeafModel.combine h637 (LeafModel.combine h638 (LeafModel.combine h639 (LeafModel.combine h640 (LeafModel.combine h641 (LeafModel.combine h642 (LeafModel.combine h643 (LeafModel.combine h644 (LeafModel.combine h645 (LeafModel.combine h646 (LeafModel.combine h647 (LeafModel.combine h648 (LeafModel.combine h649 (LeafModel.combine h650 (LeafModel.combine h651 (LeafModel.combine h652 (LeafModel.combine h653 (LeafModel.combine h654 (LeafModel.combine h655 (LeafModel.combine h656 (LeafModel.combine h657 (LeafModel.combine h658 (LeafModel.combine h659 (LeafModel.combine h660 (LeafModel.combine h661 (LeafModel.combine h662 (LeafModel.combine h663 (LeafModel.combine h664 (LeafModel.combine h665 (LeafModel.combine h666 (LeafModel.combine h667 (LeafModel.combine h668 (LeafModel.combine h669 (LeafModel.empty _ _)))))))))))))))))))))))))))))))))

def s672 (x : I) := (m670 x).set .x12 ((64 : Word)-W (off x.data))
def s673 (x : I) := (s672 x).set .x12 (high x.data 3)
def s674 (x : I) := withMem (s673 x) (before x.data 4)

def codes : List Instr := [
  Expr.instr .x12 (.sub .x18 .x16),
  Expr.instr .x12 (.srl .x17 .x12),
  .SD .x11 .x12 8]
theorem tables : OpeningStraight.Listed 671 codes := ⟨rfl,rfl,rfl,True.intro⟩
theorem spans (o : Oracle) (x : I) (nz : off x.data≠0) (cross : 64<off x.data+x.data.bits) : Contract o codes (m670 x) (s674 x) := by
  have h671 := OpeningLinear.register o (m670 x) .x12 (.sub .x18 .x16) ((64 : Word)-W (off x.data)) rfl
  have h672 := OpeningLinear.register o (s672 x) .x12 (.srl .x17 .x12) (high x.data 3) (OpeningRowOps.rightSub x.data 3 nz)
  have h673 := OpeningRowData.storeAs o (s673 x) .x11 .x12 8 (cell (atBit x.data 3)+1) (high x.data 3) (before x.data 4) (within x.data 3 (by decide)) (OpeningRowOps.following x.data 3) rfl (crosses x.data nz cross)
  exact LeafModel.combine h671 (LeafModel.combine h672 (LeafModel.combine h673 (LeafModel.empty _ _)))


def output (x : I) := if off x.data=0 then a686 x else if off x.data<19 then m670 x else s674 x

theorem run (o : Oracle) (x : I) (u : MachineState) (pc : u.pc=CommitBlocks.addr 636) (fit : Fits u (entry x)) :
    ∃ t n, n≤64 ∧ CommitExact.Segment o OpeningStraight.image n u t ∧ t.pc=CommitBlocks.addr 686 ∧
      Fits t (output x) := by
  have zstep := zero_branch o u 636 637 675 .x16 156 pc (by decide) rfl rfl rfl
    (W (off x.data)) (fit.registers _)
  have eqv : W (off x.data)=0 ↔ off x.data=0 := OpeningBranch.word_zero _
  simp only [eqv] at zstep
  unfold output
  by_cases z : off x.data=0
  · simp only [z,ite_true] at zstep ⊢
    obtain ⟨v,rv,pv,hv⟩ := OpeningLinear.block (spana o x z) (i:=675) (by decide) tablea
      (u.setPC _) rfl (fit.pc _)
    exact ⟨v,1+codea.length,by change 12≤64;decide,CommitExact.compose zstep rv,pv,hv⟩
  · simp only [z,ite_false] at zstep ⊢
    obtain ⟨v,rv,pv,hv⟩ := OpeningLinear.block (spanm o x z) (i:=637) (by decide) tablem (u.setPC _) rfl (fit.pc _)
    have branch := OpeningBranch.less o v .x16 .x12 670 686 64 pv (by decide) rfl rfl
      (off x.data) 19 (by unfold off;omega) (by decide) (hv.registers _) (hv.registers _)
    by_cases little : off x.data<19
    · simp only [little,ite_true] at branch ⊢
      exact ⟨_,1+codem.length+1,by change 35≤64;decide,CommitExact.compose (CommitExact.compose zstep rv) branch,rfl,hv.pc _⟩
    · simp only [little,ite_false] at branch ⊢
      have cross : 64<off x.data+x.data.bits := by change 64<off x.data+46;omega
      obtain ⟨w,rw,pw,hw⟩ := OpeningLinear.block (spans o x z cross) (i:=671) (by decide) tables
        (v.setPC _) rfl (hv.pc _)
      have jump := OpeningBranch.jump o w 674 686 48 pw (by decide) rfl rfl
      exact ⟨_,1+codem.length+1+codes.length+1,by change 39≤64;decide,CommitExact.compose (CommitExact.compose (CommitExact.compose
        (CommitExact.compose zstep rv) branch) rw) jump,rfl,hw.pc _⟩

theorem memory (x : I) : (output x).mem=before x.data 4 := by
  unfold output
  split
  · rfl
  · rename_i nz;split
    · rename_i little
      exact short x.data nz (by change off x.data+46≤64;omega)
    · rfl

def changed : List Reg := [.x5,.x6,.x11,.x12,.x13,.x14,.x29,.x30]

theorem frame (x : I) (r : Reg) (h : r∉changed) : (output x).reg r=(entry x).reg r := by
  unfold output
  split
  · cases r <;> first | rfl | exact False.elim (h (by decide))
  · split <;> cases r <;> first | rfl | exact False.elim (h (by decide))

end CommitGolfCandidate.Reconstruction.OpeningRow21
