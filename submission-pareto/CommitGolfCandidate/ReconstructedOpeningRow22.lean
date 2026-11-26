import CommitGolfCandidate.ReconstructedOpeningRowOps

namespace CommitGolfCandidate.Reconstruction.OpeningRow22
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningOps OpeningCursor OpeningPut OpeningRowData
open TwoPermutationPrototype.RV64
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000

abbrev I := OpeningRowOps.Input 700 46
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

def a609 (x : I) := withMem (entry x) (before x.data 1)
def a610 (x : I) := (a609 x).set .x13 (W (atBit x.data 1) >>> (3 : Nat))
def a611 (x : I) := (a610 x).set .x13 (OpeningRowData.addr x.data 1)
def a612 (x : I) := withMem (a611 x) (before x.data 2)
def a613 (x : I) := (a612 x).set .x12 (W (atBit x.data 2) >>> (3 : Nat))
def a614 (x : I) := (a613 x).set .x12 (OpeningRowData.addr x.data 2)
def a615 (x : I) := withMem (a614 x) (before x.data 3)
def a616 (x : I) := (a615 x).set .x11 (W (atBit x.data 3) >>> (3 : Nat))
def a617 (x : I) := (a616 x).set .x11 (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088))
def a618 (x : I) := (a617 x).set .x11 (OpeningRowData.addr x.data 3)
def a619 (x : I) := withMem (a618 x) (before x.data 4)

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
theorem tablea : OpeningStraight.Listed 608 codea := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem spana (o : Oracle) (x : I) (align : off x.data=0) : Contract o codea (entry x) (a619 x) := by
  have h608 := OpeningRowData.storeAs o (entry x) .x31 .x29 0 (cell (atBit x.data 0)) (x.word 0) (before x.data 1) (by have := within x.data 0 (by decide);omega) (OpeningRowOps.current x.data 0) rfl (OpeningRowData.aligned x.data 0 align)
  have h609 := OpeningLinear.register o (a609 x) .x13 (.srli .x30 3) (W (atBit x.data 1) >>> (3 : Nat)) rfl
  have h610 := OpeningLinear.register o (a610 x) .x13 (.add .x13 .x25) (OpeningRowData.addr x.data 1) (OpeningRowOps.bare x.data 1 (by decide) align)
  have h611 := OpeningRowData.storeAs o (a611 x) .x13 .x12 0 (cell (atBit x.data 1)) (x.word 1) (before x.data 2) (by have := within x.data 1 (by decide);omega) (OpeningRowOps.current x.data 1) rfl (OpeningRowData.aligned x.data 1 align)
  have h612 := OpeningLinear.register o (a612 x) .x12 (.srli .x6 3) (W (atBit x.data 2) >>> (3 : Nat)) rfl
  have h613 := OpeningLinear.register o (a613 x) .x12 (.add .x12 .x25) (OpeningRowData.addr x.data 2) (OpeningRowOps.bare x.data 2 (by decide) align)
  have h614 := OpeningRowData.storeAs o (a614 x) .x12 .x14 0 (cell (atBit x.data 2)) (x.word 2) (before x.data 3) (by have := within x.data 2 (by decide);omega) (OpeningRowOps.current x.data 2) rfl (OpeningRowData.aligned x.data 2 align)
  have h615 := OpeningLinear.register o (a615 x) .x11 (.srli .x11 3) (W (atBit x.data 3) >>> (3 : Nat)) rfl
  have h616 := OpeningLinear.register o (a616 x) .x11 (.andi .x11 4088) (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h617 := OpeningLinear.register o (a617 x) .x11 (.add .x11 .x25) (OpeningRowData.addr x.data 3) (OpeningRowOps.pointer x.data 3 (by decide))
  have h618 := OpeningRowData.storeAs o (a618 x) .x11 .x17 0 (cell (atBit x.data 3)) (x.word 3) (before x.data 4) (by have := within x.data 3 (by decide);omega) (OpeningRowOps.current x.data 3) rfl (OpeningRowData.aligned x.data 3 align)
  exact LeafModel.combine h608 (LeafModel.combine h609 (LeafModel.combine h610 (LeafModel.combine h611 (LeafModel.combine h612 (LeafModel.combine h613 (LeafModel.combine h614 (LeafModel.combine h615 (LeafModel.combine h616 (LeafModel.combine h617 (LeafModel.combine h618 (LeafModel.empty _ _)))))))))))

def m571 (x : I) := (entry x).set .x13 (old x.data 0)
def m572 (x : I) := (m571 x).set .x5 (x.word 0 <<< off x.data)
def m573 (x : I) := (m572 x).set .x13 (merged x.data 0)
def m574 (x : I) := (m573 x).set .x5 (((0 : BitVec 32)-(W (off x.data)).truncate 32).signExtend 64)
def m575 (x : I) := (m574 x).set .x29 (high x.data 0)
def m576 (x : I) := withMem (m575 x) (tailMem x.data 0)
def m577 (x : I) := withMem (m576 x) (before x.data 1)
def m578 (x : I) := (m577 x).set .x13 (W (atBit x.data 1) >>> (3 : Nat))
def m579 (x : I) := (m578 x).set .x13 (((W (atBit x.data 1) >>> (3 : Nat)) &&& signExtend12 4088))
def m580 (x : I) := (m579 x).set .x13 (OpeningRowData.addr x.data 1)
def m581 (x : I) := (m580 x).set .x29 (old x.data 1)
def m582 (x : I) := (m581 x).set .x30 (x.word 1 <<< off x.data)
def m583 (x : I) := (m582 x).set .x29 (merged x.data 1)
def m584 (x : I) := (m583 x).set .x12 (high x.data 1)
def m585 (x : I) := withMem (m584 x) (tailMem x.data 1)
def m586 (x : I) := withMem (m585 x) (before x.data 2)
def m587 (x : I) := (m586 x).set .x12 (W (atBit x.data 2) >>> (3 : Nat))
def m588 (x : I) := (m587 x).set .x12 (((W (atBit x.data 2) >>> (3 : Nat)) &&& signExtend12 4088))
def m589 (x : I) := (m588 x).set .x12 (OpeningRowData.addr x.data 2)
def m590 (x : I) := (m589 x).set .x13 (old x.data 2)
def m591 (x : I) := (m590 x).set .x6 (x.word 2 <<< off x.data)
def m592 (x : I) := (m591 x).set .x13 (merged x.data 2)
def m593 (x : I) := (m592 x).set .x14 (high x.data 2)
def m594 (x : I) := withMem (m593 x) (tailMem x.data 2)
def m595 (x : I) := withMem (m594 x) (before x.data 3)
def m596 (x : I) := (m595 x).set .x11 (W (atBit x.data 3) >>> (3 : Nat))
def m597 (x : I) := (m596 x).set .x11 (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088))
def m598 (x : I) := (m597 x).set .x11 (OpeningRowData.addr x.data 3)
def m599 (x : I) := (m598 x).set .x12 (old x.data 3)
def m600 (x : I) := (m599 x).set .x13 (x.word 3 <<< off x.data)
def m601 (x : I) := (m600 x).set .x12 (merged x.data 3)
def m602 (x : I) := withMem (m601 x) (headMem x.data 3)
def m603 (x : I) := (m602 x).set .x12 (W 19)

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
theorem tablem : OpeningStraight.Listed 570 codem := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem spanm (o : Oracle) (x : I) (nz : off x.data≠0) : Contract o codem (entry x) (m603 x) := by
  have h570 := OpeningLinear.read o (entry x) .x13 .x31 0 (cell (atBit x.data 0)) (old x.data 0) (by have := within x.data 0 (by decide);omega) (OpeningRowOps.current x.data 0) rfl
  have h571 := OpeningLinear.register o (m571 x) .x5 (.sll .x29 .x16) (x.word 0 <<< off x.data) (OpeningRowOps.left x.data 0)
  have h572 := OpeningLinear.register o (m572 x) .x13 (.or .x13 .x5) (merged x.data 0) rfl
  have h573 := OpeningLinear.register o (m573 x) .x5 (.subw .x0 .x16) (((0 : BitVec 32)-(W (off x.data)).truncate 32).signExtend 64) rfl
  have h574 := OpeningLinear.register o (m574 x) .x29 (.srl .x29 .x5) (high x.data 0) (OpeningRowOps.rightNeg x.data 0 nz)
  have h575 := OpeningRowData.storeAs o (m575 x) .x31 .x29 8 (cell (atBit x.data 0)+1) (high x.data 0) (tailMem x.data 0) (within x.data 0 (by decide)) (OpeningRowOps.following x.data 0) rfl rfl
  have h576 := OpeningRowData.storeAs o (m576 x) .x31 .x13 0 (cell (atBit x.data 0)) (merged x.data 0) (before x.data 1) (by have := within x.data 0 (by decide);omega) (OpeningRowOps.current x.data 0) rfl (full x.data 0 (by decide) nz)
  have h577 := OpeningLinear.register o (m577 x) .x13 (.srli .x30 3) (W (atBit x.data 1) >>> (3 : Nat)) rfl
  have h578 := OpeningLinear.register o (m578 x) .x13 (.andi .x13 4088) (((W (atBit x.data 1) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h579 := OpeningLinear.register o (m579 x) .x13 (.add .x13 .x25) (OpeningRowData.addr x.data 1) (OpeningRowOps.pointer x.data 1 (by decide))
  have h580 := OpeningLinear.read o (m580 x) .x29 .x13 0 (cell (atBit x.data 1)) (old x.data 1) (by have := within x.data 1 (by decide);omega) (OpeningRowOps.current x.data 1) rfl
  have h581 := OpeningLinear.register o (m581 x) .x30 (.sll .x12 .x16) (x.word 1 <<< off x.data) (OpeningRowOps.left x.data 1)
  have h582 := OpeningLinear.register o (m582 x) .x29 (.or .x29 .x30) (merged x.data 1) rfl
  have h583 := OpeningLinear.register o (m583 x) .x12 (.srl .x12 .x5) (high x.data 1) (OpeningRowOps.rightNeg x.data 1 nz)
  have h584 := OpeningRowData.storeAs o (m584 x) .x13 .x12 8 (cell (atBit x.data 1)+1) (high x.data 1) (tailMem x.data 1) (within x.data 1 (by decide)) (OpeningRowOps.following x.data 1) rfl rfl
  have h585 := OpeningRowData.storeAs o (m585 x) .x13 .x29 0 (cell (atBit x.data 1)) (merged x.data 1) (before x.data 2) (by have := within x.data 1 (by decide);omega) (OpeningRowOps.current x.data 1) rfl (full x.data 1 (by decide) nz)
  have h586 := OpeningLinear.register o (m586 x) .x12 (.srli .x6 3) (W (atBit x.data 2) >>> (3 : Nat)) rfl
  have h587 := OpeningLinear.register o (m587 x) .x12 (.andi .x12 4088) (((W (atBit x.data 2) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h588 := OpeningLinear.register o (m588 x) .x12 (.add .x12 .x25) (OpeningRowData.addr x.data 2) (OpeningRowOps.pointer x.data 2 (by decide))
  have h589 := OpeningLinear.read o (m589 x) .x13 .x12 0 (cell (atBit x.data 2)) (old x.data 2) (by have := within x.data 2 (by decide);omega) (OpeningRowOps.current x.data 2) rfl
  have h590 := OpeningLinear.register o (m590 x) .x6 (.sll .x14 .x16) (x.word 2 <<< off x.data) (OpeningRowOps.left x.data 2)
  have h591 := OpeningLinear.register o (m591 x) .x13 (.or .x13 .x6) (merged x.data 2) rfl
  have h592 := OpeningLinear.register o (m592 x) .x14 (.srl .x14 .x5) (high x.data 2) (OpeningRowOps.rightNeg x.data 2 nz)
  have h593 := OpeningRowData.storeAs o (m593 x) .x12 .x14 8 (cell (atBit x.data 2)+1) (high x.data 2) (tailMem x.data 2) (within x.data 2 (by decide)) (OpeningRowOps.following x.data 2) rfl rfl
  have h594 := OpeningRowData.storeAs o (m594 x) .x12 .x13 0 (cell (atBit x.data 2)) (merged x.data 2) (before x.data 3) (by have := within x.data 2 (by decide);omega) (OpeningRowOps.current x.data 2) rfl (full x.data 2 (by decide) nz)
  have h595 := OpeningLinear.register o (m595 x) .x11 (.srli .x11 3) (W (atBit x.data 3) >>> (3 : Nat)) rfl
  have h596 := OpeningLinear.register o (m596 x) .x11 (.andi .x11 4088) (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h597 := OpeningLinear.register o (m597 x) .x11 (.add .x11 .x25) (OpeningRowData.addr x.data 3) (OpeningRowOps.pointer x.data 3 (by decide))
  have h598 := OpeningLinear.read o (m598 x) .x12 .x11 0 (cell (atBit x.data 3)) (old x.data 3) (by have := within x.data 3 (by decide);omega) (OpeningRowOps.current x.data 3) rfl
  have h599 := OpeningLinear.register o (m599 x) .x13 (.sll .x17 .x16) (x.word 3 <<< off x.data) (OpeningRowOps.left x.data 3)
  have h600 := OpeningLinear.register o (m600 x) .x12 (.or .x12 .x13) (merged x.data 3) rfl
  have h601 := OpeningRowData.storeAs o (m601 x) .x11 .x12 0 (cell (atBit x.data 3)) (merged x.data 3) (headMem x.data 3) (by have := within x.data 3 (by decide);omega) (OpeningRowOps.current x.data 3) rfl rfl
  have h602 := OpeningLinear.register o (m602 x) .x12 (.addi .x0 19) (W 19) rfl
  exact LeafModel.combine h570 (LeafModel.combine h571 (LeafModel.combine h572 (LeafModel.combine h573 (LeafModel.combine h574 (LeafModel.combine h575 (LeafModel.combine h576 (LeafModel.combine h577 (LeafModel.combine h578 (LeafModel.combine h579 (LeafModel.combine h580 (LeafModel.combine h581 (LeafModel.combine h582 (LeafModel.combine h583 (LeafModel.combine h584 (LeafModel.combine h585 (LeafModel.combine h586 (LeafModel.combine h587 (LeafModel.combine h588 (LeafModel.combine h589 (LeafModel.combine h590 (LeafModel.combine h591 (LeafModel.combine h592 (LeafModel.combine h593 (LeafModel.combine h594 (LeafModel.combine h595 (LeafModel.combine h596 (LeafModel.combine h597 (LeafModel.combine h598 (LeafModel.combine h599 (LeafModel.combine h600 (LeafModel.combine h601 (LeafModel.combine h602 (LeafModel.empty _ _)))))))))))))))))))))))))))))))))

def s605 (x : I) := (m603 x).set .x12 ((64 : Word)-W (off x.data))
def s606 (x : I) := (s605 x).set .x12 (high x.data 3)
def s607 (x : I) := withMem (s606 x) (before x.data 4)

def codes : List Instr := [
  Expr.instr .x12 (.sub .x18 .x16),
  Expr.instr .x12 (.srl .x17 .x12),
  .SD .x11 .x12 8]
theorem tables : OpeningStraight.Listed 604 codes := ⟨rfl,rfl,rfl,True.intro⟩
theorem spans (o : Oracle) (x : I) (nz : off x.data≠0) (cross : 64<off x.data+x.data.bits) : Contract o codes (m603 x) (s607 x) := by
  have h604 := OpeningLinear.register o (m603 x) .x12 (.sub .x18 .x16) ((64 : Word)-W (off x.data)) rfl
  have h605 := OpeningLinear.register o (s605 x) .x12 (.srl .x17 .x12) (high x.data 3) (OpeningRowOps.rightSub x.data 3 nz)
  have h606 := OpeningRowData.storeAs o (s606 x) .x11 .x12 8 (cell (atBit x.data 3)+1) (high x.data 3) (before x.data 4) (within x.data 3 (by decide)) (OpeningRowOps.following x.data 3) rfl (crosses x.data nz cross)
  exact LeafModel.combine h604 (LeafModel.combine h605 (LeafModel.combine h606 (LeafModel.empty _ _)))


def output (x : I) := if off x.data=0 then a619 x else if off x.data<19 then m603 x else s607 x

theorem run (o : Oracle) (x : I) (u : MachineState) (pc : u.pc=CommitBlocks.addr 569) (fit : Fits u (entry x)) :
    ∃ t n, n≤64 ∧ CommitExact.Segment o OpeningStraight.image n u t ∧ t.pc=CommitBlocks.addr 619 ∧
      Fits t (output x) := by
  have zstep := zero_branch o u 569 570 608 .x16 156 pc (by decide) rfl rfl rfl
    (W (off x.data)) (fit.registers _)
  have eqv : W (off x.data)=0 ↔ off x.data=0 := OpeningBranch.word_zero _
  simp only [eqv] at zstep
  unfold output
  by_cases z : off x.data=0
  · simp only [z,ite_true] at zstep ⊢
    obtain ⟨v,rv,pv,hv⟩ := OpeningLinear.block (spana o x z) (i:=608) (by decide) tablea
      (u.setPC _) rfl (fit.pc _)
    exact ⟨v,1+codea.length,by change 12≤64;decide,CommitExact.compose zstep rv,pv,hv⟩
  · simp only [z,ite_false] at zstep ⊢
    obtain ⟨v,rv,pv,hv⟩ := OpeningLinear.block (spanm o x z) (i:=570) (by decide) tablem (u.setPC _) rfl (fit.pc _)
    have branch := OpeningBranch.less o v .x16 .x12 603 619 64 pv (by decide) rfl rfl
      (off x.data) 19 (by unfold off;omega) (by decide) (hv.registers _) (hv.registers _)
    by_cases little : off x.data<19
    · simp only [little,ite_true] at branch ⊢
      exact ⟨_,1+codem.length+1,by change 35≤64;decide,CommitExact.compose (CommitExact.compose zstep rv) branch,rfl,hv.pc _⟩
    · simp only [little,ite_false] at branch ⊢
      have cross : 64<off x.data+x.data.bits := by change 64<off x.data+46;omega
      obtain ⟨w,rw,pw,hw⟩ := OpeningLinear.block (spans o x z cross) (i:=604) (by decide) tables
        (v.setPC _) rfl (hv.pc _)
      have jump := OpeningBranch.jump o w 607 619 48 pw (by decide) rfl rfl
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

end CommitGolfCandidate.Reconstruction.OpeningRow22
