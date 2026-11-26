import CommitGolfCandidate.ReconstructedOpeningRowOps

namespace CommitGolfCandidate.Reconstruction.OpeningRow19
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningOps OpeningCursor OpeningPut OpeningRowData
open TwoPermutationPrototype.RV64
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000

abbrev I := OpeningRowOps.Input 1412 32
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
  | .x28 => W (atBit x.data 1)
  | .x29 => x.word 0
  | .x30 => OpeningRowData.addr x.data 0
  | r => x.initial.reg r, x.initial.mem⟩

def a815 (x : I) := withMem (entry x) (before x.data 1)
def a816 (x : I) := (a815 x).set .x13 (W (atBit x.data 1) >>> (3 : Nat))
def a817 (x : I) := (a816 x).set .x13 (OpeningRowData.addr x.data 1)
def a818 (x : I) := withMem (a817 x) (before x.data 2)
def a819 (x : I) := (a818 x).set .x12 (W (atBit x.data 2) >>> (3 : Nat))
def a820 (x : I) := (a819 x).set .x12 (OpeningRowData.addr x.data 2)
def a821 (x : I) := withMem (a820 x) (before x.data 3)
def a822 (x : I) := (a821 x).set .x11 (W (atBit x.data 3) >>> (3 : Nat))
def a823 (x : I) := (a822 x).set .x11 (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088))
def a824 (x : I) := (a823 x).set .x11 (OpeningRowData.addr x.data 3)
def a825 (x : I) := withMem (a824 x) (before x.data 4)

def codea : List Instr := [
  .SD .x30 .x29 0,
  Expr.instr .x13 (.srli .x28 3),
  Expr.instr .x13 (.add .x13 .x25),
  .SD .x13 .x12 0,
  Expr.instr .x12 (.srli .x6 3),
  Expr.instr .x12 (.add .x12 .x25),
  .SD .x12 .x14 0,
  Expr.instr .x11 (.srli .x11 3),
  Expr.instr .x11 (.andi .x11 4088),
  Expr.instr .x11 (.add .x11 .x25),
  .SD .x11 .x17 0]
theorem tablea : OpeningStraight.Listed 814 codea := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem spana (o : Oracle) (x : I) (align : off x.data=0) : Contract o codea (entry x) (a825 x) := by
  have h814 := OpeningRowData.storeAs o (entry x) .x30 .x29 0 (cell (atBit x.data 0)) (x.word 0) (before x.data 1) (by have := within x.data 0 (by decide);omega) (OpeningRowOps.current x.data 0) rfl (OpeningRowData.aligned x.data 0 align)
  have h815 := OpeningLinear.register o (a815 x) .x13 (.srli .x28 3) (W (atBit x.data 1) >>> (3 : Nat)) rfl
  have h816 := OpeningLinear.register o (a816 x) .x13 (.add .x13 .x25) (OpeningRowData.addr x.data 1) (OpeningRowOps.bare x.data 1 (by decide) align)
  have h817 := OpeningRowData.storeAs o (a817 x) .x13 .x12 0 (cell (atBit x.data 1)) (x.word 1) (before x.data 2) (by have := within x.data 1 (by decide);omega) (OpeningRowOps.current x.data 1) rfl (OpeningRowData.aligned x.data 1 align)
  have h818 := OpeningLinear.register o (a818 x) .x12 (.srli .x6 3) (W (atBit x.data 2) >>> (3 : Nat)) rfl
  have h819 := OpeningLinear.register o (a819 x) .x12 (.add .x12 .x25) (OpeningRowData.addr x.data 2) (OpeningRowOps.bare x.data 2 (by decide) align)
  have h820 := OpeningRowData.storeAs o (a820 x) .x12 .x14 0 (cell (atBit x.data 2)) (x.word 2) (before x.data 3) (by have := within x.data 2 (by decide);omega) (OpeningRowOps.current x.data 2) rfl (OpeningRowData.aligned x.data 2 align)
  have h821 := OpeningLinear.register o (a821 x) .x11 (.srli .x11 3) (W (atBit x.data 3) >>> (3 : Nat)) rfl
  have h822 := OpeningLinear.register o (a822 x) .x11 (.andi .x11 4088) (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h823 := OpeningLinear.register o (a823 x) .x11 (.add .x11 .x25) (OpeningRowData.addr x.data 3) (OpeningRowOps.pointer x.data 3 (by decide))
  have h824 := OpeningRowData.storeAs o (a824 x) .x11 .x17 0 (cell (atBit x.data 3)) (x.word 3) (before x.data 4) (by have := within x.data 3 (by decide);omega) (OpeningRowOps.current x.data 3) rfl (OpeningRowData.aligned x.data 3 align)
  exact LeafModel.combine h814 (LeafModel.combine h815 (LeafModel.combine h816 (LeafModel.combine h817 (LeafModel.combine h818 (LeafModel.combine h819 (LeafModel.combine h820 (LeafModel.combine h821 (LeafModel.combine h822 (LeafModel.combine h823 (LeafModel.combine h824 (LeafModel.empty _ _)))))))))))

def m777 (x : I) := (entry x).set .x13 (old x.data 0)
def m778 (x : I) := (m777 x).set .x5 (x.word 0 <<< off x.data)
def m779 (x : I) := (m778 x).set .x13 (merged x.data 0)
def m780 (x : I) := (m779 x).set .x5 (((0 : BitVec 32)-(W (off x.data)).truncate 32).signExtend 64)
def m781 (x : I) := (m780 x).set .x29 (high x.data 0)
def m782 (x : I) := withMem (m781 x) (tailMem x.data 0)
def m783 (x : I) := withMem (m782 x) (before x.data 1)
def m784 (x : I) := (m783 x).set .x13 (W (atBit x.data 1) >>> (3 : Nat))
def m785 (x : I) := (m784 x).set .x13 (((W (atBit x.data 1) >>> (3 : Nat)) &&& signExtend12 4088))
def m786 (x : I) := (m785 x).set .x13 (OpeningRowData.addr x.data 1)
def m787 (x : I) := (m786 x).set .x28 (old x.data 1)
def m788 (x : I) := (m787 x).set .x29 (x.word 1 <<< off x.data)
def m789 (x : I) := (m788 x).set .x28 (merged x.data 1)
def m790 (x : I) := (m789 x).set .x12 (high x.data 1)
def m791 (x : I) := withMem (m790 x) (tailMem x.data 1)
def m792 (x : I) := withMem (m791 x) (before x.data 2)
def m793 (x : I) := (m792 x).set .x12 (W (atBit x.data 2) >>> (3 : Nat))
def m794 (x : I) := (m793 x).set .x12 (((W (atBit x.data 2) >>> (3 : Nat)) &&& signExtend12 4088))
def m795 (x : I) := (m794 x).set .x12 (OpeningRowData.addr x.data 2)
def m796 (x : I) := (m795 x).set .x13 (old x.data 2)
def m797 (x : I) := (m796 x).set .x6 (x.word 2 <<< off x.data)
def m798 (x : I) := (m797 x).set .x13 (merged x.data 2)
def m799 (x : I) := (m798 x).set .x14 (high x.data 2)
def m800 (x : I) := withMem (m799 x) (tailMem x.data 2)
def m801 (x : I) := withMem (m800 x) (before x.data 3)
def m802 (x : I) := (m801 x).set .x11 (W (atBit x.data 3) >>> (3 : Nat))
def m803 (x : I) := (m802 x).set .x11 (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088))
def m804 (x : I) := (m803 x).set .x11 (OpeningRowData.addr x.data 3)
def m805 (x : I) := (m804 x).set .x12 (old x.data 3)
def m806 (x : I) := (m805 x).set .x13 (x.word 3 <<< off x.data)
def m807 (x : I) := (m806 x).set .x12 (merged x.data 3)
def m808 (x : I) := withMem (m807 x) (headMem x.data 3)
def m809 (x : I) := (m808 x).set .x12 (W 33)

def codem : List Instr := [
  .LD .x13 .x30 0,
  Expr.instr .x5 (.sll .x29 .x16),
  Expr.instr .x13 (.or .x13 .x5),
  Expr.instr .x5 (.subw .x0 .x16),
  Expr.instr .x29 (.srl .x29 .x5),
  .SD .x30 .x29 8,
  .SD .x30 .x13 0,
  Expr.instr .x13 (.srli .x28 3),
  Expr.instr .x13 (.andi .x13 4088),
  Expr.instr .x13 (.add .x13 .x25),
  .LD .x28 .x13 0,
  Expr.instr .x29 (.sll .x12 .x16),
  Expr.instr .x28 (.or .x28 .x29),
  Expr.instr .x12 (.srl .x12 .x5),
  .SD .x13 .x12 8,
  .SD .x13 .x28 0,
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
  Expr.instr .x12 (.addi .x0 33)]
theorem tablem : OpeningStraight.Listed 776 codem := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem spanm (o : Oracle) (x : I) (nz : off x.data≠0) : Contract o codem (entry x) (m809 x) := by
  have h776 := OpeningLinear.read o (entry x) .x13 .x30 0 (cell (atBit x.data 0)) (old x.data 0) (by have := within x.data 0 (by decide);omega) (OpeningRowOps.current x.data 0) rfl
  have h777 := OpeningLinear.register o (m777 x) .x5 (.sll .x29 .x16) (x.word 0 <<< off x.data) (OpeningRowOps.left x.data 0)
  have h778 := OpeningLinear.register o (m778 x) .x13 (.or .x13 .x5) (merged x.data 0) rfl
  have h779 := OpeningLinear.register o (m779 x) .x5 (.subw .x0 .x16) (((0 : BitVec 32)-(W (off x.data)).truncate 32).signExtend 64) rfl
  have h780 := OpeningLinear.register o (m780 x) .x29 (.srl .x29 .x5) (high x.data 0) (OpeningRowOps.rightNeg x.data 0 nz)
  have h781 := OpeningRowData.storeAs o (m781 x) .x30 .x29 8 (cell (atBit x.data 0)+1) (high x.data 0) (tailMem x.data 0) (within x.data 0 (by decide)) (OpeningRowOps.following x.data 0) rfl rfl
  have h782 := OpeningRowData.storeAs o (m782 x) .x30 .x13 0 (cell (atBit x.data 0)) (merged x.data 0) (before x.data 1) (by have := within x.data 0 (by decide);omega) (OpeningRowOps.current x.data 0) rfl (full x.data 0 (by decide) nz)
  have h783 := OpeningLinear.register o (m783 x) .x13 (.srli .x28 3) (W (atBit x.data 1) >>> (3 : Nat)) rfl
  have h784 := OpeningLinear.register o (m784 x) .x13 (.andi .x13 4088) (((W (atBit x.data 1) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h785 := OpeningLinear.register o (m785 x) .x13 (.add .x13 .x25) (OpeningRowData.addr x.data 1) (OpeningRowOps.pointer x.data 1 (by decide))
  have h786 := OpeningLinear.read o (m786 x) .x28 .x13 0 (cell (atBit x.data 1)) (old x.data 1) (by have := within x.data 1 (by decide);omega) (OpeningRowOps.current x.data 1) rfl
  have h787 := OpeningLinear.register o (m787 x) .x29 (.sll .x12 .x16) (x.word 1 <<< off x.data) (OpeningRowOps.left x.data 1)
  have h788 := OpeningLinear.register o (m788 x) .x28 (.or .x28 .x29) (merged x.data 1) rfl
  have h789 := OpeningLinear.register o (m789 x) .x12 (.srl .x12 .x5) (high x.data 1) (OpeningRowOps.rightNeg x.data 1 nz)
  have h790 := OpeningRowData.storeAs o (m790 x) .x13 .x12 8 (cell (atBit x.data 1)+1) (high x.data 1) (tailMem x.data 1) (within x.data 1 (by decide)) (OpeningRowOps.following x.data 1) rfl rfl
  have h791 := OpeningRowData.storeAs o (m791 x) .x13 .x28 0 (cell (atBit x.data 1)) (merged x.data 1) (before x.data 2) (by have := within x.data 1 (by decide);omega) (OpeningRowOps.current x.data 1) rfl (full x.data 1 (by decide) nz)
  have h792 := OpeningLinear.register o (m792 x) .x12 (.srli .x6 3) (W (atBit x.data 2) >>> (3 : Nat)) rfl
  have h793 := OpeningLinear.register o (m793 x) .x12 (.andi .x12 4088) (((W (atBit x.data 2) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h794 := OpeningLinear.register o (m794 x) .x12 (.add .x12 .x25) (OpeningRowData.addr x.data 2) (OpeningRowOps.pointer x.data 2 (by decide))
  have h795 := OpeningLinear.read o (m795 x) .x13 .x12 0 (cell (atBit x.data 2)) (old x.data 2) (by have := within x.data 2 (by decide);omega) (OpeningRowOps.current x.data 2) rfl
  have h796 := OpeningLinear.register o (m796 x) .x6 (.sll .x14 .x16) (x.word 2 <<< off x.data) (OpeningRowOps.left x.data 2)
  have h797 := OpeningLinear.register o (m797 x) .x13 (.or .x13 .x6) (merged x.data 2) rfl
  have h798 := OpeningLinear.register o (m798 x) .x14 (.srl .x14 .x5) (high x.data 2) (OpeningRowOps.rightNeg x.data 2 nz)
  have h799 := OpeningRowData.storeAs o (m799 x) .x12 .x14 8 (cell (atBit x.data 2)+1) (high x.data 2) (tailMem x.data 2) (within x.data 2 (by decide)) (OpeningRowOps.following x.data 2) rfl rfl
  have h800 := OpeningRowData.storeAs o (m800 x) .x12 .x13 0 (cell (atBit x.data 2)) (merged x.data 2) (before x.data 3) (by have := within x.data 2 (by decide);omega) (OpeningRowOps.current x.data 2) rfl (full x.data 2 (by decide) nz)
  have h801 := OpeningLinear.register o (m801 x) .x11 (.srli .x11 3) (W (atBit x.data 3) >>> (3 : Nat)) rfl
  have h802 := OpeningLinear.register o (m802 x) .x11 (.andi .x11 4088) (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h803 := OpeningLinear.register o (m803 x) .x11 (.add .x11 .x25) (OpeningRowData.addr x.data 3) (OpeningRowOps.pointer x.data 3 (by decide))
  have h804 := OpeningLinear.read o (m804 x) .x12 .x11 0 (cell (atBit x.data 3)) (old x.data 3) (by have := within x.data 3 (by decide);omega) (OpeningRowOps.current x.data 3) rfl
  have h805 := OpeningLinear.register o (m805 x) .x13 (.sll .x17 .x16) (x.word 3 <<< off x.data) (OpeningRowOps.left x.data 3)
  have h806 := OpeningLinear.register o (m806 x) .x12 (.or .x12 .x13) (merged x.data 3) rfl
  have h807 := OpeningRowData.storeAs o (m807 x) .x11 .x12 0 (cell (atBit x.data 3)) (merged x.data 3) (headMem x.data 3) (by have := within x.data 3 (by decide);omega) (OpeningRowOps.current x.data 3) rfl rfl
  have h808 := OpeningLinear.register o (m808 x) .x12 (.addi .x0 33) (W 33) rfl
  exact LeafModel.combine h776 (LeafModel.combine h777 (LeafModel.combine h778 (LeafModel.combine h779 (LeafModel.combine h780 (LeafModel.combine h781 (LeafModel.combine h782 (LeafModel.combine h783 (LeafModel.combine h784 (LeafModel.combine h785 (LeafModel.combine h786 (LeafModel.combine h787 (LeafModel.combine h788 (LeafModel.combine h789 (LeafModel.combine h790 (LeafModel.combine h791 (LeafModel.combine h792 (LeafModel.combine h793 (LeafModel.combine h794 (LeafModel.combine h795 (LeafModel.combine h796 (LeafModel.combine h797 (LeafModel.combine h798 (LeafModel.combine h799 (LeafModel.combine h800 (LeafModel.combine h801 (LeafModel.combine h802 (LeafModel.combine h803 (LeafModel.combine h804 (LeafModel.combine h805 (LeafModel.combine h806 (LeafModel.combine h807 (LeafModel.combine h808 (LeafModel.empty _ _)))))))))))))))))))))))))))))))))

def s811 (x : I) := (m809 x).set .x12 ((64 : Word)-W (off x.data))
def s812 (x : I) := (s811 x).set .x12 (high x.data 3)
def s813 (x : I) := withMem (s812 x) (before x.data 4)

def codes : List Instr := [
  Expr.instr .x12 (.sub .x18 .x16),
  Expr.instr .x12 (.srl .x17 .x12),
  .SD .x11 .x12 8]
theorem tables : OpeningStraight.Listed 810 codes := ⟨rfl,rfl,rfl,True.intro⟩
theorem spans (o : Oracle) (x : I) (nz : off x.data≠0) (cross : 64<off x.data+x.data.bits) : Contract o codes (m809 x) (s813 x) := by
  have h810 := OpeningLinear.register o (m809 x) .x12 (.sub .x18 .x16) ((64 : Word)-W (off x.data)) rfl
  have h811 := OpeningLinear.register o (s811 x) .x12 (.srl .x17 .x12) (high x.data 3) (OpeningRowOps.rightSub x.data 3 nz)
  have h812 := OpeningRowData.storeAs o (s812 x) .x11 .x12 8 (cell (atBit x.data 3)+1) (high x.data 3) (before x.data 4) (within x.data 3 (by decide)) (OpeningRowOps.following x.data 3) rfl (crosses x.data nz cross)
  exact LeafModel.combine h810 (LeafModel.combine h811 (LeafModel.combine h812 (LeafModel.empty _ _)))


def output (x : I) := if off x.data=0 then a825 x else if off x.data<33 then m809 x else s813 x

theorem run (o : Oracle) (x : I) (u : MachineState) (pc : u.pc=CommitBlocks.addr 775) (fit : Fits u (entry x)) :
    ∃ t n, n≤64 ∧ CommitExact.Segment o OpeningStraight.image n u t ∧ t.pc=CommitBlocks.addr 825 ∧
      Fits t (output x) := by
  have zstep := zero_branch o u 775 776 814 .x16 156 pc (by decide) rfl rfl rfl
    (W (off x.data)) (fit.registers _)
  have eqv : W (off x.data)=0 ↔ off x.data=0 := OpeningBranch.word_zero _
  simp only [eqv] at zstep
  unfold output
  by_cases z : off x.data=0
  · simp only [z,ite_true] at zstep ⊢
    obtain ⟨v,rv,pv,hv⟩ := OpeningLinear.block (spana o x z) (i:=814) (by decide) tablea
      (u.setPC _) rfl (fit.pc _)
    exact ⟨v,1+codea.length,by change 12≤64;decide,CommitExact.compose zstep rv,pv,hv⟩
  · simp only [z,ite_false] at zstep ⊢
    obtain ⟨v,rv,pv,hv⟩ := OpeningLinear.block (spanm o x z) (i:=776) (by decide) tablem (u.setPC _) rfl (fit.pc _)
    have branch := OpeningBranch.less o v .x16 .x12 809 825 64 pv (by decide) rfl rfl
      (off x.data) 33 (by unfold off;omega) (by decide) (hv.registers _) (hv.registers _)
    by_cases little : off x.data<33
    · simp only [little,ite_true] at branch ⊢
      exact ⟨_,1+codem.length+1,by change 35≤64;decide,CommitExact.compose (CommitExact.compose zstep rv) branch,rfl,hv.pc _⟩
    · simp only [little,ite_false] at branch ⊢
      have cross : 64<off x.data+x.data.bits := by change 64<off x.data+32;omega
      obtain ⟨w,rw,pw,hw⟩ := OpeningLinear.block (spans o x z cross) (i:=810) (by decide) tables
        (v.setPC _) rfl (hv.pc _)
      have jump := OpeningBranch.jump o w 813 825 48 pw (by decide) rfl rfl
      exact ⟨_,1+codem.length+1+codes.length+1,by change 39≤64;decide,CommitExact.compose (CommitExact.compose (CommitExact.compose
        (CommitExact.compose zstep rv) branch) rw) jump,rfl,hw.pc _⟩

theorem memory (x : I) : (output x).mem=before x.data 4 := by
  unfold output
  split
  · rfl
  · rename_i nz;split
    · rename_i little
      exact short x.data nz (by change off x.data+32≤64;omega)
    · rfl

def changed : List Reg := [.x5,.x6,.x11,.x12,.x13,.x14,.x28,.x29]

theorem frame (x : I) (r : Reg) (h : r∉changed) : (output x).reg r=(entry x).reg r := by
  unfold output
  split
  · cases r <;> first | rfl | exact False.elim (h (by decide))
  · split <;> cases r <;> first | rfl | exact False.elim (h (by decide))

end CommitGolfCandidate.Reconstruction.OpeningRow19
