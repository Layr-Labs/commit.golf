import CommitGolfCandidate.ReconstructedOpeningRowOps

namespace CommitGolfCandidate.Reconstruction.OpeningRow18
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningOps OpeningCursor OpeningPut OpeningRowData
open TwoPermutationPrototype.RV64
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000

abbrev I := OpeningRowOps.Input 1636 31
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
  | .x28 => x.word 0
  | .x29 => W (atBit x.data 1)
  | .x30 => OpeningRowData.addr x.data 0
  | r => x.initial.reg r, x.initial.mem⟩

def a881 (x : I) := withMem (entry x) (before x.data 1)
def a882 (x : I) := (a881 x).set .x13 (W (atBit x.data 1) >>> (3 : Nat))
def a883 (x : I) := (a882 x).set .x13 (OpeningRowData.addr x.data 1)
def a884 (x : I) := withMem (a883 x) (before x.data 2)
def a885 (x : I) := (a884 x).set .x12 (W (atBit x.data 2) >>> (3 : Nat))
def a886 (x : I) := (a885 x).set .x12 (OpeningRowData.addr x.data 2)
def a887 (x : I) := withMem (a886 x) (before x.data 3)
def a888 (x : I) := (a887 x).set .x11 (W (atBit x.data 3) >>> (3 : Nat))
def a889 (x : I) := (a888 x).set .x11 (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088))
def a890 (x : I) := (a889 x).set .x11 (OpeningRowData.addr x.data 3)
def a891 (x : I) := withMem (a890 x) (before x.data 4)

def codea : List Instr := [
  .SD .x30 .x28 0,
  Expr.instr .x13 (.srli .x29 3),
  Expr.instr .x13 (.add .x13 .x25),
  .SD .x13 .x12 0,
  Expr.instr .x12 (.srli .x6 3),
  Expr.instr .x12 (.add .x12 .x25),
  .SD .x12 .x14 0,
  Expr.instr .x11 (.srli .x11 3),
  Expr.instr .x11 (.andi .x11 4088),
  Expr.instr .x11 (.add .x11 .x25),
  .SD .x11 .x17 0]
theorem tablea : OpeningStraight.Listed 880 codea := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem spana (o : Oracle) (x : I) (align : off x.data=0) : Contract o codea (entry x) (a891 x) := by
  have h880 := OpeningRowData.storeAs o (entry x) .x30 .x28 0 (cell (atBit x.data 0)) (x.word 0) (before x.data 1) (by have := within x.data 0 (by decide);omega) (OpeningRowOps.current x.data 0) rfl (OpeningRowData.aligned x.data 0 align)
  have h881 := OpeningLinear.register o (a881 x) .x13 (.srli .x29 3) (W (atBit x.data 1) >>> (3 : Nat)) rfl
  have h882 := OpeningLinear.register o (a882 x) .x13 (.add .x13 .x25) (OpeningRowData.addr x.data 1) (OpeningRowOps.bare x.data 1 (by decide) align)
  have h883 := OpeningRowData.storeAs o (a883 x) .x13 .x12 0 (cell (atBit x.data 1)) (x.word 1) (before x.data 2) (by have := within x.data 1 (by decide);omega) (OpeningRowOps.current x.data 1) rfl (OpeningRowData.aligned x.data 1 align)
  have h884 := OpeningLinear.register o (a884 x) .x12 (.srli .x6 3) (W (atBit x.data 2) >>> (3 : Nat)) rfl
  have h885 := OpeningLinear.register o (a885 x) .x12 (.add .x12 .x25) (OpeningRowData.addr x.data 2) (OpeningRowOps.bare x.data 2 (by decide) align)
  have h886 := OpeningRowData.storeAs o (a886 x) .x12 .x14 0 (cell (atBit x.data 2)) (x.word 2) (before x.data 3) (by have := within x.data 2 (by decide);omega) (OpeningRowOps.current x.data 2) rfl (OpeningRowData.aligned x.data 2 align)
  have h887 := OpeningLinear.register o (a887 x) .x11 (.srli .x11 3) (W (atBit x.data 3) >>> (3 : Nat)) rfl
  have h888 := OpeningLinear.register o (a888 x) .x11 (.andi .x11 4088) (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h889 := OpeningLinear.register o (a889 x) .x11 (.add .x11 .x25) (OpeningRowData.addr x.data 3) (OpeningRowOps.pointer x.data 3 (by decide))
  have h890 := OpeningRowData.storeAs o (a890 x) .x11 .x17 0 (cell (atBit x.data 3)) (x.word 3) (before x.data 4) (by have := within x.data 3 (by decide);omega) (OpeningRowOps.current x.data 3) rfl (OpeningRowData.aligned x.data 3 align)
  exact LeafModel.combine h880 (LeafModel.combine h881 (LeafModel.combine h882 (LeafModel.combine h883 (LeafModel.combine h884 (LeafModel.combine h885 (LeafModel.combine h886 (LeafModel.combine h887 (LeafModel.combine h888 (LeafModel.combine h889 (LeafModel.combine h890 (LeafModel.empty _ _)))))))))))

def m843 (x : I) := (entry x).set .x13 (old x.data 0)
def m844 (x : I) := (m843 x).set .x5 (x.word 0 <<< off x.data)
def m845 (x : I) := (m844 x).set .x13 (merged x.data 0)
def m846 (x : I) := (m845 x).set .x5 (((0 : BitVec 32)-(W (off x.data)).truncate 32).signExtend 64)
def m847 (x : I) := (m846 x).set .x28 (high x.data 0)
def m848 (x : I) := withMem (m847 x) (tailMem x.data 0)
def m849 (x : I) := withMem (m848 x) (before x.data 1)
def m850 (x : I) := (m849 x).set .x13 (W (atBit x.data 1) >>> (3 : Nat))
def m851 (x : I) := (m850 x).set .x13 (((W (atBit x.data 1) >>> (3 : Nat)) &&& signExtend12 4088))
def m852 (x : I) := (m851 x).set .x13 (OpeningRowData.addr x.data 1)
def m853 (x : I) := (m852 x).set .x28 (old x.data 1)
def m854 (x : I) := (m853 x).set .x29 (x.word 1 <<< off x.data)
def m855 (x : I) := (m854 x).set .x28 (merged x.data 1)
def m856 (x : I) := (m855 x).set .x12 (high x.data 1)
def m857 (x : I) := withMem (m856 x) (tailMem x.data 1)
def m858 (x : I) := withMem (m857 x) (before x.data 2)
def m859 (x : I) := (m858 x).set .x12 (W (atBit x.data 2) >>> (3 : Nat))
def m860 (x : I) := (m859 x).set .x12 (((W (atBit x.data 2) >>> (3 : Nat)) &&& signExtend12 4088))
def m861 (x : I) := (m860 x).set .x12 (OpeningRowData.addr x.data 2)
def m862 (x : I) := (m861 x).set .x13 (old x.data 2)
def m863 (x : I) := (m862 x).set .x6 (x.word 2 <<< off x.data)
def m864 (x : I) := (m863 x).set .x13 (merged x.data 2)
def m865 (x : I) := (m864 x).set .x14 (high x.data 2)
def m866 (x : I) := withMem (m865 x) (tailMem x.data 2)
def m867 (x : I) := withMem (m866 x) (before x.data 3)
def m868 (x : I) := (m867 x).set .x11 (W (atBit x.data 3) >>> (3 : Nat))
def m869 (x : I) := (m868 x).set .x11 (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088))
def m870 (x : I) := (m869 x).set .x11 (OpeningRowData.addr x.data 3)
def m871 (x : I) := (m870 x).set .x12 (old x.data 3)
def m872 (x : I) := (m871 x).set .x13 (x.word 3 <<< off x.data)
def m873 (x : I) := (m872 x).set .x12 (merged x.data 3)
def m874 (x : I) := withMem (m873 x) (headMem x.data 3)
def m875 (x : I) := (m874 x).set .x12 (W 34)

def codem : List Instr := [
  .LD .x13 .x30 0,
  Expr.instr .x5 (.sll .x28 .x16),
  Expr.instr .x13 (.or .x13 .x5),
  Expr.instr .x5 (.subw .x0 .x16),
  Expr.instr .x28 (.srl .x28 .x5),
  .SD .x30 .x28 8,
  .SD .x30 .x13 0,
  Expr.instr .x13 (.srli .x29 3),
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
  Expr.instr .x12 (.addi .x0 34)]
theorem tablem : OpeningStraight.Listed 842 codem := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem spanm (o : Oracle) (x : I) (nz : off x.data≠0) : Contract o codem (entry x) (m875 x) := by
  have h842 := OpeningLinear.read o (entry x) .x13 .x30 0 (cell (atBit x.data 0)) (old x.data 0) (by have := within x.data 0 (by decide);omega) (OpeningRowOps.current x.data 0) rfl
  have h843 := OpeningLinear.register o (m843 x) .x5 (.sll .x28 .x16) (x.word 0 <<< off x.data) (OpeningRowOps.left x.data 0)
  have h844 := OpeningLinear.register o (m844 x) .x13 (.or .x13 .x5) (merged x.data 0) rfl
  have h845 := OpeningLinear.register o (m845 x) .x5 (.subw .x0 .x16) (((0 : BitVec 32)-(W (off x.data)).truncate 32).signExtend 64) rfl
  have h846 := OpeningLinear.register o (m846 x) .x28 (.srl .x28 .x5) (high x.data 0) (OpeningRowOps.rightNeg x.data 0 nz)
  have h847 := OpeningRowData.storeAs o (m847 x) .x30 .x28 8 (cell (atBit x.data 0)+1) (high x.data 0) (tailMem x.data 0) (within x.data 0 (by decide)) (OpeningRowOps.following x.data 0) rfl rfl
  have h848 := OpeningRowData.storeAs o (m848 x) .x30 .x13 0 (cell (atBit x.data 0)) (merged x.data 0) (before x.data 1) (by have := within x.data 0 (by decide);omega) (OpeningRowOps.current x.data 0) rfl (full x.data 0 (by decide) nz)
  have h849 := OpeningLinear.register o (m849 x) .x13 (.srli .x29 3) (W (atBit x.data 1) >>> (3 : Nat)) rfl
  have h850 := OpeningLinear.register o (m850 x) .x13 (.andi .x13 4088) (((W (atBit x.data 1) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h851 := OpeningLinear.register o (m851 x) .x13 (.add .x13 .x25) (OpeningRowData.addr x.data 1) (OpeningRowOps.pointer x.data 1 (by decide))
  have h852 := OpeningLinear.read o (m852 x) .x28 .x13 0 (cell (atBit x.data 1)) (old x.data 1) (by have := within x.data 1 (by decide);omega) (OpeningRowOps.current x.data 1) rfl
  have h853 := OpeningLinear.register o (m853 x) .x29 (.sll .x12 .x16) (x.word 1 <<< off x.data) (OpeningRowOps.left x.data 1)
  have h854 := OpeningLinear.register o (m854 x) .x28 (.or .x28 .x29) (merged x.data 1) rfl
  have h855 := OpeningLinear.register o (m855 x) .x12 (.srl .x12 .x5) (high x.data 1) (OpeningRowOps.rightNeg x.data 1 nz)
  have h856 := OpeningRowData.storeAs o (m856 x) .x13 .x12 8 (cell (atBit x.data 1)+1) (high x.data 1) (tailMem x.data 1) (within x.data 1 (by decide)) (OpeningRowOps.following x.data 1) rfl rfl
  have h857 := OpeningRowData.storeAs o (m857 x) .x13 .x28 0 (cell (atBit x.data 1)) (merged x.data 1) (before x.data 2) (by have := within x.data 1 (by decide);omega) (OpeningRowOps.current x.data 1) rfl (full x.data 1 (by decide) nz)
  have h858 := OpeningLinear.register o (m858 x) .x12 (.srli .x6 3) (W (atBit x.data 2) >>> (3 : Nat)) rfl
  have h859 := OpeningLinear.register o (m859 x) .x12 (.andi .x12 4088) (((W (atBit x.data 2) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h860 := OpeningLinear.register o (m860 x) .x12 (.add .x12 .x25) (OpeningRowData.addr x.data 2) (OpeningRowOps.pointer x.data 2 (by decide))
  have h861 := OpeningLinear.read o (m861 x) .x13 .x12 0 (cell (atBit x.data 2)) (old x.data 2) (by have := within x.data 2 (by decide);omega) (OpeningRowOps.current x.data 2) rfl
  have h862 := OpeningLinear.register o (m862 x) .x6 (.sll .x14 .x16) (x.word 2 <<< off x.data) (OpeningRowOps.left x.data 2)
  have h863 := OpeningLinear.register o (m863 x) .x13 (.or .x13 .x6) (merged x.data 2) rfl
  have h864 := OpeningLinear.register o (m864 x) .x14 (.srl .x14 .x5) (high x.data 2) (OpeningRowOps.rightNeg x.data 2 nz)
  have h865 := OpeningRowData.storeAs o (m865 x) .x12 .x14 8 (cell (atBit x.data 2)+1) (high x.data 2) (tailMem x.data 2) (within x.data 2 (by decide)) (OpeningRowOps.following x.data 2) rfl rfl
  have h866 := OpeningRowData.storeAs o (m866 x) .x12 .x13 0 (cell (atBit x.data 2)) (merged x.data 2) (before x.data 3) (by have := within x.data 2 (by decide);omega) (OpeningRowOps.current x.data 2) rfl (full x.data 2 (by decide) nz)
  have h867 := OpeningLinear.register o (m867 x) .x11 (.srli .x11 3) (W (atBit x.data 3) >>> (3 : Nat)) rfl
  have h868 := OpeningLinear.register o (m868 x) .x11 (.andi .x11 4088) (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h869 := OpeningLinear.register o (m869 x) .x11 (.add .x11 .x25) (OpeningRowData.addr x.data 3) (OpeningRowOps.pointer x.data 3 (by decide))
  have h870 := OpeningLinear.read o (m870 x) .x12 .x11 0 (cell (atBit x.data 3)) (old x.data 3) (by have := within x.data 3 (by decide);omega) (OpeningRowOps.current x.data 3) rfl
  have h871 := OpeningLinear.register o (m871 x) .x13 (.sll .x17 .x16) (x.word 3 <<< off x.data) (OpeningRowOps.left x.data 3)
  have h872 := OpeningLinear.register o (m872 x) .x12 (.or .x12 .x13) (merged x.data 3) rfl
  have h873 := OpeningRowData.storeAs o (m873 x) .x11 .x12 0 (cell (atBit x.data 3)) (merged x.data 3) (headMem x.data 3) (by have := within x.data 3 (by decide);omega) (OpeningRowOps.current x.data 3) rfl rfl
  have h874 := OpeningLinear.register o (m874 x) .x12 (.addi .x0 34) (W 34) rfl
  exact LeafModel.combine h842 (LeafModel.combine h843 (LeafModel.combine h844 (LeafModel.combine h845 (LeafModel.combine h846 (LeafModel.combine h847 (LeafModel.combine h848 (LeafModel.combine h849 (LeafModel.combine h850 (LeafModel.combine h851 (LeafModel.combine h852 (LeafModel.combine h853 (LeafModel.combine h854 (LeafModel.combine h855 (LeafModel.combine h856 (LeafModel.combine h857 (LeafModel.combine h858 (LeafModel.combine h859 (LeafModel.combine h860 (LeafModel.combine h861 (LeafModel.combine h862 (LeafModel.combine h863 (LeafModel.combine h864 (LeafModel.combine h865 (LeafModel.combine h866 (LeafModel.combine h867 (LeafModel.combine h868 (LeafModel.combine h869 (LeafModel.combine h870 (LeafModel.combine h871 (LeafModel.combine h872 (LeafModel.combine h873 (LeafModel.combine h874 (LeafModel.empty _ _)))))))))))))))))))))))))))))))))

def s877 (x : I) := (m875 x).set .x12 ((64 : Word)-W (off x.data))
def s878 (x : I) := (s877 x).set .x12 (high x.data 3)
def s879 (x : I) := withMem (s878 x) (before x.data 4)

def codes : List Instr := [
  Expr.instr .x12 (.sub .x18 .x16),
  Expr.instr .x12 (.srl .x17 .x12),
  .SD .x11 .x12 8]
theorem tables : OpeningStraight.Listed 876 codes := ⟨rfl,rfl,rfl,True.intro⟩
theorem spans (o : Oracle) (x : I) (nz : off x.data≠0) (cross : 64<off x.data+x.data.bits) : Contract o codes (m875 x) (s879 x) := by
  have h876 := OpeningLinear.register o (m875 x) .x12 (.sub .x18 .x16) ((64 : Word)-W (off x.data)) rfl
  have h877 := OpeningLinear.register o (s877 x) .x12 (.srl .x17 .x12) (high x.data 3) (OpeningRowOps.rightSub x.data 3 nz)
  have h878 := OpeningRowData.storeAs o (s878 x) .x11 .x12 8 (cell (atBit x.data 3)+1) (high x.data 3) (before x.data 4) (within x.data 3 (by decide)) (OpeningRowOps.following x.data 3) rfl (crosses x.data nz cross)
  exact LeafModel.combine h876 (LeafModel.combine h877 (LeafModel.combine h878 (LeafModel.empty _ _)))


def output (x : I) := if off x.data=0 then a891 x else if off x.data<34 then m875 x else s879 x

theorem run (o : Oracle) (x : I) (u : MachineState) (pc : u.pc=CommitBlocks.addr 841) (fit : Fits u (entry x)) :
    ∃ t n, n≤64 ∧ CommitExact.Segment o OpeningStraight.image n u t ∧ t.pc=CommitBlocks.addr 891 ∧
      Fits t (output x) := by
  have zstep := zero_branch o u 841 842 880 .x16 156 pc (by decide) rfl rfl rfl
    (W (off x.data)) (fit.registers _)
  have eqv : W (off x.data)=0 ↔ off x.data=0 := OpeningBranch.word_zero _
  simp only [eqv] at zstep
  unfold output
  by_cases z : off x.data=0
  · simp only [z,ite_true] at zstep ⊢
    obtain ⟨v,rv,pv,hv⟩ := OpeningLinear.block (spana o x z) (i:=880) (by decide) tablea
      (u.setPC _) rfl (fit.pc _)
    exact ⟨v,1+codea.length,by change 12≤64;decide,CommitExact.compose zstep rv,pv,hv⟩
  · simp only [z,ite_false] at zstep ⊢
    obtain ⟨v,rv,pv,hv⟩ := OpeningLinear.block (spanm o x z) (i:=842) (by decide) tablem (u.setPC _) rfl (fit.pc _)
    have branch := OpeningBranch.less o v .x16 .x12 875 891 64 pv (by decide) rfl rfl
      (off x.data) 34 (by unfold off;omega) (by decide) (hv.registers _) (hv.registers _)
    by_cases little : off x.data<34
    · simp only [little,ite_true] at branch ⊢
      exact ⟨_,1+codem.length+1,by change 35≤64;decide,CommitExact.compose (CommitExact.compose zstep rv) branch,rfl,hv.pc _⟩
    · simp only [little,ite_false] at branch ⊢
      have cross : 64<off x.data+x.data.bits := by change 64<off x.data+31;omega
      obtain ⟨w,rw,pw,hw⟩ := OpeningLinear.block (spans o x z cross) (i:=876) (by decide) tables
        (v.setPC _) rfl (hv.pc _)
      have jump := OpeningBranch.jump o w 879 891 48 pw (by decide) rfl rfl
      exact ⟨_,1+codem.length+1+codes.length+1,by change 39≤64;decide,CommitExact.compose (CommitExact.compose (CommitExact.compose
        (CommitExact.compose zstep rv) branch) rw) jump,rfl,hw.pc _⟩

theorem memory (x : I) : (output x).mem=before x.data 4 := by
  unfold output
  split
  · rfl
  · rename_i nz;split
    · rename_i little
      exact short x.data nz (by change off x.data+31≤64;omega)
    · rfl

def changed : List Reg := [.x5,.x6,.x11,.x12,.x13,.x14,.x28,.x29]

theorem frame (x : I) (r : Reg) (h : r∉changed) : (output x).reg r=(entry x).reg r := by
  unfold output
  split
  · cases r <;> first | rfl | exact False.elim (h (by decide))
  · split <;> cases r <;> first | rfl | exact False.elim (h (by decide))

end CommitGolfCandidate.Reconstruction.OpeningRow18
