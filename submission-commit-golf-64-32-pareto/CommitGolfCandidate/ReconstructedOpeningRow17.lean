import CommitGolfCandidate.ReconstructedOpeningRowOps

namespace CommitGolfCandidate.Reconstruction.OpeningRow17
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningOps OpeningCursor OpeningPut OpeningRowData
open TwoPermutationPrototype.RV64
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000

abbrev I := OpeningRowOps.Input 1859 30
def entry (x : I) : Model := ⟨fun
  | .x0 => W 0
  | .x6 => x.word 0
  | .x11 => x.word 1
  | .x12 => W (atBit x.data 2)
  | .x14 => x.word 2
  | .x16 => W (off x.data)
  | .x17 => x.word 3
  | .x18 => W 64
  | .x20 => W (atBit x.data 3)
  | .x25 => wordAddress OpeningPut.base
  | .x28 => OpeningRowData.addr x.data 0
  | .x29 => W (atBit x.data 1)
  | r => x.initial.reg r, x.initial.mem⟩

def a947 (x : I) := withMem (entry x) (before x.data 1)
def a948 (x : I) := (a947 x).set .x13 (W (atBit x.data 1) >>> (3 : Nat))
def a949 (x : I) := (a948 x).set .x13 (OpeningRowData.addr x.data 1)
def a950 (x : I) := withMem (a949 x) (before x.data 2)
def a951 (x : I) := (a950 x).set .x12 (W (atBit x.data 2) >>> (3 : Nat))
def a952 (x : I) := (a951 x).set .x12 (OpeningRowData.addr x.data 2)
def a953 (x : I) := withMem (a952 x) (before x.data 3)
def a954 (x : I) := (a953 x).set .x11 (W (atBit x.data 3) >>> (3 : Nat))
def a955 (x : I) := (a954 x).set .x11 (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088))
def a956 (x : I) := (a955 x).set .x11 (OpeningRowData.addr x.data 3)
def a957 (x : I) := withMem (a956 x) (before x.data 4)

def codea : List Instr := [
  .SD .x28 .x6 0,
  Expr.instr .x13 (.srli .x29 3),
  Expr.instr .x13 (.add .x13 .x25),
  .SD .x13 .x11 0,
  Expr.instr .x12 (.srli .x12 3),
  Expr.instr .x12 (.add .x12 .x25),
  .SD .x12 .x14 0,
  Expr.instr .x11 (.srli .x20 3),
  Expr.instr .x11 (.andi .x11 4088),
  Expr.instr .x11 (.add .x11 .x25),
  .SD .x11 .x17 0]
theorem tablea : OpeningStraight.Listed 946 codea := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem spana (o : Oracle) (x : I) (align : off x.data=0) : Contract o codea (entry x) (a957 x) := by
  have h946 := OpeningRowData.storeAs o (entry x) .x28 .x6 0 (cell (atBit x.data 0)) (x.word 0) (before x.data 1) (by have := within x.data 0 (by decide);omega) (OpeningRowOps.current x.data 0) rfl (OpeningRowData.aligned x.data 0 align)
  have h947 := OpeningLinear.register o (a947 x) .x13 (.srli .x29 3) (W (atBit x.data 1) >>> (3 : Nat)) rfl
  have h948 := OpeningLinear.register o (a948 x) .x13 (.add .x13 .x25) (OpeningRowData.addr x.data 1) (OpeningRowOps.bare x.data 1 (by decide) align)
  have h949 := OpeningRowData.storeAs o (a949 x) .x13 .x11 0 (cell (atBit x.data 1)) (x.word 1) (before x.data 2) (by have := within x.data 1 (by decide);omega) (OpeningRowOps.current x.data 1) rfl (OpeningRowData.aligned x.data 1 align)
  have h950 := OpeningLinear.register o (a950 x) .x12 (.srli .x12 3) (W (atBit x.data 2) >>> (3 : Nat)) rfl
  have h951 := OpeningLinear.register o (a951 x) .x12 (.add .x12 .x25) (OpeningRowData.addr x.data 2) (OpeningRowOps.bare x.data 2 (by decide) align)
  have h952 := OpeningRowData.storeAs o (a952 x) .x12 .x14 0 (cell (atBit x.data 2)) (x.word 2) (before x.data 3) (by have := within x.data 2 (by decide);omega) (OpeningRowOps.current x.data 2) rfl (OpeningRowData.aligned x.data 2 align)
  have h953 := OpeningLinear.register o (a953 x) .x11 (.srli .x20 3) (W (atBit x.data 3) >>> (3 : Nat)) rfl
  have h954 := OpeningLinear.register o (a954 x) .x11 (.andi .x11 4088) (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h955 := OpeningLinear.register o (a955 x) .x11 (.add .x11 .x25) (OpeningRowData.addr x.data 3) (OpeningRowOps.pointer x.data 3 (by decide))
  have h956 := OpeningRowData.storeAs o (a956 x) .x11 .x17 0 (cell (atBit x.data 3)) (x.word 3) (before x.data 4) (by have := within x.data 3 (by decide);omega) (OpeningRowOps.current x.data 3) rfl (OpeningRowData.aligned x.data 3 align)
  exact LeafModel.combine h946 (LeafModel.combine h947 (LeafModel.combine h948 (LeafModel.combine h949 (LeafModel.combine h950 (LeafModel.combine h951 (LeafModel.combine h952 (LeafModel.combine h953 (LeafModel.combine h954 (LeafModel.combine h955 (LeafModel.combine h956 (LeafModel.empty _ _)))))))))))

def m909 (x : I) := (entry x).set .x13 (old x.data 0)
def m910 (x : I) := (m909 x).set .x5 (x.word 0 <<< off x.data)
def m911 (x : I) := (m910 x).set .x13 (merged x.data 0)
def m912 (x : I) := (m911 x).set .x5 (((0 : BitVec 32)-(W (off x.data)).truncate 32).signExtend 64)
def m913 (x : I) := (m912 x).set .x6 (high x.data 0)
def m914 (x : I) := withMem (m913 x) (tailMem x.data 0)
def m915 (x : I) := withMem (m914 x) (before x.data 1)
def m916 (x : I) := (m915 x).set .x13 (W (atBit x.data 1) >>> (3 : Nat))
def m917 (x : I) := (m916 x).set .x13 (((W (atBit x.data 1) >>> (3 : Nat)) &&& signExtend12 4088))
def m918 (x : I) := (m917 x).set .x13 (OpeningRowData.addr x.data 1)
def m919 (x : I) := (m918 x).set .x6 (old x.data 1)
def m920 (x : I) := (m919 x).set .x7 (x.word 1 <<< off x.data)
def m921 (x : I) := (m920 x).set .x6 (merged x.data 1)
def m922 (x : I) := (m921 x).set .x11 (high x.data 1)
def m923 (x : I) := withMem (m922 x) (tailMem x.data 1)
def m924 (x : I) := withMem (m923 x) (before x.data 2)
def m925 (x : I) := (m924 x).set .x12 (W (atBit x.data 2) >>> (3 : Nat))
def m926 (x : I) := (m925 x).set .x12 (((W (atBit x.data 2) >>> (3 : Nat)) &&& signExtend12 4088))
def m927 (x : I) := (m926 x).set .x12 (OpeningRowData.addr x.data 2)
def m928 (x : I) := (m927 x).set .x11 (old x.data 2)
def m929 (x : I) := (m928 x).set .x13 (x.word 2 <<< off x.data)
def m930 (x : I) := (m929 x).set .x11 (merged x.data 2)
def m931 (x : I) := (m930 x).set .x13 (high x.data 2)
def m932 (x : I) := withMem (m931 x) (tailMem x.data 2)
def m933 (x : I) := withMem (m932 x) (before x.data 3)
def m934 (x : I) := (m933 x).set .x11 (W (atBit x.data 3) >>> (3 : Nat))
def m935 (x : I) := (m934 x).set .x11 (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088))
def m936 (x : I) := (m935 x).set .x11 (OpeningRowData.addr x.data 3)
def m937 (x : I) := (m936 x).set .x12 (old x.data 3)
def m938 (x : I) := (m937 x).set .x13 (x.word 3 <<< off x.data)
def m939 (x : I) := (m938 x).set .x12 (merged x.data 3)
def m940 (x : I) := withMem (m939 x) (headMem x.data 3)
def m941 (x : I) := (m940 x).set .x12 (W 35)

def codem : List Instr := [
  .LD .x13 .x28 0,
  Expr.instr .x5 (.sll .x6 .x16),
  Expr.instr .x13 (.or .x13 .x5),
  Expr.instr .x5 (.subw .x0 .x16),
  Expr.instr .x6 (.srl .x6 .x5),
  .SD .x28 .x6 8,
  .SD .x28 .x13 0,
  Expr.instr .x13 (.srli .x29 3),
  Expr.instr .x13 (.andi .x13 4088),
  Expr.instr .x13 (.add .x13 .x25),
  .LD .x6 .x13 0,
  Expr.instr .x7 (.sll .x11 .x16),
  Expr.instr .x6 (.or .x6 .x7),
  Expr.instr .x11 (.srl .x11 .x5),
  .SD .x13 .x11 8,
  .SD .x13 .x6 0,
  Expr.instr .x12 (.srli .x12 3),
  Expr.instr .x12 (.andi .x12 4088),
  Expr.instr .x12 (.add .x12 .x25),
  .LD .x11 .x12 0,
  Expr.instr .x13 (.sll .x14 .x16),
  Expr.instr .x11 (.or .x11 .x13),
  Expr.instr .x13 (.srl .x14 .x5),
  .SD .x12 .x13 8,
  .SD .x12 .x11 0,
  Expr.instr .x11 (.srli .x20 3),
  Expr.instr .x11 (.andi .x11 4088),
  Expr.instr .x11 (.add .x11 .x25),
  .LD .x12 .x11 0,
  Expr.instr .x13 (.sll .x17 .x16),
  Expr.instr .x12 (.or .x12 .x13),
  .SD .x11 .x12 0,
  Expr.instr .x12 (.addi .x0 35)]
theorem tablem : OpeningStraight.Listed 908 codem := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem spanm (o : Oracle) (x : I) (nz : off x.data≠0) : Contract o codem (entry x) (m941 x) := by
  have h908 := OpeningLinear.read o (entry x) .x13 .x28 0 (cell (atBit x.data 0)) (old x.data 0) (by have := within x.data 0 (by decide);omega) (OpeningRowOps.current x.data 0) rfl
  have h909 := OpeningLinear.register o (m909 x) .x5 (.sll .x6 .x16) (x.word 0 <<< off x.data) (OpeningRowOps.left x.data 0)
  have h910 := OpeningLinear.register o (m910 x) .x13 (.or .x13 .x5) (merged x.data 0) rfl
  have h911 := OpeningLinear.register o (m911 x) .x5 (.subw .x0 .x16) (((0 : BitVec 32)-(W (off x.data)).truncate 32).signExtend 64) rfl
  have h912 := OpeningLinear.register o (m912 x) .x6 (.srl .x6 .x5) (high x.data 0) (OpeningRowOps.rightNeg x.data 0 nz)
  have h913 := OpeningRowData.storeAs o (m913 x) .x28 .x6 8 (cell (atBit x.data 0)+1) (high x.data 0) (tailMem x.data 0) (within x.data 0 (by decide)) (OpeningRowOps.following x.data 0) rfl rfl
  have h914 := OpeningRowData.storeAs o (m914 x) .x28 .x13 0 (cell (atBit x.data 0)) (merged x.data 0) (before x.data 1) (by have := within x.data 0 (by decide);omega) (OpeningRowOps.current x.data 0) rfl (full x.data 0 (by decide) nz)
  have h915 := OpeningLinear.register o (m915 x) .x13 (.srli .x29 3) (W (atBit x.data 1) >>> (3 : Nat)) rfl
  have h916 := OpeningLinear.register o (m916 x) .x13 (.andi .x13 4088) (((W (atBit x.data 1) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h917 := OpeningLinear.register o (m917 x) .x13 (.add .x13 .x25) (OpeningRowData.addr x.data 1) (OpeningRowOps.pointer x.data 1 (by decide))
  have h918 := OpeningLinear.read o (m918 x) .x6 .x13 0 (cell (atBit x.data 1)) (old x.data 1) (by have := within x.data 1 (by decide);omega) (OpeningRowOps.current x.data 1) rfl
  have h919 := OpeningLinear.register o (m919 x) .x7 (.sll .x11 .x16) (x.word 1 <<< off x.data) (OpeningRowOps.left x.data 1)
  have h920 := OpeningLinear.register o (m920 x) .x6 (.or .x6 .x7) (merged x.data 1) rfl
  have h921 := OpeningLinear.register o (m921 x) .x11 (.srl .x11 .x5) (high x.data 1) (OpeningRowOps.rightNeg x.data 1 nz)
  have h922 := OpeningRowData.storeAs o (m922 x) .x13 .x11 8 (cell (atBit x.data 1)+1) (high x.data 1) (tailMem x.data 1) (within x.data 1 (by decide)) (OpeningRowOps.following x.data 1) rfl rfl
  have h923 := OpeningRowData.storeAs o (m923 x) .x13 .x6 0 (cell (atBit x.data 1)) (merged x.data 1) (before x.data 2) (by have := within x.data 1 (by decide);omega) (OpeningRowOps.current x.data 1) rfl (full x.data 1 (by decide) nz)
  have h924 := OpeningLinear.register o (m924 x) .x12 (.srli .x12 3) (W (atBit x.data 2) >>> (3 : Nat)) rfl
  have h925 := OpeningLinear.register o (m925 x) .x12 (.andi .x12 4088) (((W (atBit x.data 2) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h926 := OpeningLinear.register o (m926 x) .x12 (.add .x12 .x25) (OpeningRowData.addr x.data 2) (OpeningRowOps.pointer x.data 2 (by decide))
  have h927 := OpeningLinear.read o (m927 x) .x11 .x12 0 (cell (atBit x.data 2)) (old x.data 2) (by have := within x.data 2 (by decide);omega) (OpeningRowOps.current x.data 2) rfl
  have h928 := OpeningLinear.register o (m928 x) .x13 (.sll .x14 .x16) (x.word 2 <<< off x.data) (OpeningRowOps.left x.data 2)
  have h929 := OpeningLinear.register o (m929 x) .x11 (.or .x11 .x13) (merged x.data 2) rfl
  have h930 := OpeningLinear.register o (m930 x) .x13 (.srl .x14 .x5) (high x.data 2) (OpeningRowOps.rightNeg x.data 2 nz)
  have h931 := OpeningRowData.storeAs o (m931 x) .x12 .x13 8 (cell (atBit x.data 2)+1) (high x.data 2) (tailMem x.data 2) (within x.data 2 (by decide)) (OpeningRowOps.following x.data 2) rfl rfl
  have h932 := OpeningRowData.storeAs o (m932 x) .x12 .x11 0 (cell (atBit x.data 2)) (merged x.data 2) (before x.data 3) (by have := within x.data 2 (by decide);omega) (OpeningRowOps.current x.data 2) rfl (full x.data 2 (by decide) nz)
  have h933 := OpeningLinear.register o (m933 x) .x11 (.srli .x20 3) (W (atBit x.data 3) >>> (3 : Nat)) rfl
  have h934 := OpeningLinear.register o (m934 x) .x11 (.andi .x11 4088) (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h935 := OpeningLinear.register o (m935 x) .x11 (.add .x11 .x25) (OpeningRowData.addr x.data 3) (OpeningRowOps.pointer x.data 3 (by decide))
  have h936 := OpeningLinear.read o (m936 x) .x12 .x11 0 (cell (atBit x.data 3)) (old x.data 3) (by have := within x.data 3 (by decide);omega) (OpeningRowOps.current x.data 3) rfl
  have h937 := OpeningLinear.register o (m937 x) .x13 (.sll .x17 .x16) (x.word 3 <<< off x.data) (OpeningRowOps.left x.data 3)
  have h938 := OpeningLinear.register o (m938 x) .x12 (.or .x12 .x13) (merged x.data 3) rfl
  have h939 := OpeningRowData.storeAs o (m939 x) .x11 .x12 0 (cell (atBit x.data 3)) (merged x.data 3) (headMem x.data 3) (by have := within x.data 3 (by decide);omega) (OpeningRowOps.current x.data 3) rfl rfl
  have h940 := OpeningLinear.register o (m940 x) .x12 (.addi .x0 35) (W 35) rfl
  exact LeafModel.combine h908 (LeafModel.combine h909 (LeafModel.combine h910 (LeafModel.combine h911 (LeafModel.combine h912 (LeafModel.combine h913 (LeafModel.combine h914 (LeafModel.combine h915 (LeafModel.combine h916 (LeafModel.combine h917 (LeafModel.combine h918 (LeafModel.combine h919 (LeafModel.combine h920 (LeafModel.combine h921 (LeafModel.combine h922 (LeafModel.combine h923 (LeafModel.combine h924 (LeafModel.combine h925 (LeafModel.combine h926 (LeafModel.combine h927 (LeafModel.combine h928 (LeafModel.combine h929 (LeafModel.combine h930 (LeafModel.combine h931 (LeafModel.combine h932 (LeafModel.combine h933 (LeafModel.combine h934 (LeafModel.combine h935 (LeafModel.combine h936 (LeafModel.combine h937 (LeafModel.combine h938 (LeafModel.combine h939 (LeafModel.combine h940 (LeafModel.empty _ _)))))))))))))))))))))))))))))))))

def s943 (x : I) := (m941 x).set .x12 ((64 : Word)-W (off x.data))
def s944 (x : I) := (s943 x).set .x12 (high x.data 3)
def s945 (x : I) := withMem (s944 x) (before x.data 4)

def codes : List Instr := [
  Expr.instr .x12 (.sub .x18 .x16),
  Expr.instr .x12 (.srl .x17 .x12),
  .SD .x11 .x12 8]
theorem tables : OpeningStraight.Listed 942 codes := ⟨rfl,rfl,rfl,True.intro⟩
theorem spans (o : Oracle) (x : I) (nz : off x.data≠0) (cross : 64<off x.data+x.data.bits) : Contract o codes (m941 x) (s945 x) := by
  have h942 := OpeningLinear.register o (m941 x) .x12 (.sub .x18 .x16) ((64 : Word)-W (off x.data)) rfl
  have h943 := OpeningLinear.register o (s943 x) .x12 (.srl .x17 .x12) (high x.data 3) (OpeningRowOps.rightSub x.data 3 nz)
  have h944 := OpeningRowData.storeAs o (s944 x) .x11 .x12 8 (cell (atBit x.data 3)+1) (high x.data 3) (before x.data 4) (within x.data 3 (by decide)) (OpeningRowOps.following x.data 3) rfl (crosses x.data nz cross)
  exact LeafModel.combine h942 (LeafModel.combine h943 (LeafModel.combine h944 (LeafModel.empty _ _)))


def output (x : I) := if off x.data=0 then a957 x else if off x.data<35 then m941 x else s945 x

theorem run (o : Oracle) (x : I) (u : MachineState) (pc : u.pc=CommitBlocks.addr 907) (fit : Fits u (entry x)) :
    ∃ t n, n≤64 ∧ CommitExact.Segment o OpeningStraight.image n u t ∧ t.pc=CommitBlocks.addr 957 ∧
      Fits t (output x) := by
  have zstep := zero_branch o u 907 908 946 .x16 156 pc (by decide) rfl rfl rfl
    (W (off x.data)) (fit.registers _)
  have eqv : W (off x.data)=0 ↔ off x.data=0 := OpeningBranch.word_zero _
  simp only [eqv] at zstep
  unfold output
  by_cases z : off x.data=0
  · simp only [z,ite_true] at zstep ⊢
    obtain ⟨v,rv,pv,hv⟩ := OpeningLinear.block (spana o x z) (i:=946) (by decide) tablea
      (u.setPC _) rfl (fit.pc _)
    exact ⟨v,1+codea.length,by change 12≤64;decide,CommitExact.compose zstep rv,pv,hv⟩
  · simp only [z,ite_false] at zstep ⊢
    obtain ⟨v,rv,pv,hv⟩ := OpeningLinear.block (spanm o x z) (i:=908) (by decide) tablem (u.setPC _) rfl (fit.pc _)
    have branch := OpeningBranch.less o v .x16 .x12 941 957 64 pv (by decide) rfl rfl
      (off x.data) 35 (by unfold off;omega) (by decide) (hv.registers _) (hv.registers _)
    by_cases little : off x.data<35
    · simp only [little,ite_true] at branch ⊢
      exact ⟨_,1+codem.length+1,by change 35≤64;decide,CommitExact.compose (CommitExact.compose zstep rv) branch,rfl,hv.pc _⟩
    · simp only [little,ite_false] at branch ⊢
      have cross : 64<off x.data+x.data.bits := by change 64<off x.data+30;omega
      obtain ⟨w,rw,pw,hw⟩ := OpeningLinear.block (spans o x z cross) (i:=942) (by decide) tables
        (v.setPC _) rfl (hv.pc _)
      have jump := OpeningBranch.jump o w 945 957 48 pw (by decide) rfl rfl
      exact ⟨_,1+codem.length+1+codes.length+1,by change 39≤64;decide,CommitExact.compose (CommitExact.compose (CommitExact.compose
        (CommitExact.compose zstep rv) branch) rw) jump,rfl,hw.pc _⟩

theorem memory (x : I) : (output x).mem=before x.data 4 := by
  unfold output
  split
  · rfl
  · rename_i nz;split
    · rename_i little
      exact short x.data nz (by change off x.data+30≤64;omega)
    · rfl

def changed : List Reg := [.x5,.x6,.x7,.x11,.x12,.x13]

theorem frame (x : I) (r : Reg) (h : r∉changed) : (output x).reg r=(entry x).reg r := by
  unfold output
  split
  · cases r <;> first | rfl | exact False.elim (h (by decide))
  · split <;> cases r <;> first | rfl | exact False.elim (h (by decide))

end CommitGolfCandidate.Reconstruction.OpeningRow17
