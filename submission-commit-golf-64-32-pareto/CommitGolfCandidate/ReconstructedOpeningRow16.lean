import CommitGolfCandidate.ReconstructedOpeningRowOps

namespace CommitGolfCandidate.Reconstruction.OpeningRow16
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningOps OpeningCursor OpeningPut OpeningRowData
open TwoPermutationPrototype.RV64
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000

abbrev I := OpeningRowOps.Input 2081 30
def entry (x : I) : Model := ⟨fun
  | .x0 => W 0
  | .x6 => x.word 2
  | .x11 => x.word 1
  | .x12 => x.word 0
  | .x14 => OpeningRowData.addr x.data 0
  | .x16 => W (off x.data)
  | .x17 => x.word 3
  | .x18 => W 64
  | .x20 => W (x.root+2051)
  | .x25 => wordAddress OpeningPut.base
  | r => x.initial.reg r, x.initial.mem⟩

def a1011 (x : I) := withMem (entry x) (before x.data 1)
def a1012 (x : I) := (a1011 x).set .x12 (W (atBit x.data 1))
def a1013 (x : I) := (a1012 x).set .x12 (W (atBit x.data 1) >>> (3 : Nat))
def a1014 (x : I) := (a1013 x).set .x12 (OpeningRowData.addr x.data 1)
def a1015 (x : I) := withMem (a1014 x) (before x.data 2)
def a1016 (x : I) := (a1015 x).set .x11 (W (atBit x.data 2))
def a1017 (x : I) := (a1016 x).set .x11 (W (atBit x.data 2) >>> (3 : Nat))
def a1018 (x : I) := (a1017 x).set .x11 (OpeningRowData.addr x.data 2)
def a1019 (x : I) := withMem (a1018 x) (before x.data 3)
def a1020 (x : I) := (a1019 x).set .x11 (W (atBit x.data 3))
def a1021 (x : I) := (a1020 x).set .x11 (W (atBit x.data 3) >>> (3 : Nat))
def a1022 (x : I) := (a1021 x).set .x11 (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088))
def a1023 (x : I) := (a1022 x).set .x11 (OpeningRowData.addr x.data 3)
def a1024 (x : I) := withMem (a1023 x) (before x.data 4)

def codea : List Instr := [
  .SD .x14 .x12 0,
  Expr.instr .x12 (.addi .x20 94),
  Expr.instr .x12 (.srli .x12 3),
  Expr.instr .x12 (.add .x12 .x25),
  .SD .x12 .x11 0,
  Expr.instr .x11 (.addi .x20 158),
  Expr.instr .x11 (.srli .x11 3),
  Expr.instr .x11 (.add .x11 .x25),
  .SD .x11 .x6 0,
  Expr.instr .x11 (.addi .x20 222),
  Expr.instr .x11 (.srli .x11 3),
  Expr.instr .x11 (.andi .x11 4088),
  Expr.instr .x11 (.add .x11 .x25),
  .SD .x11 .x17 0]
theorem tablea : OpeningStraight.Listed 1010 codea := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem spana (o : Oracle) (x : I) (align : off x.data=0) : Contract o codea (entry x) (a1024 x) := by
  have h1010 := OpeningRowData.storeAs o (entry x) .x14 .x12 0 (cell (atBit x.data 0)) (x.word 0) (before x.data 1) (by have := within x.data 0 (by decide);omega) (OpeningRowOps.current x.data 0) rfl (OpeningRowData.aligned x.data 0 align)
  have h1011 := OpeningLinear.register o (a1011 x) .x12 (.addi .x20 94) (W (atBit x.data 1)) (OpeningRowOps.plusBit x.root 2051 94 2145 94 rfl rfl)
  have h1012 := OpeningLinear.register o (a1012 x) .x12 (.srli .x12 3) (W (atBit x.data 1) >>> (3 : Nat)) rfl
  have h1013 := OpeningLinear.register o (a1013 x) .x12 (.add .x12 .x25) (OpeningRowData.addr x.data 1) (OpeningRowOps.bare x.data 1 (by decide) align)
  have h1014 := OpeningRowData.storeAs o (a1014 x) .x12 .x11 0 (cell (atBit x.data 1)) (x.word 1) (before x.data 2) (by have := within x.data 1 (by decide);omega) (OpeningRowOps.current x.data 1) rfl (OpeningRowData.aligned x.data 1 align)
  have h1015 := OpeningLinear.register o (a1015 x) .x11 (.addi .x20 158) (W (atBit x.data 2)) (OpeningRowOps.plusBit x.root 2051 158 2209 158 rfl rfl)
  have h1016 := OpeningLinear.register o (a1016 x) .x11 (.srli .x11 3) (W (atBit x.data 2) >>> (3 : Nat)) rfl
  have h1017 := OpeningLinear.register o (a1017 x) .x11 (.add .x11 .x25) (OpeningRowData.addr x.data 2) (OpeningRowOps.bare x.data 2 (by decide) align)
  have h1018 := OpeningRowData.storeAs o (a1018 x) .x11 .x6 0 (cell (atBit x.data 2)) (x.word 2) (before x.data 3) (by have := within x.data 2 (by decide);omega) (OpeningRowOps.current x.data 2) rfl (OpeningRowData.aligned x.data 2 align)
  have h1019 := OpeningLinear.register o (a1019 x) .x11 (.addi .x20 222) (W (atBit x.data 3)) (OpeningRowOps.plusBit x.root 2051 222 2273 222 rfl rfl)
  have h1020 := OpeningLinear.register o (a1020 x) .x11 (.srli .x11 3) (W (atBit x.data 3) >>> (3 : Nat)) rfl
  have h1021 := OpeningLinear.register o (a1021 x) .x11 (.andi .x11 4088) (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h1022 := OpeningLinear.register o (a1022 x) .x11 (.add .x11 .x25) (OpeningRowData.addr x.data 3) (OpeningRowOps.pointer x.data 3 (by decide))
  have h1023 := OpeningRowData.storeAs o (a1023 x) .x11 .x17 0 (cell (atBit x.data 3)) (x.word 3) (before x.data 4) (by have := within x.data 3 (by decide);omega) (OpeningRowOps.current x.data 3) rfl (OpeningRowData.aligned x.data 3 align)
  exact LeafModel.combine h1010 (LeafModel.combine h1011 (LeafModel.combine h1012 (LeafModel.combine h1013 (LeafModel.combine h1014 (LeafModel.combine h1015 (LeafModel.combine h1016 (LeafModel.combine h1017 (LeafModel.combine h1018 (LeafModel.combine h1019 (LeafModel.combine h1020 (LeafModel.combine h1021 (LeafModel.combine h1022 (LeafModel.combine h1023 (LeafModel.empty _ _))))))))))))))

def m970 (x : I) := (entry x).set .x13 (old x.data 0)
def m971 (x : I) := (m970 x).set .x5 (x.word 0 <<< off x.data)
def m972 (x : I) := (m971 x).set .x13 (merged x.data 0)
def m973 (x : I) := (m972 x).set .x5 (((0 : BitVec 32)-(W (off x.data)).truncate 32).signExtend 64)
def m974 (x : I) := (m973 x).set .x12 (high x.data 0)
def m975 (x : I) := withMem (m974 x) (tailMem x.data 0)
def m976 (x : I) := withMem (m975 x) (before x.data 1)
def m977 (x : I) := (m976 x).set .x12 (W (atBit x.data 1))
def m978 (x : I) := (m977 x).set .x12 (W (atBit x.data 1) >>> (3 : Nat))
def m979 (x : I) := (m978 x).set .x12 (((W (atBit x.data 1) >>> (3 : Nat)) &&& signExtend12 4088))
def m980 (x : I) := (m979 x).set .x12 (OpeningRowData.addr x.data 1)
def m981 (x : I) := (m980 x).set .x13 (old x.data 1)
def m982 (x : I) := (m981 x).set .x14 (x.word 1 <<< off x.data)
def m983 (x : I) := (m982 x).set .x13 (merged x.data 1)
def m984 (x : I) := (m983 x).set .x11 (high x.data 1)
def m985 (x : I) := withMem (m984 x) (tailMem x.data 1)
def m986 (x : I) := withMem (m985 x) (before x.data 2)
def m987 (x : I) := (m986 x).set .x11 (W (atBit x.data 2))
def m988 (x : I) := (m987 x).set .x11 (W (atBit x.data 2) >>> (3 : Nat))
def m989 (x : I) := (m988 x).set .x11 (((W (atBit x.data 2) >>> (3 : Nat)) &&& signExtend12 4088))
def m990 (x : I) := (m989 x).set .x11 (OpeningRowData.addr x.data 2)
def m991 (x : I) := (m990 x).set .x12 (old x.data 2)
def m992 (x : I) := (m991 x).set .x13 (x.word 2 <<< off x.data)
def m993 (x : I) := (m992 x).set .x12 (merged x.data 2)
def m994 (x : I) := (m993 x).set .x13 (high x.data 2)
def m995 (x : I) := withMem (m994 x) (tailMem x.data 2)
def m996 (x : I) := withMem (m995 x) (before x.data 3)
def m997 (x : I) := (m996 x).set .x11 (W (atBit x.data 3))
def m998 (x : I) := (m997 x).set .x11 (W (atBit x.data 3) >>> (3 : Nat))
def m999 (x : I) := (m998 x).set .x11 (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088))
def m1000 (x : I) := (m999 x).set .x11 (OpeningRowData.addr x.data 3)
def m1001 (x : I) := (m1000 x).set .x12 (old x.data 3)
def m1002 (x : I) := (m1001 x).set .x13 (x.word 3 <<< off x.data)
def m1003 (x : I) := (m1002 x).set .x12 (merged x.data 3)
def m1004 (x : I) := withMem (m1003 x) (headMem x.data 3)
def m1005 (x : I) := (m1004 x).set .x12 (W 35)

def codem : List Instr := [
  .LD .x13 .x14 0,
  Expr.instr .x5 (.sll .x12 .x16),
  Expr.instr .x13 (.or .x13 .x5),
  Expr.instr .x5 (.subw .x0 .x16),
  Expr.instr .x12 (.srl .x12 .x5),
  .SD .x14 .x12 8,
  .SD .x14 .x13 0,
  Expr.instr .x12 (.addi .x20 94),
  Expr.instr .x12 (.srli .x12 3),
  Expr.instr .x12 (.andi .x12 4088),
  Expr.instr .x12 (.add .x12 .x25),
  .LD .x13 .x12 0,
  Expr.instr .x14 (.sll .x11 .x16),
  Expr.instr .x13 (.or .x13 .x14),
  Expr.instr .x11 (.srl .x11 .x5),
  .SD .x12 .x11 8,
  .SD .x12 .x13 0,
  Expr.instr .x11 (.addi .x20 158),
  Expr.instr .x11 (.srli .x11 3),
  Expr.instr .x11 (.andi .x11 4088),
  Expr.instr .x11 (.add .x11 .x25),
  .LD .x12 .x11 0,
  Expr.instr .x13 (.sll .x6 .x16),
  Expr.instr .x12 (.or .x12 .x13),
  Expr.instr .x13 (.srl .x6 .x5),
  .SD .x11 .x13 8,
  .SD .x11 .x12 0,
  Expr.instr .x11 (.addi .x20 222),
  Expr.instr .x11 (.srli .x11 3),
  Expr.instr .x11 (.andi .x11 4088),
  Expr.instr .x11 (.add .x11 .x25),
  .LD .x12 .x11 0,
  Expr.instr .x13 (.sll .x17 .x16),
  Expr.instr .x12 (.or .x12 .x13),
  .SD .x11 .x12 0,
  Expr.instr .x12 (.addi .x0 35)]
theorem tablem : OpeningStraight.Listed 969 codem := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem spanm (o : Oracle) (x : I) (nz : off x.data≠0) : Contract o codem (entry x) (m1005 x) := by
  have h969 := OpeningLinear.read o (entry x) .x13 .x14 0 (cell (atBit x.data 0)) (old x.data 0) (by have := within x.data 0 (by decide);omega) (OpeningRowOps.current x.data 0) rfl
  have h970 := OpeningLinear.register o (m970 x) .x5 (.sll .x12 .x16) (x.word 0 <<< off x.data) (OpeningRowOps.left x.data 0)
  have h971 := OpeningLinear.register o (m971 x) .x13 (.or .x13 .x5) (merged x.data 0) rfl
  have h972 := OpeningLinear.register o (m972 x) .x5 (.subw .x0 .x16) (((0 : BitVec 32)-(W (off x.data)).truncate 32).signExtend 64) rfl
  have h973 := OpeningLinear.register o (m973 x) .x12 (.srl .x12 .x5) (high x.data 0) (OpeningRowOps.rightNeg x.data 0 nz)
  have h974 := OpeningRowData.storeAs o (m974 x) .x14 .x12 8 (cell (atBit x.data 0)+1) (high x.data 0) (tailMem x.data 0) (within x.data 0 (by decide)) (OpeningRowOps.following x.data 0) rfl rfl
  have h975 := OpeningRowData.storeAs o (m975 x) .x14 .x13 0 (cell (atBit x.data 0)) (merged x.data 0) (before x.data 1) (by have := within x.data 0 (by decide);omega) (OpeningRowOps.current x.data 0) rfl (full x.data 0 (by decide) nz)
  have h976 := OpeningLinear.register o (m976 x) .x12 (.addi .x20 94) (W (atBit x.data 1)) (OpeningRowOps.plusBit x.root 2051 94 2145 94 rfl rfl)
  have h977 := OpeningLinear.register o (m977 x) .x12 (.srli .x12 3) (W (atBit x.data 1) >>> (3 : Nat)) rfl
  have h978 := OpeningLinear.register o (m978 x) .x12 (.andi .x12 4088) (((W (atBit x.data 1) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h979 := OpeningLinear.register o (m979 x) .x12 (.add .x12 .x25) (OpeningRowData.addr x.data 1) (OpeningRowOps.pointer x.data 1 (by decide))
  have h980 := OpeningLinear.read o (m980 x) .x13 .x12 0 (cell (atBit x.data 1)) (old x.data 1) (by have := within x.data 1 (by decide);omega) (OpeningRowOps.current x.data 1) rfl
  have h981 := OpeningLinear.register o (m981 x) .x14 (.sll .x11 .x16) (x.word 1 <<< off x.data) (OpeningRowOps.left x.data 1)
  have h982 := OpeningLinear.register o (m982 x) .x13 (.or .x13 .x14) (merged x.data 1) rfl
  have h983 := OpeningLinear.register o (m983 x) .x11 (.srl .x11 .x5) (high x.data 1) (OpeningRowOps.rightNeg x.data 1 nz)
  have h984 := OpeningRowData.storeAs o (m984 x) .x12 .x11 8 (cell (atBit x.data 1)+1) (high x.data 1) (tailMem x.data 1) (within x.data 1 (by decide)) (OpeningRowOps.following x.data 1) rfl rfl
  have h985 := OpeningRowData.storeAs o (m985 x) .x12 .x13 0 (cell (atBit x.data 1)) (merged x.data 1) (before x.data 2) (by have := within x.data 1 (by decide);omega) (OpeningRowOps.current x.data 1) rfl (full x.data 1 (by decide) nz)
  have h986 := OpeningLinear.register o (m986 x) .x11 (.addi .x20 158) (W (atBit x.data 2)) (OpeningRowOps.plusBit x.root 2051 158 2209 158 rfl rfl)
  have h987 := OpeningLinear.register o (m987 x) .x11 (.srli .x11 3) (W (atBit x.data 2) >>> (3 : Nat)) rfl
  have h988 := OpeningLinear.register o (m988 x) .x11 (.andi .x11 4088) (((W (atBit x.data 2) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h989 := OpeningLinear.register o (m989 x) .x11 (.add .x11 .x25) (OpeningRowData.addr x.data 2) (OpeningRowOps.pointer x.data 2 (by decide))
  have h990 := OpeningLinear.read o (m990 x) .x12 .x11 0 (cell (atBit x.data 2)) (old x.data 2) (by have := within x.data 2 (by decide);omega) (OpeningRowOps.current x.data 2) rfl
  have h991 := OpeningLinear.register o (m991 x) .x13 (.sll .x6 .x16) (x.word 2 <<< off x.data) (OpeningRowOps.left x.data 2)
  have h992 := OpeningLinear.register o (m992 x) .x12 (.or .x12 .x13) (merged x.data 2) rfl
  have h993 := OpeningLinear.register o (m993 x) .x13 (.srl .x6 .x5) (high x.data 2) (OpeningRowOps.rightNeg x.data 2 nz)
  have h994 := OpeningRowData.storeAs o (m994 x) .x11 .x13 8 (cell (atBit x.data 2)+1) (high x.data 2) (tailMem x.data 2) (within x.data 2 (by decide)) (OpeningRowOps.following x.data 2) rfl rfl
  have h995 := OpeningRowData.storeAs o (m995 x) .x11 .x12 0 (cell (atBit x.data 2)) (merged x.data 2) (before x.data 3) (by have := within x.data 2 (by decide);omega) (OpeningRowOps.current x.data 2) rfl (full x.data 2 (by decide) nz)
  have h996 := OpeningLinear.register o (m996 x) .x11 (.addi .x20 222) (W (atBit x.data 3)) (OpeningRowOps.plusBit x.root 2051 222 2273 222 rfl rfl)
  have h997 := OpeningLinear.register o (m997 x) .x11 (.srli .x11 3) (W (atBit x.data 3) >>> (3 : Nat)) rfl
  have h998 := OpeningLinear.register o (m998 x) .x11 (.andi .x11 4088) (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h999 := OpeningLinear.register o (m999 x) .x11 (.add .x11 .x25) (OpeningRowData.addr x.data 3) (OpeningRowOps.pointer x.data 3 (by decide))
  have h1000 := OpeningLinear.read o (m1000 x) .x12 .x11 0 (cell (atBit x.data 3)) (old x.data 3) (by have := within x.data 3 (by decide);omega) (OpeningRowOps.current x.data 3) rfl
  have h1001 := OpeningLinear.register o (m1001 x) .x13 (.sll .x17 .x16) (x.word 3 <<< off x.data) (OpeningRowOps.left x.data 3)
  have h1002 := OpeningLinear.register o (m1002 x) .x12 (.or .x12 .x13) (merged x.data 3) rfl
  have h1003 := OpeningRowData.storeAs o (m1003 x) .x11 .x12 0 (cell (atBit x.data 3)) (merged x.data 3) (headMem x.data 3) (by have := within x.data 3 (by decide);omega) (OpeningRowOps.current x.data 3) rfl rfl
  have h1004 := OpeningLinear.register o (m1004 x) .x12 (.addi .x0 35) (W 35) rfl
  exact LeafModel.combine h969 (LeafModel.combine h970 (LeafModel.combine h971 (LeafModel.combine h972 (LeafModel.combine h973 (LeafModel.combine h974 (LeafModel.combine h975 (LeafModel.combine h976 (LeafModel.combine h977 (LeafModel.combine h978 (LeafModel.combine h979 (LeafModel.combine h980 (LeafModel.combine h981 (LeafModel.combine h982 (LeafModel.combine h983 (LeafModel.combine h984 (LeafModel.combine h985 (LeafModel.combine h986 (LeafModel.combine h987 (LeafModel.combine h988 (LeafModel.combine h989 (LeafModel.combine h990 (LeafModel.combine h991 (LeafModel.combine h992 (LeafModel.combine h993 (LeafModel.combine h994 (LeafModel.combine h995 (LeafModel.combine h996 (LeafModel.combine h997 (LeafModel.combine h998 (LeafModel.combine h999 (LeafModel.combine h1000 (LeafModel.combine h1001 (LeafModel.combine h1002 (LeafModel.combine h1003 (LeafModel.combine h1004 (LeafModel.empty _ _))))))))))))))))))))))))))))))))))))

def s1007 (x : I) := (m1005 x).set .x12 ((64 : Word)-W (off x.data))
def s1008 (x : I) := (s1007 x).set .x12 (high x.data 3)
def s1009 (x : I) := withMem (s1008 x) (before x.data 4)

def codes : List Instr := [
  Expr.instr .x12 (.sub .x18 .x16),
  Expr.instr .x12 (.srl .x17 .x12),
  .SD .x11 .x12 8]
theorem tables : OpeningStraight.Listed 1006 codes := ⟨rfl,rfl,rfl,True.intro⟩
theorem spans (o : Oracle) (x : I) (nz : off x.data≠0) (cross : 64<off x.data+x.data.bits) : Contract o codes (m1005 x) (s1009 x) := by
  have h1006 := OpeningLinear.register o (m1005 x) .x12 (.sub .x18 .x16) ((64 : Word)-W (off x.data)) rfl
  have h1007 := OpeningLinear.register o (s1007 x) .x12 (.srl .x17 .x12) (high x.data 3) (OpeningRowOps.rightSub x.data 3 nz)
  have h1008 := OpeningRowData.storeAs o (s1008 x) .x11 .x12 8 (cell (atBit x.data 3)+1) (high x.data 3) (before x.data 4) (within x.data 3 (by decide)) (OpeningRowOps.following x.data 3) rfl (crosses x.data nz cross)
  exact LeafModel.combine h1006 (LeafModel.combine h1007 (LeafModel.combine h1008 (LeafModel.empty _ _)))


def output (x : I) := if off x.data=0 then a1024 x else if off x.data<35 then m1005 x else s1009 x

theorem run (o : Oracle) (x : I) (u : MachineState) (pc : u.pc=CommitBlocks.addr 968) (fit : Fits u (entry x)) :
    ∃ t n, n≤64 ∧ CommitExact.Segment o OpeningStraight.image n u t ∧ t.pc=CommitBlocks.addr 1024 ∧
      Fits t (output x) := by
  have zstep := zero_branch o u 968 969 1010 .x16 168 pc (by decide) rfl rfl rfl
    (W (off x.data)) (fit.registers _)
  have eqv : W (off x.data)=0 ↔ off x.data=0 := OpeningBranch.word_zero _
  simp only [eqv] at zstep
  unfold output
  by_cases z : off x.data=0
  · simp only [z,ite_true] at zstep ⊢
    obtain ⟨v,rv,pv,hv⟩ := OpeningLinear.block (spana o x z) (i:=1010) (by decide) tablea
      (u.setPC _) rfl (fit.pc _)
    exact ⟨v,1+codea.length,by change 15≤64;decide,CommitExact.compose zstep rv,pv,hv⟩
  · simp only [z,ite_false] at zstep ⊢
    obtain ⟨v,rv,pv,hv⟩ := OpeningLinear.block (spanm o x z) (i:=969) (by decide) tablem (u.setPC _) rfl (fit.pc _)
    have branch := OpeningBranch.less o v .x16 .x12 1005 1024 76 pv (by decide) rfl rfl
      (off x.data) 35 (by unfold off;omega) (by decide) (hv.registers _) (hv.registers _)
    by_cases little : off x.data<35
    · simp only [little,ite_true] at branch ⊢
      exact ⟨_,1+codem.length+1,by change 38≤64;decide,CommitExact.compose (CommitExact.compose zstep rv) branch,rfl,hv.pc _⟩
    · simp only [little,ite_false] at branch ⊢
      have cross : 64<off x.data+x.data.bits := by change 64<off x.data+30;omega
      obtain ⟨w,rw,pw,hw⟩ := OpeningLinear.block (spans o x z cross) (i:=1006) (by decide) tables
        (v.setPC _) rfl (hv.pc _)
      have jump := OpeningBranch.jump o w 1009 1024 60 pw (by decide) rfl rfl
      exact ⟨_,1+codem.length+1+codes.length+1,by change 42≤64;decide,CommitExact.compose (CommitExact.compose (CommitExact.compose
        (CommitExact.compose zstep rv) branch) rw) jump,rfl,hw.pc _⟩

theorem memory (x : I) : (output x).mem=before x.data 4 := by
  unfold output
  split
  · rfl
  · rename_i nz;split
    · rename_i little
      exact short x.data nz (by change off x.data+30≤64;omega)
    · rfl

def changed : List Reg := [.x5,.x11,.x12,.x13,.x14]

theorem frame (x : I) (r : Reg) (h : r∉changed) : (output x).reg r=(entry x).reg r := by
  unfold output
  split
  · cases r <;> first | rfl | exact False.elim (h (by decide))
  · split <;> cases r <;> first | rfl | exact False.elim (h (by decide))

end CommitGolfCandidate.Reconstruction.OpeningRow16
