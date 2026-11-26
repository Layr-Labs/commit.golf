import CommitGolfCandidate.ReconstructedOpeningRowOps

namespace CommitGolfCandidate.Reconstruction.OpeningRow15
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningOps OpeningCursor OpeningPut OpeningRowData
open TwoPermutationPrototype.RV64
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000

abbrev I := OpeningRowOps.Input 2303 33
def entry (x : I) : Model := ⟨fun
  | .x0 => W 0
  | .x11 => x.word 1
  | .x12 => x.word 0
  | .x14 => OpeningRowData.addr x.data 0
  | .x15 => x.word 3
  | .x16 => W (off x.data)
  | .x17 => x.word 2
  | .x18 => W 64
  | .x20 => W (x.root+2051)
  | .x25 => wordAddress OpeningPut.base
  | r => x.initial.reg r, x.initial.mem⟩

def a1083 (x : I) := withMem (entry x) (before x.data 1)
def a1084 (x : I) := (a1083 x).set .x12 (W (atBit x.data 1))
def a1085 (x : I) := (a1084 x).set .x12 (W (atBit x.data 1) >>> (3 : Nat))
def a1086 (x : I) := (a1085 x).set .x12 (OpeningRowData.addr x.data 1)
def a1087 (x : I) := withMem (a1086 x) (before x.data 2)
def a1088 (x : I) := (a1087 x).set .x11 (W (atBit x.data 2))
def a1089 (x : I) := (a1088 x).set .x11 (W (atBit x.data 2) >>> (3 : Nat))
def a1090 (x : I) := (a1089 x).set .x11 (OpeningRowData.addr x.data 2)
def a1091 (x : I) := withMem (a1090 x) (before x.data 3)
def a1092 (x : I) := (a1091 x).set .x11 (W (atBit x.data 3))
def a1093 (x : I) := (a1092 x).set .x11 (W (atBit x.data 3) >>> (3 : Nat))
def a1094 (x : I) := (a1093 x).set .x11 (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088))
def a1095 (x : I) := (a1094 x).set .x11 (OpeningRowData.addr x.data 3)
def a1096 (x : I) := withMem (a1095 x) (before x.data 4)

def codea : List Instr := [
  .SD .x14 .x12 0,
  Expr.instr .x12 (.addi .x20 316),
  Expr.instr .x12 (.srli .x12 3),
  Expr.instr .x12 (.add .x12 .x25),
  .SD .x12 .x11 0,
  Expr.instr .x11 (.addi .x20 380),
  Expr.instr .x11 (.srli .x11 3),
  Expr.instr .x11 (.add .x11 .x25),
  .SD .x11 .x17 0,
  Expr.instr .x11 (.addi .x20 444),
  Expr.instr .x11 (.srli .x11 3),
  Expr.instr .x11 (.andi .x11 4088),
  Expr.instr .x11 (.add .x11 .x25),
  .SD .x11 .x15 0]
theorem tablea : OpeningStraight.Listed 1082 codea := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem spana (o : Oracle) (x : I) (align : off x.data=0) : Contract o codea (entry x) (a1096 x) := by
  have h1082 := OpeningRowData.storeAs o (entry x) .x14 .x12 0 (cell (atBit x.data 0)) (x.word 0) (before x.data 1) (by have := within x.data 0 (by decide);omega) (OpeningRowOps.current x.data 0) rfl (OpeningRowData.aligned x.data 0 align)
  have h1083 := OpeningLinear.register o (a1083 x) .x12 (.addi .x20 316) (W (atBit x.data 1)) (OpeningRowOps.plusBit x.root 2051 316 2367 316 rfl rfl)
  have h1084 := OpeningLinear.register o (a1084 x) .x12 (.srli .x12 3) (W (atBit x.data 1) >>> (3 : Nat)) rfl
  have h1085 := OpeningLinear.register o (a1085 x) .x12 (.add .x12 .x25) (OpeningRowData.addr x.data 1) (OpeningRowOps.bare x.data 1 (by decide) align)
  have h1086 := OpeningRowData.storeAs o (a1086 x) .x12 .x11 0 (cell (atBit x.data 1)) (x.word 1) (before x.data 2) (by have := within x.data 1 (by decide);omega) (OpeningRowOps.current x.data 1) rfl (OpeningRowData.aligned x.data 1 align)
  have h1087 := OpeningLinear.register o (a1087 x) .x11 (.addi .x20 380) (W (atBit x.data 2)) (OpeningRowOps.plusBit x.root 2051 380 2431 380 rfl rfl)
  have h1088 := OpeningLinear.register o (a1088 x) .x11 (.srli .x11 3) (W (atBit x.data 2) >>> (3 : Nat)) rfl
  have h1089 := OpeningLinear.register o (a1089 x) .x11 (.add .x11 .x25) (OpeningRowData.addr x.data 2) (OpeningRowOps.bare x.data 2 (by decide) align)
  have h1090 := OpeningRowData.storeAs o (a1090 x) .x11 .x17 0 (cell (atBit x.data 2)) (x.word 2) (before x.data 3) (by have := within x.data 2 (by decide);omega) (OpeningRowOps.current x.data 2) rfl (OpeningRowData.aligned x.data 2 align)
  have h1091 := OpeningLinear.register o (a1091 x) .x11 (.addi .x20 444) (W (atBit x.data 3)) (OpeningRowOps.plusBit x.root 2051 444 2495 444 rfl rfl)
  have h1092 := OpeningLinear.register o (a1092 x) .x11 (.srli .x11 3) (W (atBit x.data 3) >>> (3 : Nat)) rfl
  have h1093 := OpeningLinear.register o (a1093 x) .x11 (.andi .x11 4088) (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h1094 := OpeningLinear.register o (a1094 x) .x11 (.add .x11 .x25) (OpeningRowData.addr x.data 3) (OpeningRowOps.pointer x.data 3 (by decide))
  have h1095 := OpeningRowData.storeAs o (a1095 x) .x11 .x15 0 (cell (atBit x.data 3)) (x.word 3) (before x.data 4) (by have := within x.data 3 (by decide);omega) (OpeningRowOps.current x.data 3) rfl (OpeningRowData.aligned x.data 3 align)
  exact LeafModel.combine h1082 (LeafModel.combine h1083 (LeafModel.combine h1084 (LeafModel.combine h1085 (LeafModel.combine h1086 (LeafModel.combine h1087 (LeafModel.combine h1088 (LeafModel.combine h1089 (LeafModel.combine h1090 (LeafModel.combine h1091 (LeafModel.combine h1092 (LeafModel.combine h1093 (LeafModel.combine h1094 (LeafModel.combine h1095 (LeafModel.empty _ _))))))))))))))

def m1042 (x : I) := (entry x).set .x13 (old x.data 0)
def m1043 (x : I) := (m1042 x).set .x5 (x.word 0 <<< off x.data)
def m1044 (x : I) := (m1043 x).set .x13 (merged x.data 0)
def m1045 (x : I) := (m1044 x).set .x5 (((0 : BitVec 32)-(W (off x.data)).truncate 32).signExtend 64)
def m1046 (x : I) := (m1045 x).set .x12 (high x.data 0)
def m1047 (x : I) := withMem (m1046 x) (tailMem x.data 0)
def m1048 (x : I) := withMem (m1047 x) (before x.data 1)
def m1049 (x : I) := (m1048 x).set .x12 (W (atBit x.data 1))
def m1050 (x : I) := (m1049 x).set .x12 (W (atBit x.data 1) >>> (3 : Nat))
def m1051 (x : I) := (m1050 x).set .x12 (((W (atBit x.data 1) >>> (3 : Nat)) &&& signExtend12 4088))
def m1052 (x : I) := (m1051 x).set .x12 (OpeningRowData.addr x.data 1)
def m1053 (x : I) := (m1052 x).set .x13 (old x.data 1)
def m1054 (x : I) := (m1053 x).set .x14 (x.word 1 <<< off x.data)
def m1055 (x : I) := (m1054 x).set .x13 (merged x.data 1)
def m1056 (x : I) := (m1055 x).set .x11 (high x.data 1)
def m1057 (x : I) := withMem (m1056 x) (tailMem x.data 1)
def m1058 (x : I) := withMem (m1057 x) (before x.data 2)
def m1059 (x : I) := (m1058 x).set .x11 (W (atBit x.data 2))
def m1060 (x : I) := (m1059 x).set .x11 (W (atBit x.data 2) >>> (3 : Nat))
def m1061 (x : I) := (m1060 x).set .x11 (((W (atBit x.data 2) >>> (3 : Nat)) &&& signExtend12 4088))
def m1062 (x : I) := (m1061 x).set .x11 (OpeningRowData.addr x.data 2)
def m1063 (x : I) := (m1062 x).set .x12 (old x.data 2)
def m1064 (x : I) := (m1063 x).set .x13 (x.word 2 <<< off x.data)
def m1065 (x : I) := (m1064 x).set .x12 (merged x.data 2)
def m1066 (x : I) := (m1065 x).set .x13 (high x.data 2)
def m1067 (x : I) := withMem (m1066 x) (tailMem x.data 2)
def m1068 (x : I) := withMem (m1067 x) (before x.data 3)
def m1069 (x : I) := (m1068 x).set .x11 (W (atBit x.data 3))
def m1070 (x : I) := (m1069 x).set .x11 (W (atBit x.data 3) >>> (3 : Nat))
def m1071 (x : I) := (m1070 x).set .x11 (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088))
def m1072 (x : I) := (m1071 x).set .x11 (OpeningRowData.addr x.data 3)
def m1073 (x : I) := (m1072 x).set .x12 (old x.data 3)
def m1074 (x : I) := (m1073 x).set .x13 (x.word 3 <<< off x.data)
def m1075 (x : I) := (m1074 x).set .x12 (merged x.data 3)
def m1076 (x : I) := withMem (m1075 x) (headMem x.data 3)
def m1077 (x : I) := (m1076 x).set .x12 (W 32)

def codem : List Instr := [
  .LD .x13 .x14 0,
  Expr.instr .x5 (.sll .x12 .x16),
  Expr.instr .x13 (.or .x13 .x5),
  Expr.instr .x5 (.subw .x0 .x16),
  Expr.instr .x12 (.srl .x12 .x5),
  .SD .x14 .x12 8,
  .SD .x14 .x13 0,
  Expr.instr .x12 (.addi .x20 316),
  Expr.instr .x12 (.srli .x12 3),
  Expr.instr .x12 (.andi .x12 4088),
  Expr.instr .x12 (.add .x12 .x25),
  .LD .x13 .x12 0,
  Expr.instr .x14 (.sll .x11 .x16),
  Expr.instr .x13 (.or .x13 .x14),
  Expr.instr .x11 (.srl .x11 .x5),
  .SD .x12 .x11 8,
  .SD .x12 .x13 0,
  Expr.instr .x11 (.addi .x20 380),
  Expr.instr .x11 (.srli .x11 3),
  Expr.instr .x11 (.andi .x11 4088),
  Expr.instr .x11 (.add .x11 .x25),
  .LD .x12 .x11 0,
  Expr.instr .x13 (.sll .x17 .x16),
  Expr.instr .x12 (.or .x12 .x13),
  Expr.instr .x13 (.srl .x17 .x5),
  .SD .x11 .x13 8,
  .SD .x11 .x12 0,
  Expr.instr .x11 (.addi .x20 444),
  Expr.instr .x11 (.srli .x11 3),
  Expr.instr .x11 (.andi .x11 4088),
  Expr.instr .x11 (.add .x11 .x25),
  .LD .x12 .x11 0,
  Expr.instr .x13 (.sll .x15 .x16),
  Expr.instr .x12 (.or .x12 .x13),
  .SD .x11 .x12 0,
  Expr.instr .x12 (.addi .x0 32)]
theorem tablem : OpeningStraight.Listed 1041 codem := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem spanm (o : Oracle) (x : I) (nz : off x.data≠0) : Contract o codem (entry x) (m1077 x) := by
  have h1041 := OpeningLinear.read o (entry x) .x13 .x14 0 (cell (atBit x.data 0)) (old x.data 0) (by have := within x.data 0 (by decide);omega) (OpeningRowOps.current x.data 0) rfl
  have h1042 := OpeningLinear.register o (m1042 x) .x5 (.sll .x12 .x16) (x.word 0 <<< off x.data) (OpeningRowOps.left x.data 0)
  have h1043 := OpeningLinear.register o (m1043 x) .x13 (.or .x13 .x5) (merged x.data 0) rfl
  have h1044 := OpeningLinear.register o (m1044 x) .x5 (.subw .x0 .x16) (((0 : BitVec 32)-(W (off x.data)).truncate 32).signExtend 64) rfl
  have h1045 := OpeningLinear.register o (m1045 x) .x12 (.srl .x12 .x5) (high x.data 0) (OpeningRowOps.rightNeg x.data 0 nz)
  have h1046 := OpeningRowData.storeAs o (m1046 x) .x14 .x12 8 (cell (atBit x.data 0)+1) (high x.data 0) (tailMem x.data 0) (within x.data 0 (by decide)) (OpeningRowOps.following x.data 0) rfl rfl
  have h1047 := OpeningRowData.storeAs o (m1047 x) .x14 .x13 0 (cell (atBit x.data 0)) (merged x.data 0) (before x.data 1) (by have := within x.data 0 (by decide);omega) (OpeningRowOps.current x.data 0) rfl (full x.data 0 (by decide) nz)
  have h1048 := OpeningLinear.register o (m1048 x) .x12 (.addi .x20 316) (W (atBit x.data 1)) (OpeningRowOps.plusBit x.root 2051 316 2367 316 rfl rfl)
  have h1049 := OpeningLinear.register o (m1049 x) .x12 (.srli .x12 3) (W (atBit x.data 1) >>> (3 : Nat)) rfl
  have h1050 := OpeningLinear.register o (m1050 x) .x12 (.andi .x12 4088) (((W (atBit x.data 1) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h1051 := OpeningLinear.register o (m1051 x) .x12 (.add .x12 .x25) (OpeningRowData.addr x.data 1) (OpeningRowOps.pointer x.data 1 (by decide))
  have h1052 := OpeningLinear.read o (m1052 x) .x13 .x12 0 (cell (atBit x.data 1)) (old x.data 1) (by have := within x.data 1 (by decide);omega) (OpeningRowOps.current x.data 1) rfl
  have h1053 := OpeningLinear.register o (m1053 x) .x14 (.sll .x11 .x16) (x.word 1 <<< off x.data) (OpeningRowOps.left x.data 1)
  have h1054 := OpeningLinear.register o (m1054 x) .x13 (.or .x13 .x14) (merged x.data 1) rfl
  have h1055 := OpeningLinear.register o (m1055 x) .x11 (.srl .x11 .x5) (high x.data 1) (OpeningRowOps.rightNeg x.data 1 nz)
  have h1056 := OpeningRowData.storeAs o (m1056 x) .x12 .x11 8 (cell (atBit x.data 1)+1) (high x.data 1) (tailMem x.data 1) (within x.data 1 (by decide)) (OpeningRowOps.following x.data 1) rfl rfl
  have h1057 := OpeningRowData.storeAs o (m1057 x) .x12 .x13 0 (cell (atBit x.data 1)) (merged x.data 1) (before x.data 2) (by have := within x.data 1 (by decide);omega) (OpeningRowOps.current x.data 1) rfl (full x.data 1 (by decide) nz)
  have h1058 := OpeningLinear.register o (m1058 x) .x11 (.addi .x20 380) (W (atBit x.data 2)) (OpeningRowOps.plusBit x.root 2051 380 2431 380 rfl rfl)
  have h1059 := OpeningLinear.register o (m1059 x) .x11 (.srli .x11 3) (W (atBit x.data 2) >>> (3 : Nat)) rfl
  have h1060 := OpeningLinear.register o (m1060 x) .x11 (.andi .x11 4088) (((W (atBit x.data 2) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h1061 := OpeningLinear.register o (m1061 x) .x11 (.add .x11 .x25) (OpeningRowData.addr x.data 2) (OpeningRowOps.pointer x.data 2 (by decide))
  have h1062 := OpeningLinear.read o (m1062 x) .x12 .x11 0 (cell (atBit x.data 2)) (old x.data 2) (by have := within x.data 2 (by decide);omega) (OpeningRowOps.current x.data 2) rfl
  have h1063 := OpeningLinear.register o (m1063 x) .x13 (.sll .x17 .x16) (x.word 2 <<< off x.data) (OpeningRowOps.left x.data 2)
  have h1064 := OpeningLinear.register o (m1064 x) .x12 (.or .x12 .x13) (merged x.data 2) rfl
  have h1065 := OpeningLinear.register o (m1065 x) .x13 (.srl .x17 .x5) (high x.data 2) (OpeningRowOps.rightNeg x.data 2 nz)
  have h1066 := OpeningRowData.storeAs o (m1066 x) .x11 .x13 8 (cell (atBit x.data 2)+1) (high x.data 2) (tailMem x.data 2) (within x.data 2 (by decide)) (OpeningRowOps.following x.data 2) rfl rfl
  have h1067 := OpeningRowData.storeAs o (m1067 x) .x11 .x12 0 (cell (atBit x.data 2)) (merged x.data 2) (before x.data 3) (by have := within x.data 2 (by decide);omega) (OpeningRowOps.current x.data 2) rfl (full x.data 2 (by decide) nz)
  have h1068 := OpeningLinear.register o (m1068 x) .x11 (.addi .x20 444) (W (atBit x.data 3)) (OpeningRowOps.plusBit x.root 2051 444 2495 444 rfl rfl)
  have h1069 := OpeningLinear.register o (m1069 x) .x11 (.srli .x11 3) (W (atBit x.data 3) >>> (3 : Nat)) rfl
  have h1070 := OpeningLinear.register o (m1070 x) .x11 (.andi .x11 4088) (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h1071 := OpeningLinear.register o (m1071 x) .x11 (.add .x11 .x25) (OpeningRowData.addr x.data 3) (OpeningRowOps.pointer x.data 3 (by decide))
  have h1072 := OpeningLinear.read o (m1072 x) .x12 .x11 0 (cell (atBit x.data 3)) (old x.data 3) (by have := within x.data 3 (by decide);omega) (OpeningRowOps.current x.data 3) rfl
  have h1073 := OpeningLinear.register o (m1073 x) .x13 (.sll .x15 .x16) (x.word 3 <<< off x.data) (OpeningRowOps.left x.data 3)
  have h1074 := OpeningLinear.register o (m1074 x) .x12 (.or .x12 .x13) (merged x.data 3) rfl
  have h1075 := OpeningRowData.storeAs o (m1075 x) .x11 .x12 0 (cell (atBit x.data 3)) (merged x.data 3) (headMem x.data 3) (by have := within x.data 3 (by decide);omega) (OpeningRowOps.current x.data 3) rfl rfl
  have h1076 := OpeningLinear.register o (m1076 x) .x12 (.addi .x0 32) (W 32) rfl
  exact LeafModel.combine h1041 (LeafModel.combine h1042 (LeafModel.combine h1043 (LeafModel.combine h1044 (LeafModel.combine h1045 (LeafModel.combine h1046 (LeafModel.combine h1047 (LeafModel.combine h1048 (LeafModel.combine h1049 (LeafModel.combine h1050 (LeafModel.combine h1051 (LeafModel.combine h1052 (LeafModel.combine h1053 (LeafModel.combine h1054 (LeafModel.combine h1055 (LeafModel.combine h1056 (LeafModel.combine h1057 (LeafModel.combine h1058 (LeafModel.combine h1059 (LeafModel.combine h1060 (LeafModel.combine h1061 (LeafModel.combine h1062 (LeafModel.combine h1063 (LeafModel.combine h1064 (LeafModel.combine h1065 (LeafModel.combine h1066 (LeafModel.combine h1067 (LeafModel.combine h1068 (LeafModel.combine h1069 (LeafModel.combine h1070 (LeafModel.combine h1071 (LeafModel.combine h1072 (LeafModel.combine h1073 (LeafModel.combine h1074 (LeafModel.combine h1075 (LeafModel.combine h1076 (LeafModel.empty _ _))))))))))))))))))))))))))))))))))))

def s1079 (x : I) := (m1077 x).set .x12 ((64 : Word)-W (off x.data))
def s1080 (x : I) := (s1079 x).set .x12 (high x.data 3)
def s1081 (x : I) := withMem (s1080 x) (before x.data 4)

def codes : List Instr := [
  Expr.instr .x12 (.sub .x18 .x16),
  Expr.instr .x12 (.srl .x15 .x12),
  .SD .x11 .x12 8]
theorem tables : OpeningStraight.Listed 1078 codes := ⟨rfl,rfl,rfl,True.intro⟩
theorem spans (o : Oracle) (x : I) (nz : off x.data≠0) (cross : 64<off x.data+x.data.bits) : Contract o codes (m1077 x) (s1081 x) := by
  have h1078 := OpeningLinear.register o (m1077 x) .x12 (.sub .x18 .x16) ((64 : Word)-W (off x.data)) rfl
  have h1079 := OpeningLinear.register o (s1079 x) .x12 (.srl .x15 .x12) (high x.data 3) (OpeningRowOps.rightSub x.data 3 nz)
  have h1080 := OpeningRowData.storeAs o (s1080 x) .x11 .x12 8 (cell (atBit x.data 3)+1) (high x.data 3) (before x.data 4) (within x.data 3 (by decide)) (OpeningRowOps.following x.data 3) rfl (crosses x.data nz cross)
  exact LeafModel.combine h1078 (LeafModel.combine h1079 (LeafModel.combine h1080 (LeafModel.empty _ _)))


def output (x : I) := if off x.data=0 then a1096 x else if off x.data<32 then m1077 x else s1081 x

theorem run (o : Oracle) (x : I) (u : MachineState) (pc : u.pc=CommitBlocks.addr 1040) (fit : Fits u (entry x)) :
    ∃ t n, n≤64 ∧ CommitExact.Segment o OpeningStraight.image n u t ∧ t.pc=CommitBlocks.addr 1096 ∧
      Fits t (output x) := by
  have zstep := zero_branch o u 1040 1041 1082 .x16 168 pc (by decide) rfl rfl rfl
    (W (off x.data)) (fit.registers _)
  have eqv : W (off x.data)=0 ↔ off x.data=0 := OpeningBranch.word_zero _
  simp only [eqv] at zstep
  unfold output
  by_cases z : off x.data=0
  · simp only [z,ite_true] at zstep ⊢
    obtain ⟨v,rv,pv,hv⟩ := OpeningLinear.block (spana o x z) (i:=1082) (by decide) tablea
      (u.setPC _) rfl (fit.pc _)
    exact ⟨v,1+codea.length,by change 15≤64;decide,CommitExact.compose zstep rv,pv,hv⟩
  · simp only [z,ite_false] at zstep ⊢
    obtain ⟨v,rv,pv,hv⟩ := OpeningLinear.block (spanm o x z) (i:=1041) (by decide) tablem (u.setPC _) rfl (fit.pc _)
    have branch := OpeningBranch.less o v .x16 .x12 1077 1096 76 pv (by decide) rfl rfl
      (off x.data) 32 (by unfold off;omega) (by decide) (hv.registers _) (hv.registers _)
    by_cases little : off x.data<32
    · simp only [little,ite_true] at branch ⊢
      exact ⟨_,1+codem.length+1,by change 38≤64;decide,CommitExact.compose (CommitExact.compose zstep rv) branch,rfl,hv.pc _⟩
    · simp only [little,ite_false] at branch ⊢
      have cross : 64<off x.data+x.data.bits := by change 64<off x.data+33;omega
      obtain ⟨w,rw,pw,hw⟩ := OpeningLinear.block (spans o x z cross) (i:=1078) (by decide) tables
        (v.setPC _) rfl (hv.pc _)
      have jump := OpeningBranch.jump o w 1081 1096 60 pw (by decide) rfl rfl
      exact ⟨_,1+codem.length+1+codes.length+1,by change 42≤64;decide,CommitExact.compose (CommitExact.compose (CommitExact.compose
        (CommitExact.compose zstep rv) branch) rw) jump,rfl,hw.pc _⟩

theorem memory (x : I) : (output x).mem=before x.data 4 := by
  unfold output
  split
  · rfl
  · rename_i nz;split
    · rename_i little
      exact short x.data nz (by change off x.data+33≤64;omega)
    · rfl

def changed : List Reg := [.x5,.x11,.x12,.x13,.x14]

theorem frame (x : I) (r : Reg) (h : r∉changed) : (output x).reg r=(entry x).reg r := by
  unfold output
  split
  · cases r <;> first | rfl | exact False.elim (h (by decide))
  · split <;> cases r <;> first | rfl | exact False.elim (h (by decide))

end CommitGolfCandidate.Reconstruction.OpeningRow15
