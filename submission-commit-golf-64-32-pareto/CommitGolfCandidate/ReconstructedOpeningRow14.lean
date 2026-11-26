import CommitGolfCandidate.ReconstructedOpeningRowOps

namespace CommitGolfCandidate.Reconstruction.OpeningRow14
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningOps OpeningCursor OpeningPut OpeningRowData
open TwoPermutationPrototype.RV64
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000

abbrev I := OpeningRowOps.Input 2528 29
def entry (x : I) : Model := ⟨fun
  | .x0 => W 0
  | .x7 => W 36
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

def a1151 (x : I) := withMem (entry x) (before x.data 1)
def a1152 (x : I) := (a1151 x).set .x12 (W (atBit x.data 1))
def a1153 (x : I) := (a1152 x).set .x12 (W (atBit x.data 1) >>> (3 : Nat))
def a1154 (x : I) := (a1153 x).set .x12 (OpeningRowData.addr x.data 1)
def a1155 (x : I) := withMem (a1154 x) (before x.data 2)
def a1156 (x : I) := (a1155 x).set .x11 (W (atBit x.data 2))
def a1157 (x : I) := (a1156 x).set .x11 (W (atBit x.data 2) >>> (3 : Nat))
def a1158 (x : I) := (a1157 x).set .x11 (OpeningRowData.addr x.data 2)
def a1159 (x : I) := withMem (a1158 x) (before x.data 3)
def a1160 (x : I) := (a1159 x).set .x11 (W (atBit x.data 3))
def a1161 (x : I) := (a1160 x).set .x11 (W (atBit x.data 3) >>> (3 : Nat))
def a1162 (x : I) := (a1161 x).set .x11 (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088))
def a1163 (x : I) := (a1162 x).set .x11 (OpeningRowData.addr x.data 3)
def a1164 (x : I) := withMem (a1163 x) (before x.data 4)

def codea : List Instr := [
  .SD .x14 .x12 0,
  Expr.instr .x12 (.addi .x20 541),
  Expr.instr .x12 (.srli .x12 3),
  Expr.instr .x12 (.add .x12 .x25),
  .SD .x12 .x11 0,
  Expr.instr .x11 (.addi .x20 605),
  Expr.instr .x11 (.srli .x11 3),
  Expr.instr .x11 (.add .x11 .x25),
  .SD .x11 .x17 0,
  Expr.instr .x11 (.addi .x20 669),
  Expr.instr .x11 (.srli .x11 3),
  Expr.instr .x11 (.andi .x11 4088),
  Expr.instr .x11 (.add .x11 .x25),
  .SD .x11 .x15 0]
theorem tablea : OpeningStraight.Listed 1150 codea := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem spana (o : Oracle) (x : I) (align : off x.data=0) : Contract o codea (entry x) (a1164 x) := by
  have h1150 := OpeningRowData.storeAs o (entry x) .x14 .x12 0 (cell (atBit x.data 0)) (x.word 0) (before x.data 1) (by have := within x.data 0 (by decide);omega) (OpeningRowOps.current x.data 0) rfl (OpeningRowData.aligned x.data 0 align)
  have h1151 := OpeningLinear.register o (a1151 x) .x12 (.addi .x20 541) (W (atBit x.data 1)) (OpeningRowOps.plusBit x.root 2051 541 2592 541 rfl rfl)
  have h1152 := OpeningLinear.register o (a1152 x) .x12 (.srli .x12 3) (W (atBit x.data 1) >>> (3 : Nat)) rfl
  have h1153 := OpeningLinear.register o (a1153 x) .x12 (.add .x12 .x25) (OpeningRowData.addr x.data 1) (OpeningRowOps.bare x.data 1 (by decide) align)
  have h1154 := OpeningRowData.storeAs o (a1154 x) .x12 .x11 0 (cell (atBit x.data 1)) (x.word 1) (before x.data 2) (by have := within x.data 1 (by decide);omega) (OpeningRowOps.current x.data 1) rfl (OpeningRowData.aligned x.data 1 align)
  have h1155 := OpeningLinear.register o (a1155 x) .x11 (.addi .x20 605) (W (atBit x.data 2)) (OpeningRowOps.plusBit x.root 2051 605 2656 605 rfl rfl)
  have h1156 := OpeningLinear.register o (a1156 x) .x11 (.srli .x11 3) (W (atBit x.data 2) >>> (3 : Nat)) rfl
  have h1157 := OpeningLinear.register o (a1157 x) .x11 (.add .x11 .x25) (OpeningRowData.addr x.data 2) (OpeningRowOps.bare x.data 2 (by decide) align)
  have h1158 := OpeningRowData.storeAs o (a1158 x) .x11 .x17 0 (cell (atBit x.data 2)) (x.word 2) (before x.data 3) (by have := within x.data 2 (by decide);omega) (OpeningRowOps.current x.data 2) rfl (OpeningRowData.aligned x.data 2 align)
  have h1159 := OpeningLinear.register o (a1159 x) .x11 (.addi .x20 669) (W (atBit x.data 3)) (OpeningRowOps.plusBit x.root 2051 669 2720 669 rfl rfl)
  have h1160 := OpeningLinear.register o (a1160 x) .x11 (.srli .x11 3) (W (atBit x.data 3) >>> (3 : Nat)) rfl
  have h1161 := OpeningLinear.register o (a1161 x) .x11 (.andi .x11 4088) (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h1162 := OpeningLinear.register o (a1162 x) .x11 (.add .x11 .x25) (OpeningRowData.addr x.data 3) (OpeningRowOps.pointer x.data 3 (by decide))
  have h1163 := OpeningRowData.storeAs o (a1163 x) .x11 .x15 0 (cell (atBit x.data 3)) (x.word 3) (before x.data 4) (by have := within x.data 3 (by decide);omega) (OpeningRowOps.current x.data 3) rfl (OpeningRowData.aligned x.data 3 align)
  exact LeafModel.combine h1150 (LeafModel.combine h1151 (LeafModel.combine h1152 (LeafModel.combine h1153 (LeafModel.combine h1154 (LeafModel.combine h1155 (LeafModel.combine h1156 (LeafModel.combine h1157 (LeafModel.combine h1158 (LeafModel.combine h1159 (LeafModel.combine h1160 (LeafModel.combine h1161 (LeafModel.combine h1162 (LeafModel.combine h1163 (LeafModel.empty _ _))))))))))))))

def m1111 (x : I) := (entry x).set .x13 (old x.data 0)
def m1112 (x : I) := (m1111 x).set .x5 (x.word 0 <<< off x.data)
def m1113 (x : I) := (m1112 x).set .x13 (merged x.data 0)
def m1114 (x : I) := (m1113 x).set .x5 (((0 : BitVec 32)-(W (off x.data)).truncate 32).signExtend 64)
def m1115 (x : I) := (m1114 x).set .x12 (high x.data 0)
def m1116 (x : I) := withMem (m1115 x) (tailMem x.data 0)
def m1117 (x : I) := withMem (m1116 x) (before x.data 1)
def m1118 (x : I) := (m1117 x).set .x12 (W (atBit x.data 1))
def m1119 (x : I) := (m1118 x).set .x12 (W (atBit x.data 1) >>> (3 : Nat))
def m1120 (x : I) := (m1119 x).set .x12 (((W (atBit x.data 1) >>> (3 : Nat)) &&& signExtend12 4088))
def m1121 (x : I) := (m1120 x).set .x12 (OpeningRowData.addr x.data 1)
def m1122 (x : I) := (m1121 x).set .x13 (old x.data 1)
def m1123 (x : I) := (m1122 x).set .x14 (x.word 1 <<< off x.data)
def m1124 (x : I) := (m1123 x).set .x13 (merged x.data 1)
def m1125 (x : I) := (m1124 x).set .x11 (high x.data 1)
def m1126 (x : I) := withMem (m1125 x) (tailMem x.data 1)
def m1127 (x : I) := withMem (m1126 x) (before x.data 2)
def m1128 (x : I) := (m1127 x).set .x11 (W (atBit x.data 2))
def m1129 (x : I) := (m1128 x).set .x11 (W (atBit x.data 2) >>> (3 : Nat))
def m1130 (x : I) := (m1129 x).set .x11 (((W (atBit x.data 2) >>> (3 : Nat)) &&& signExtend12 4088))
def m1131 (x : I) := (m1130 x).set .x11 (OpeningRowData.addr x.data 2)
def m1132 (x : I) := (m1131 x).set .x12 (old x.data 2)
def m1133 (x : I) := (m1132 x).set .x13 (x.word 2 <<< off x.data)
def m1134 (x : I) := (m1133 x).set .x12 (merged x.data 2)
def m1135 (x : I) := (m1134 x).set .x13 (high x.data 2)
def m1136 (x : I) := withMem (m1135 x) (tailMem x.data 2)
def m1137 (x : I) := withMem (m1136 x) (before x.data 3)
def m1138 (x : I) := (m1137 x).set .x11 (W (atBit x.data 3))
def m1139 (x : I) := (m1138 x).set .x11 (W (atBit x.data 3) >>> (3 : Nat))
def m1140 (x : I) := (m1139 x).set .x11 (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088))
def m1141 (x : I) := (m1140 x).set .x11 (OpeningRowData.addr x.data 3)
def m1142 (x : I) := (m1141 x).set .x12 (old x.data 3)
def m1143 (x : I) := (m1142 x).set .x13 (x.word 3 <<< off x.data)
def m1144 (x : I) := (m1143 x).set .x12 (merged x.data 3)
def m1145 (x : I) := withMem (m1144 x) (headMem x.data 3)

def codem : List Instr := [
  .LD .x13 .x14 0,
  Expr.instr .x5 (.sll .x12 .x16),
  Expr.instr .x13 (.or .x13 .x5),
  Expr.instr .x5 (.subw .x0 .x16),
  Expr.instr .x12 (.srl .x12 .x5),
  .SD .x14 .x12 8,
  .SD .x14 .x13 0,
  Expr.instr .x12 (.addi .x20 541),
  Expr.instr .x12 (.srli .x12 3),
  Expr.instr .x12 (.andi .x12 4088),
  Expr.instr .x12 (.add .x12 .x25),
  .LD .x13 .x12 0,
  Expr.instr .x14 (.sll .x11 .x16),
  Expr.instr .x13 (.or .x13 .x14),
  Expr.instr .x11 (.srl .x11 .x5),
  .SD .x12 .x11 8,
  .SD .x12 .x13 0,
  Expr.instr .x11 (.addi .x20 605),
  Expr.instr .x11 (.srli .x11 3),
  Expr.instr .x11 (.andi .x11 4088),
  Expr.instr .x11 (.add .x11 .x25),
  .LD .x12 .x11 0,
  Expr.instr .x13 (.sll .x17 .x16),
  Expr.instr .x12 (.or .x12 .x13),
  Expr.instr .x13 (.srl .x17 .x5),
  .SD .x11 .x13 8,
  .SD .x11 .x12 0,
  Expr.instr .x11 (.addi .x20 669),
  Expr.instr .x11 (.srli .x11 3),
  Expr.instr .x11 (.andi .x11 4088),
  Expr.instr .x11 (.add .x11 .x25),
  .LD .x12 .x11 0,
  Expr.instr .x13 (.sll .x15 .x16),
  Expr.instr .x12 (.or .x12 .x13),
  .SD .x11 .x12 0]
theorem tablem : OpeningStraight.Listed 1110 codem := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem spanm (o : Oracle) (x : I) (nz : off x.data≠0) : Contract o codem (entry x) (m1145 x) := by
  have h1110 := OpeningLinear.read o (entry x) .x13 .x14 0 (cell (atBit x.data 0)) (old x.data 0) (by have := within x.data 0 (by decide);omega) (OpeningRowOps.current x.data 0) rfl
  have h1111 := OpeningLinear.register o (m1111 x) .x5 (.sll .x12 .x16) (x.word 0 <<< off x.data) (OpeningRowOps.left x.data 0)
  have h1112 := OpeningLinear.register o (m1112 x) .x13 (.or .x13 .x5) (merged x.data 0) rfl
  have h1113 := OpeningLinear.register o (m1113 x) .x5 (.subw .x0 .x16) (((0 : BitVec 32)-(W (off x.data)).truncate 32).signExtend 64) rfl
  have h1114 := OpeningLinear.register o (m1114 x) .x12 (.srl .x12 .x5) (high x.data 0) (OpeningRowOps.rightNeg x.data 0 nz)
  have h1115 := OpeningRowData.storeAs o (m1115 x) .x14 .x12 8 (cell (atBit x.data 0)+1) (high x.data 0) (tailMem x.data 0) (within x.data 0 (by decide)) (OpeningRowOps.following x.data 0) rfl rfl
  have h1116 := OpeningRowData.storeAs o (m1116 x) .x14 .x13 0 (cell (atBit x.data 0)) (merged x.data 0) (before x.data 1) (by have := within x.data 0 (by decide);omega) (OpeningRowOps.current x.data 0) rfl (full x.data 0 (by decide) nz)
  have h1117 := OpeningLinear.register o (m1117 x) .x12 (.addi .x20 541) (W (atBit x.data 1)) (OpeningRowOps.plusBit x.root 2051 541 2592 541 rfl rfl)
  have h1118 := OpeningLinear.register o (m1118 x) .x12 (.srli .x12 3) (W (atBit x.data 1) >>> (3 : Nat)) rfl
  have h1119 := OpeningLinear.register o (m1119 x) .x12 (.andi .x12 4088) (((W (atBit x.data 1) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h1120 := OpeningLinear.register o (m1120 x) .x12 (.add .x12 .x25) (OpeningRowData.addr x.data 1) (OpeningRowOps.pointer x.data 1 (by decide))
  have h1121 := OpeningLinear.read o (m1121 x) .x13 .x12 0 (cell (atBit x.data 1)) (old x.data 1) (by have := within x.data 1 (by decide);omega) (OpeningRowOps.current x.data 1) rfl
  have h1122 := OpeningLinear.register o (m1122 x) .x14 (.sll .x11 .x16) (x.word 1 <<< off x.data) (OpeningRowOps.left x.data 1)
  have h1123 := OpeningLinear.register o (m1123 x) .x13 (.or .x13 .x14) (merged x.data 1) rfl
  have h1124 := OpeningLinear.register o (m1124 x) .x11 (.srl .x11 .x5) (high x.data 1) (OpeningRowOps.rightNeg x.data 1 nz)
  have h1125 := OpeningRowData.storeAs o (m1125 x) .x12 .x11 8 (cell (atBit x.data 1)+1) (high x.data 1) (tailMem x.data 1) (within x.data 1 (by decide)) (OpeningRowOps.following x.data 1) rfl rfl
  have h1126 := OpeningRowData.storeAs o (m1126 x) .x12 .x13 0 (cell (atBit x.data 1)) (merged x.data 1) (before x.data 2) (by have := within x.data 1 (by decide);omega) (OpeningRowOps.current x.data 1) rfl (full x.data 1 (by decide) nz)
  have h1127 := OpeningLinear.register o (m1127 x) .x11 (.addi .x20 605) (W (atBit x.data 2)) (OpeningRowOps.plusBit x.root 2051 605 2656 605 rfl rfl)
  have h1128 := OpeningLinear.register o (m1128 x) .x11 (.srli .x11 3) (W (atBit x.data 2) >>> (3 : Nat)) rfl
  have h1129 := OpeningLinear.register o (m1129 x) .x11 (.andi .x11 4088) (((W (atBit x.data 2) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h1130 := OpeningLinear.register o (m1130 x) .x11 (.add .x11 .x25) (OpeningRowData.addr x.data 2) (OpeningRowOps.pointer x.data 2 (by decide))
  have h1131 := OpeningLinear.read o (m1131 x) .x12 .x11 0 (cell (atBit x.data 2)) (old x.data 2) (by have := within x.data 2 (by decide);omega) (OpeningRowOps.current x.data 2) rfl
  have h1132 := OpeningLinear.register o (m1132 x) .x13 (.sll .x17 .x16) (x.word 2 <<< off x.data) (OpeningRowOps.left x.data 2)
  have h1133 := OpeningLinear.register o (m1133 x) .x12 (.or .x12 .x13) (merged x.data 2) rfl
  have h1134 := OpeningLinear.register o (m1134 x) .x13 (.srl .x17 .x5) (high x.data 2) (OpeningRowOps.rightNeg x.data 2 nz)
  have h1135 := OpeningRowData.storeAs o (m1135 x) .x11 .x13 8 (cell (atBit x.data 2)+1) (high x.data 2) (tailMem x.data 2) (within x.data 2 (by decide)) (OpeningRowOps.following x.data 2) rfl rfl
  have h1136 := OpeningRowData.storeAs o (m1136 x) .x11 .x12 0 (cell (atBit x.data 2)) (merged x.data 2) (before x.data 3) (by have := within x.data 2 (by decide);omega) (OpeningRowOps.current x.data 2) rfl (full x.data 2 (by decide) nz)
  have h1137 := OpeningLinear.register o (m1137 x) .x11 (.addi .x20 669) (W (atBit x.data 3)) (OpeningRowOps.plusBit x.root 2051 669 2720 669 rfl rfl)
  have h1138 := OpeningLinear.register o (m1138 x) .x11 (.srli .x11 3) (W (atBit x.data 3) >>> (3 : Nat)) rfl
  have h1139 := OpeningLinear.register o (m1139 x) .x11 (.andi .x11 4088) (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h1140 := OpeningLinear.register o (m1140 x) .x11 (.add .x11 .x25) (OpeningRowData.addr x.data 3) (OpeningRowOps.pointer x.data 3 (by decide))
  have h1141 := OpeningLinear.read o (m1141 x) .x12 .x11 0 (cell (atBit x.data 3)) (old x.data 3) (by have := within x.data 3 (by decide);omega) (OpeningRowOps.current x.data 3) rfl
  have h1142 := OpeningLinear.register o (m1142 x) .x13 (.sll .x15 .x16) (x.word 3 <<< off x.data) (OpeningRowOps.left x.data 3)
  have h1143 := OpeningLinear.register o (m1143 x) .x12 (.or .x12 .x13) (merged x.data 3) rfl
  have h1144 := OpeningRowData.storeAs o (m1144 x) .x11 .x12 0 (cell (atBit x.data 3)) (merged x.data 3) (headMem x.data 3) (by have := within x.data 3 (by decide);omega) (OpeningRowOps.current x.data 3) rfl rfl
  exact LeafModel.combine h1110 (LeafModel.combine h1111 (LeafModel.combine h1112 (LeafModel.combine h1113 (LeafModel.combine h1114 (LeafModel.combine h1115 (LeafModel.combine h1116 (LeafModel.combine h1117 (LeafModel.combine h1118 (LeafModel.combine h1119 (LeafModel.combine h1120 (LeafModel.combine h1121 (LeafModel.combine h1122 (LeafModel.combine h1123 (LeafModel.combine h1124 (LeafModel.combine h1125 (LeafModel.combine h1126 (LeafModel.combine h1127 (LeafModel.combine h1128 (LeafModel.combine h1129 (LeafModel.combine h1130 (LeafModel.combine h1131 (LeafModel.combine h1132 (LeafModel.combine h1133 (LeafModel.combine h1134 (LeafModel.combine h1135 (LeafModel.combine h1136 (LeafModel.combine h1137 (LeafModel.combine h1138 (LeafModel.combine h1139 (LeafModel.combine h1140 (LeafModel.combine h1141 (LeafModel.combine h1142 (LeafModel.combine h1143 (LeafModel.combine h1144 (LeafModel.empty _ _)))))))))))))))))))))))))))))))))))

def s1147 (x : I) := (m1145 x).set .x12 ((64 : Word)-W (off x.data))
def s1148 (x : I) := (s1147 x).set .x12 (high x.data 3)
def s1149 (x : I) := withMem (s1148 x) (before x.data 4)

def codes : List Instr := [
  Expr.instr .x12 (.sub .x18 .x16),
  Expr.instr .x12 (.srl .x15 .x12),
  .SD .x11 .x12 8]
theorem tables : OpeningStraight.Listed 1146 codes := ⟨rfl,rfl,rfl,True.intro⟩
theorem spans (o : Oracle) (x : I) (nz : off x.data≠0) (cross : 64<off x.data+x.data.bits) : Contract o codes (m1145 x) (s1149 x) := by
  have h1146 := OpeningLinear.register o (m1145 x) .x12 (.sub .x18 .x16) ((64 : Word)-W (off x.data)) rfl
  have h1147 := OpeningLinear.register o (s1147 x) .x12 (.srl .x15 .x12) (high x.data 3) (OpeningRowOps.rightSub x.data 3 nz)
  have h1148 := OpeningRowData.storeAs o (s1148 x) .x11 .x12 8 (cell (atBit x.data 3)+1) (high x.data 3) (before x.data 4) (within x.data 3 (by decide)) (OpeningRowOps.following x.data 3) rfl (crosses x.data nz cross)
  exact LeafModel.combine h1146 (LeafModel.combine h1147 (LeafModel.combine h1148 (LeafModel.empty _ _)))


def output (x : I) := if off x.data=0 then a1164 x else if off x.data<36 then m1145 x else s1149 x

theorem run (o : Oracle) (x : I) (u : MachineState) (pc : u.pc=CommitBlocks.addr 1109) (fit : Fits u (entry x)) :
    ∃ t n, n≤64 ∧ CommitExact.Segment o OpeningStraight.image n u t ∧ t.pc=CommitBlocks.addr 1164 ∧
      Fits t (output x) := by
  have zstep := zero_branch o u 1109 1110 1150 .x16 164 pc (by decide) rfl rfl rfl
    (W (off x.data)) (fit.registers _)
  have eqv : W (off x.data)=0 ↔ off x.data=0 := OpeningBranch.word_zero _
  simp only [eqv] at zstep
  unfold output
  by_cases z : off x.data=0
  · simp only [z,ite_true] at zstep ⊢
    obtain ⟨v,rv,pv,hv⟩ := OpeningLinear.block (spana o x z) (i:=1150) (by decide) tablea
      (u.setPC _) rfl (fit.pc _)
    exact ⟨v,1+codea.length,by change 15≤64;decide,CommitExact.compose zstep rv,pv,hv⟩
  · simp only [z,ite_false] at zstep ⊢
    obtain ⟨v,rv,pv,hv⟩ := OpeningLinear.block (spanm o x z) (i:=1110) (by decide) tablem (u.setPC _) rfl (fit.pc _)
    have branch := OpeningBranch.less o v .x16 .x7 1145 1164 76 pv (by decide) rfl rfl
      (off x.data) 36 (by unfold off;omega) (by decide) (hv.registers _) (hv.registers _)
    by_cases little : off x.data<36
    · simp only [little,ite_true] at branch ⊢
      exact ⟨_,1+codem.length+1,by change 37≤64;decide,CommitExact.compose (CommitExact.compose zstep rv) branch,rfl,hv.pc _⟩
    · simp only [little,ite_false] at branch ⊢
      have cross : 64<off x.data+x.data.bits := by change 64<off x.data+29;omega
      obtain ⟨w,rw,pw,hw⟩ := OpeningLinear.block (spans o x z cross) (i:=1146) (by decide) tables
        (v.setPC _) rfl (hv.pc _)
      have jump := OpeningBranch.jump o w 1149 1164 60 pw (by decide) rfl rfl
      exact ⟨_,1+codem.length+1+codes.length+1,by change 41≤64;decide,CommitExact.compose (CommitExact.compose (CommitExact.compose
        (CommitExact.compose zstep rv) branch) rw) jump,rfl,hw.pc _⟩

theorem memory (x : I) : (output x).mem=before x.data 4 := by
  unfold output
  split
  · rfl
  · rename_i nz;split
    · rename_i little
      exact short x.data nz (by change off x.data+29≤64;omega)
    · rfl

def changed : List Reg := [.x5,.x11,.x12,.x13,.x14]

theorem frame (x : I) (r : Reg) (h : r∉changed) : (output x).reg r=(entry x).reg r := by
  unfold output
  split
  · cases r <;> first | rfl | exact False.elim (h (by decide))
  · split <;> cases r <;> first | rfl | exact False.elim (h (by decide))

end CommitGolfCandidate.Reconstruction.OpeningRow14
