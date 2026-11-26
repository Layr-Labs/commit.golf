import CommitGolfCandidate.ReconstructedOpeningRowOps

namespace CommitGolfCandidate.Reconstruction.OpeningRow13
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningOps OpeningCursor OpeningPut OpeningRowData
open TwoPermutationPrototype.RV64
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000

abbrev I := OpeningRowOps.Input 2749 29
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

def a1219 (x : I) := withMem (entry x) (before x.data 1)
def a1220 (x : I) := (a1219 x).set .x12 (W (atBit x.data 1))
def a1221 (x : I) := (a1220 x).set .x12 (W (atBit x.data 1) >>> (3 : Nat))
def a1222 (x : I) := (a1221 x).set .x12 (OpeningRowData.addr x.data 1)
def a1223 (x : I) := withMem (a1222 x) (before x.data 2)
def a1224 (x : I) := (a1223 x).set .x11 (W (atBit x.data 2))
def a1225 (x : I) := (a1224 x).set .x11 (W (atBit x.data 2) >>> (3 : Nat))
def a1226 (x : I) := (a1225 x).set .x11 (OpeningRowData.addr x.data 2)
def a1227 (x : I) := withMem (a1226 x) (before x.data 3)
def a1228 (x : I) := (a1227 x).set .x11 (W (atBit x.data 3))
def a1229 (x : I) := (a1228 x).set .x11 (W (atBit x.data 3) >>> (3 : Nat))
def a1230 (x : I) := (a1229 x).set .x11 (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088))
def a1231 (x : I) := (a1230 x).set .x11 (OpeningRowData.addr x.data 3)
def a1232 (x : I) := withMem (a1231 x) (before x.data 4)

def codea : List Instr := [
  .SD .x14 .x12 0,
  Expr.instr .x12 (.addi .x20 762),
  Expr.instr .x12 (.srli .x12 3),
  Expr.instr .x12 (.add .x12 .x25),
  .SD .x12 .x11 0,
  Expr.instr .x11 (.addi .x20 826),
  Expr.instr .x11 (.srli .x11 3),
  Expr.instr .x11 (.add .x11 .x25),
  .SD .x11 .x17 0,
  Expr.instr .x11 (.addi .x20 890),
  Expr.instr .x11 (.srli .x11 3),
  Expr.instr .x11 (.andi .x11 4088),
  Expr.instr .x11 (.add .x11 .x25),
  .SD .x11 .x15 0]
theorem tablea : OpeningStraight.Listed 1218 codea := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem spana (o : Oracle) (x : I) (align : off x.data=0) : Contract o codea (entry x) (a1232 x) := by
  have h1218 := OpeningRowData.storeAs o (entry x) .x14 .x12 0 (cell (atBit x.data 0)) (x.word 0) (before x.data 1) (by have := within x.data 0 (by decide);omega) (OpeningRowOps.current x.data 0) rfl (OpeningRowData.aligned x.data 0 align)
  have h1219 := OpeningLinear.register o (a1219 x) .x12 (.addi .x20 762) (W (atBit x.data 1)) (OpeningRowOps.plusBit x.root 2051 762 2813 762 rfl rfl)
  have h1220 := OpeningLinear.register o (a1220 x) .x12 (.srli .x12 3) (W (atBit x.data 1) >>> (3 : Nat)) rfl
  have h1221 := OpeningLinear.register o (a1221 x) .x12 (.add .x12 .x25) (OpeningRowData.addr x.data 1) (OpeningRowOps.bare x.data 1 (by decide) align)
  have h1222 := OpeningRowData.storeAs o (a1222 x) .x12 .x11 0 (cell (atBit x.data 1)) (x.word 1) (before x.data 2) (by have := within x.data 1 (by decide);omega) (OpeningRowOps.current x.data 1) rfl (OpeningRowData.aligned x.data 1 align)
  have h1223 := OpeningLinear.register o (a1223 x) .x11 (.addi .x20 826) (W (atBit x.data 2)) (OpeningRowOps.plusBit x.root 2051 826 2877 826 rfl rfl)
  have h1224 := OpeningLinear.register o (a1224 x) .x11 (.srli .x11 3) (W (atBit x.data 2) >>> (3 : Nat)) rfl
  have h1225 := OpeningLinear.register o (a1225 x) .x11 (.add .x11 .x25) (OpeningRowData.addr x.data 2) (OpeningRowOps.bare x.data 2 (by decide) align)
  have h1226 := OpeningRowData.storeAs o (a1226 x) .x11 .x17 0 (cell (atBit x.data 2)) (x.word 2) (before x.data 3) (by have := within x.data 2 (by decide);omega) (OpeningRowOps.current x.data 2) rfl (OpeningRowData.aligned x.data 2 align)
  have h1227 := OpeningLinear.register o (a1227 x) .x11 (.addi .x20 890) (W (atBit x.data 3)) (OpeningRowOps.plusBit x.root 2051 890 2941 890 rfl rfl)
  have h1228 := OpeningLinear.register o (a1228 x) .x11 (.srli .x11 3) (W (atBit x.data 3) >>> (3 : Nat)) rfl
  have h1229 := OpeningLinear.register o (a1229 x) .x11 (.andi .x11 4088) (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h1230 := OpeningLinear.register o (a1230 x) .x11 (.add .x11 .x25) (OpeningRowData.addr x.data 3) (OpeningRowOps.pointer x.data 3 (by decide))
  have h1231 := OpeningRowData.storeAs o (a1231 x) .x11 .x15 0 (cell (atBit x.data 3)) (x.word 3) (before x.data 4) (by have := within x.data 3 (by decide);omega) (OpeningRowOps.current x.data 3) rfl (OpeningRowData.aligned x.data 3 align)
  exact LeafModel.combine h1218 (LeafModel.combine h1219 (LeafModel.combine h1220 (LeafModel.combine h1221 (LeafModel.combine h1222 (LeafModel.combine h1223 (LeafModel.combine h1224 (LeafModel.combine h1225 (LeafModel.combine h1226 (LeafModel.combine h1227 (LeafModel.combine h1228 (LeafModel.combine h1229 (LeafModel.combine h1230 (LeafModel.combine h1231 (LeafModel.empty _ _))))))))))))))

def m1179 (x : I) := (entry x).set .x13 (old x.data 0)
def m1180 (x : I) := (m1179 x).set .x5 (x.word 0 <<< off x.data)
def m1181 (x : I) := (m1180 x).set .x13 (merged x.data 0)
def m1182 (x : I) := (m1181 x).set .x5 (((0 : BitVec 32)-(W (off x.data)).truncate 32).signExtend 64)
def m1183 (x : I) := (m1182 x).set .x12 (high x.data 0)
def m1184 (x : I) := withMem (m1183 x) (tailMem x.data 0)
def m1185 (x : I) := withMem (m1184 x) (before x.data 1)
def m1186 (x : I) := (m1185 x).set .x12 (W (atBit x.data 1))
def m1187 (x : I) := (m1186 x).set .x12 (W (atBit x.data 1) >>> (3 : Nat))
def m1188 (x : I) := (m1187 x).set .x12 (((W (atBit x.data 1) >>> (3 : Nat)) &&& signExtend12 4088))
def m1189 (x : I) := (m1188 x).set .x12 (OpeningRowData.addr x.data 1)
def m1190 (x : I) := (m1189 x).set .x13 (old x.data 1)
def m1191 (x : I) := (m1190 x).set .x14 (x.word 1 <<< off x.data)
def m1192 (x : I) := (m1191 x).set .x13 (merged x.data 1)
def m1193 (x : I) := (m1192 x).set .x11 (high x.data 1)
def m1194 (x : I) := withMem (m1193 x) (tailMem x.data 1)
def m1195 (x : I) := withMem (m1194 x) (before x.data 2)
def m1196 (x : I) := (m1195 x).set .x11 (W (atBit x.data 2))
def m1197 (x : I) := (m1196 x).set .x11 (W (atBit x.data 2) >>> (3 : Nat))
def m1198 (x : I) := (m1197 x).set .x11 (((W (atBit x.data 2) >>> (3 : Nat)) &&& signExtend12 4088))
def m1199 (x : I) := (m1198 x).set .x11 (OpeningRowData.addr x.data 2)
def m1200 (x : I) := (m1199 x).set .x12 (old x.data 2)
def m1201 (x : I) := (m1200 x).set .x13 (x.word 2 <<< off x.data)
def m1202 (x : I) := (m1201 x).set .x12 (merged x.data 2)
def m1203 (x : I) := (m1202 x).set .x13 (high x.data 2)
def m1204 (x : I) := withMem (m1203 x) (tailMem x.data 2)
def m1205 (x : I) := withMem (m1204 x) (before x.data 3)
def m1206 (x : I) := (m1205 x).set .x11 (W (atBit x.data 3))
def m1207 (x : I) := (m1206 x).set .x11 (W (atBit x.data 3) >>> (3 : Nat))
def m1208 (x : I) := (m1207 x).set .x11 (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088))
def m1209 (x : I) := (m1208 x).set .x11 (OpeningRowData.addr x.data 3)
def m1210 (x : I) := (m1209 x).set .x12 (old x.data 3)
def m1211 (x : I) := (m1210 x).set .x13 (x.word 3 <<< off x.data)
def m1212 (x : I) := (m1211 x).set .x12 (merged x.data 3)
def m1213 (x : I) := withMem (m1212 x) (headMem x.data 3)

def codem : List Instr := [
  .LD .x13 .x14 0,
  Expr.instr .x5 (.sll .x12 .x16),
  Expr.instr .x13 (.or .x13 .x5),
  Expr.instr .x5 (.subw .x0 .x16),
  Expr.instr .x12 (.srl .x12 .x5),
  .SD .x14 .x12 8,
  .SD .x14 .x13 0,
  Expr.instr .x12 (.addi .x20 762),
  Expr.instr .x12 (.srli .x12 3),
  Expr.instr .x12 (.andi .x12 4088),
  Expr.instr .x12 (.add .x12 .x25),
  .LD .x13 .x12 0,
  Expr.instr .x14 (.sll .x11 .x16),
  Expr.instr .x13 (.or .x13 .x14),
  Expr.instr .x11 (.srl .x11 .x5),
  .SD .x12 .x11 8,
  .SD .x12 .x13 0,
  Expr.instr .x11 (.addi .x20 826),
  Expr.instr .x11 (.srli .x11 3),
  Expr.instr .x11 (.andi .x11 4088),
  Expr.instr .x11 (.add .x11 .x25),
  .LD .x12 .x11 0,
  Expr.instr .x13 (.sll .x17 .x16),
  Expr.instr .x12 (.or .x12 .x13),
  Expr.instr .x13 (.srl .x17 .x5),
  .SD .x11 .x13 8,
  .SD .x11 .x12 0,
  Expr.instr .x11 (.addi .x20 890),
  Expr.instr .x11 (.srli .x11 3),
  Expr.instr .x11 (.andi .x11 4088),
  Expr.instr .x11 (.add .x11 .x25),
  .LD .x12 .x11 0,
  Expr.instr .x13 (.sll .x15 .x16),
  Expr.instr .x12 (.or .x12 .x13),
  .SD .x11 .x12 0]
theorem tablem : OpeningStraight.Listed 1178 codem := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem spanm (o : Oracle) (x : I) (nz : off x.data≠0) : Contract o codem (entry x) (m1213 x) := by
  have h1178 := OpeningLinear.read o (entry x) .x13 .x14 0 (cell (atBit x.data 0)) (old x.data 0) (by have := within x.data 0 (by decide);omega) (OpeningRowOps.current x.data 0) rfl
  have h1179 := OpeningLinear.register o (m1179 x) .x5 (.sll .x12 .x16) (x.word 0 <<< off x.data) (OpeningRowOps.left x.data 0)
  have h1180 := OpeningLinear.register o (m1180 x) .x13 (.or .x13 .x5) (merged x.data 0) rfl
  have h1181 := OpeningLinear.register o (m1181 x) .x5 (.subw .x0 .x16) (((0 : BitVec 32)-(W (off x.data)).truncate 32).signExtend 64) rfl
  have h1182 := OpeningLinear.register o (m1182 x) .x12 (.srl .x12 .x5) (high x.data 0) (OpeningRowOps.rightNeg x.data 0 nz)
  have h1183 := OpeningRowData.storeAs o (m1183 x) .x14 .x12 8 (cell (atBit x.data 0)+1) (high x.data 0) (tailMem x.data 0) (within x.data 0 (by decide)) (OpeningRowOps.following x.data 0) rfl rfl
  have h1184 := OpeningRowData.storeAs o (m1184 x) .x14 .x13 0 (cell (atBit x.data 0)) (merged x.data 0) (before x.data 1) (by have := within x.data 0 (by decide);omega) (OpeningRowOps.current x.data 0) rfl (full x.data 0 (by decide) nz)
  have h1185 := OpeningLinear.register o (m1185 x) .x12 (.addi .x20 762) (W (atBit x.data 1)) (OpeningRowOps.plusBit x.root 2051 762 2813 762 rfl rfl)
  have h1186 := OpeningLinear.register o (m1186 x) .x12 (.srli .x12 3) (W (atBit x.data 1) >>> (3 : Nat)) rfl
  have h1187 := OpeningLinear.register o (m1187 x) .x12 (.andi .x12 4088) (((W (atBit x.data 1) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h1188 := OpeningLinear.register o (m1188 x) .x12 (.add .x12 .x25) (OpeningRowData.addr x.data 1) (OpeningRowOps.pointer x.data 1 (by decide))
  have h1189 := OpeningLinear.read o (m1189 x) .x13 .x12 0 (cell (atBit x.data 1)) (old x.data 1) (by have := within x.data 1 (by decide);omega) (OpeningRowOps.current x.data 1) rfl
  have h1190 := OpeningLinear.register o (m1190 x) .x14 (.sll .x11 .x16) (x.word 1 <<< off x.data) (OpeningRowOps.left x.data 1)
  have h1191 := OpeningLinear.register o (m1191 x) .x13 (.or .x13 .x14) (merged x.data 1) rfl
  have h1192 := OpeningLinear.register o (m1192 x) .x11 (.srl .x11 .x5) (high x.data 1) (OpeningRowOps.rightNeg x.data 1 nz)
  have h1193 := OpeningRowData.storeAs o (m1193 x) .x12 .x11 8 (cell (atBit x.data 1)+1) (high x.data 1) (tailMem x.data 1) (within x.data 1 (by decide)) (OpeningRowOps.following x.data 1) rfl rfl
  have h1194 := OpeningRowData.storeAs o (m1194 x) .x12 .x13 0 (cell (atBit x.data 1)) (merged x.data 1) (before x.data 2) (by have := within x.data 1 (by decide);omega) (OpeningRowOps.current x.data 1) rfl (full x.data 1 (by decide) nz)
  have h1195 := OpeningLinear.register o (m1195 x) .x11 (.addi .x20 826) (W (atBit x.data 2)) (OpeningRowOps.plusBit x.root 2051 826 2877 826 rfl rfl)
  have h1196 := OpeningLinear.register o (m1196 x) .x11 (.srli .x11 3) (W (atBit x.data 2) >>> (3 : Nat)) rfl
  have h1197 := OpeningLinear.register o (m1197 x) .x11 (.andi .x11 4088) (((W (atBit x.data 2) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h1198 := OpeningLinear.register o (m1198 x) .x11 (.add .x11 .x25) (OpeningRowData.addr x.data 2) (OpeningRowOps.pointer x.data 2 (by decide))
  have h1199 := OpeningLinear.read o (m1199 x) .x12 .x11 0 (cell (atBit x.data 2)) (old x.data 2) (by have := within x.data 2 (by decide);omega) (OpeningRowOps.current x.data 2) rfl
  have h1200 := OpeningLinear.register o (m1200 x) .x13 (.sll .x17 .x16) (x.word 2 <<< off x.data) (OpeningRowOps.left x.data 2)
  have h1201 := OpeningLinear.register o (m1201 x) .x12 (.or .x12 .x13) (merged x.data 2) rfl
  have h1202 := OpeningLinear.register o (m1202 x) .x13 (.srl .x17 .x5) (high x.data 2) (OpeningRowOps.rightNeg x.data 2 nz)
  have h1203 := OpeningRowData.storeAs o (m1203 x) .x11 .x13 8 (cell (atBit x.data 2)+1) (high x.data 2) (tailMem x.data 2) (within x.data 2 (by decide)) (OpeningRowOps.following x.data 2) rfl rfl
  have h1204 := OpeningRowData.storeAs o (m1204 x) .x11 .x12 0 (cell (atBit x.data 2)) (merged x.data 2) (before x.data 3) (by have := within x.data 2 (by decide);omega) (OpeningRowOps.current x.data 2) rfl (full x.data 2 (by decide) nz)
  have h1205 := OpeningLinear.register o (m1205 x) .x11 (.addi .x20 890) (W (atBit x.data 3)) (OpeningRowOps.plusBit x.root 2051 890 2941 890 rfl rfl)
  have h1206 := OpeningLinear.register o (m1206 x) .x11 (.srli .x11 3) (W (atBit x.data 3) >>> (3 : Nat)) rfl
  have h1207 := OpeningLinear.register o (m1207 x) .x11 (.andi .x11 4088) (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h1208 := OpeningLinear.register o (m1208 x) .x11 (.add .x11 .x25) (OpeningRowData.addr x.data 3) (OpeningRowOps.pointer x.data 3 (by decide))
  have h1209 := OpeningLinear.read o (m1209 x) .x12 .x11 0 (cell (atBit x.data 3)) (old x.data 3) (by have := within x.data 3 (by decide);omega) (OpeningRowOps.current x.data 3) rfl
  have h1210 := OpeningLinear.register o (m1210 x) .x13 (.sll .x15 .x16) (x.word 3 <<< off x.data) (OpeningRowOps.left x.data 3)
  have h1211 := OpeningLinear.register o (m1211 x) .x12 (.or .x12 .x13) (merged x.data 3) rfl
  have h1212 := OpeningRowData.storeAs o (m1212 x) .x11 .x12 0 (cell (atBit x.data 3)) (merged x.data 3) (headMem x.data 3) (by have := within x.data 3 (by decide);omega) (OpeningRowOps.current x.data 3) rfl rfl
  exact LeafModel.combine h1178 (LeafModel.combine h1179 (LeafModel.combine h1180 (LeafModel.combine h1181 (LeafModel.combine h1182 (LeafModel.combine h1183 (LeafModel.combine h1184 (LeafModel.combine h1185 (LeafModel.combine h1186 (LeafModel.combine h1187 (LeafModel.combine h1188 (LeafModel.combine h1189 (LeafModel.combine h1190 (LeafModel.combine h1191 (LeafModel.combine h1192 (LeafModel.combine h1193 (LeafModel.combine h1194 (LeafModel.combine h1195 (LeafModel.combine h1196 (LeafModel.combine h1197 (LeafModel.combine h1198 (LeafModel.combine h1199 (LeafModel.combine h1200 (LeafModel.combine h1201 (LeafModel.combine h1202 (LeafModel.combine h1203 (LeafModel.combine h1204 (LeafModel.combine h1205 (LeafModel.combine h1206 (LeafModel.combine h1207 (LeafModel.combine h1208 (LeafModel.combine h1209 (LeafModel.combine h1210 (LeafModel.combine h1211 (LeafModel.combine h1212 (LeafModel.empty _ _)))))))))))))))))))))))))))))))))))

def s1215 (x : I) := (m1213 x).set .x12 ((64 : Word)-W (off x.data))
def s1216 (x : I) := (s1215 x).set .x12 (high x.data 3)
def s1217 (x : I) := withMem (s1216 x) (before x.data 4)

def codes : List Instr := [
  Expr.instr .x12 (.sub .x18 .x16),
  Expr.instr .x12 (.srl .x15 .x12),
  .SD .x11 .x12 8]
theorem tables : OpeningStraight.Listed 1214 codes := ⟨rfl,rfl,rfl,True.intro⟩
theorem spans (o : Oracle) (x : I) (nz : off x.data≠0) (cross : 64<off x.data+x.data.bits) : Contract o codes (m1213 x) (s1217 x) := by
  have h1214 := OpeningLinear.register o (m1213 x) .x12 (.sub .x18 .x16) ((64 : Word)-W (off x.data)) rfl
  have h1215 := OpeningLinear.register o (s1215 x) .x12 (.srl .x15 .x12) (high x.data 3) (OpeningRowOps.rightSub x.data 3 nz)
  have h1216 := OpeningRowData.storeAs o (s1216 x) .x11 .x12 8 (cell (atBit x.data 3)+1) (high x.data 3) (before x.data 4) (within x.data 3 (by decide)) (OpeningRowOps.following x.data 3) rfl (crosses x.data nz cross)
  exact LeafModel.combine h1214 (LeafModel.combine h1215 (LeafModel.combine h1216 (LeafModel.empty _ _)))


def output (x : I) := if off x.data=0 then a1232 x else if off x.data<36 then m1213 x else s1217 x

theorem run (o : Oracle) (x : I) (u : MachineState) (pc : u.pc=CommitBlocks.addr 1177) (fit : Fits u (entry x)) :
    ∃ t n, n≤64 ∧ CommitExact.Segment o OpeningStraight.image n u t ∧ t.pc=CommitBlocks.addr 1232 ∧
      Fits t (output x) := by
  have zstep := zero_branch o u 1177 1178 1218 .x16 164 pc (by decide) rfl rfl rfl
    (W (off x.data)) (fit.registers _)
  have eqv : W (off x.data)=0 ↔ off x.data=0 := OpeningBranch.word_zero _
  simp only [eqv] at zstep
  unfold output
  by_cases z : off x.data=0
  · simp only [z,ite_true] at zstep ⊢
    obtain ⟨v,rv,pv,hv⟩ := OpeningLinear.block (spana o x z) (i:=1218) (by decide) tablea
      (u.setPC _) rfl (fit.pc _)
    exact ⟨v,1+codea.length,by change 15≤64;decide,CommitExact.compose zstep rv,pv,hv⟩
  · simp only [z,ite_false] at zstep ⊢
    obtain ⟨v,rv,pv,hv⟩ := OpeningLinear.block (spanm o x z) (i:=1178) (by decide) tablem (u.setPC _) rfl (fit.pc _)
    have branch := OpeningBranch.less o v .x16 .x7 1213 1232 76 pv (by decide) rfl rfl
      (off x.data) 36 (by unfold off;omega) (by decide) (hv.registers _) (hv.registers _)
    by_cases little : off x.data<36
    · simp only [little,ite_true] at branch ⊢
      exact ⟨_,1+codem.length+1,by change 37≤64;decide,CommitExact.compose (CommitExact.compose zstep rv) branch,rfl,hv.pc _⟩
    · simp only [little,ite_false] at branch ⊢
      have cross : 64<off x.data+x.data.bits := by change 64<off x.data+29;omega
      obtain ⟨w,rw,pw,hw⟩ := OpeningLinear.block (spans o x z cross) (i:=1214) (by decide) tables
        (v.setPC _) rfl (hv.pc _)
      have jump := OpeningBranch.jump o w 1217 1232 60 pw (by decide) rfl rfl
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

end CommitGolfCandidate.Reconstruction.OpeningRow13
