import CommitGolfCandidate.ReconstructedOpeningRowOps

namespace CommitGolfCandidate.Reconstruction.OpeningRow12
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningOps OpeningCursor OpeningPut OpeningRowData
open TwoPermutationPrototype.RV64
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000

abbrev I := OpeningRowOps.Input 2970 29
def entry (x : I) : Model := ⟨fun
  | .x0 => W 0
  | .x7 => W 36
  | .x11 => x.word 1
  | .x12 => x.word 0
  | .x13 => x.word 3
  | .x14 => OpeningRowData.addr x.data 0
  | .x15 => W (off x.data)
  | .x16 => x.word 2
  | .x18 => W 64
  | .x20 => W (x.root+2051)
  | .x25 => wordAddress OpeningPut.base
  | r => x.initial.reg r, x.initial.mem⟩

def a1287 (x : I) := withMem (entry x) (before x.data 1)
def a1288 (x : I) := (a1287 x).set .x12 (W (atBit x.data 1))
def a1289 (x : I) := (a1288 x).set .x12 (W (atBit x.data 1) >>> (3 : Nat))
def a1290 (x : I) := (a1289 x).set .x12 (OpeningRowData.addr x.data 1)
def a1291 (x : I) := withMem (a1290 x) (before x.data 2)
def a1292 (x : I) := (a1291 x).set .x11 (W (atBit x.data 2))
def a1293 (x : I) := (a1292 x).set .x11 (W (atBit x.data 2) >>> (3 : Nat))
def a1294 (x : I) := (a1293 x).set .x11 (OpeningRowData.addr x.data 2)
def a1295 (x : I) := withMem (a1294 x) (before x.data 3)
def a1296 (x : I) := (a1295 x).set .x11 (W (atBit x.data 3))
def a1297 (x : I) := (a1296 x).set .x11 (W (atBit x.data 3) >>> (3 : Nat))
def a1298 (x : I) := (a1297 x).set .x11 (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088))
def a1299 (x : I) := (a1298 x).set .x11 (OpeningRowData.addr x.data 3)
def a1300 (x : I) := withMem (a1299 x) (before x.data 4)

def codea : List Instr := [
  .SD .x14 .x12 0,
  Expr.instr .x12 (.addi .x20 983),
  Expr.instr .x12 (.srli .x12 3),
  Expr.instr .x12 (.add .x12 .x25),
  .SD .x12 .x11 0,
  Expr.instr .x11 (.addi .x20 1047),
  Expr.instr .x11 (.srli .x11 3),
  Expr.instr .x11 (.add .x11 .x25),
  .SD .x11 .x16 0,
  Expr.instr .x11 (.addi .x20 1111),
  Expr.instr .x11 (.srli .x11 3),
  Expr.instr .x11 (.andi .x11 4088),
  Expr.instr .x11 (.add .x11 .x25),
  .SD .x11 .x13 0]
theorem tablea : OpeningStraight.Listed 1286 codea := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem spana (o : Oracle) (x : I) (align : off x.data=0) : Contract o codea (entry x) (a1300 x) := by
  have h1286 := OpeningRowData.storeAs o (entry x) .x14 .x12 0 (cell (atBit x.data 0)) (x.word 0) (before x.data 1) (by have := within x.data 0 (by decide);omega) (OpeningRowOps.current x.data 0) rfl (OpeningRowData.aligned x.data 0 align)
  have h1287 := OpeningLinear.register o (a1287 x) .x12 (.addi .x20 983) (W (atBit x.data 1)) (OpeningRowOps.plusBit x.root 2051 983 3034 983 rfl rfl)
  have h1288 := OpeningLinear.register o (a1288 x) .x12 (.srli .x12 3) (W (atBit x.data 1) >>> (3 : Nat)) rfl
  have h1289 := OpeningLinear.register o (a1289 x) .x12 (.add .x12 .x25) (OpeningRowData.addr x.data 1) (OpeningRowOps.bare x.data 1 (by decide) align)
  have h1290 := OpeningRowData.storeAs o (a1290 x) .x12 .x11 0 (cell (atBit x.data 1)) (x.word 1) (before x.data 2) (by have := within x.data 1 (by decide);omega) (OpeningRowOps.current x.data 1) rfl (OpeningRowData.aligned x.data 1 align)
  have h1291 := OpeningLinear.register o (a1291 x) .x11 (.addi .x20 1047) (W (atBit x.data 2)) (OpeningRowOps.plusBit x.root 2051 1047 3098 1047 rfl rfl)
  have h1292 := OpeningLinear.register o (a1292 x) .x11 (.srli .x11 3) (W (atBit x.data 2) >>> (3 : Nat)) rfl
  have h1293 := OpeningLinear.register o (a1293 x) .x11 (.add .x11 .x25) (OpeningRowData.addr x.data 2) (OpeningRowOps.bare x.data 2 (by decide) align)
  have h1294 := OpeningRowData.storeAs o (a1294 x) .x11 .x16 0 (cell (atBit x.data 2)) (x.word 2) (before x.data 3) (by have := within x.data 2 (by decide);omega) (OpeningRowOps.current x.data 2) rfl (OpeningRowData.aligned x.data 2 align)
  have h1295 := OpeningLinear.register o (a1295 x) .x11 (.addi .x20 1111) (W (atBit x.data 3)) (OpeningRowOps.plusBit x.root 2051 1111 3162 1111 rfl rfl)
  have h1296 := OpeningLinear.register o (a1296 x) .x11 (.srli .x11 3) (W (atBit x.data 3) >>> (3 : Nat)) rfl
  have h1297 := OpeningLinear.register o (a1297 x) .x11 (.andi .x11 4088) (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h1298 := OpeningLinear.register o (a1298 x) .x11 (.add .x11 .x25) (OpeningRowData.addr x.data 3) (OpeningRowOps.pointer x.data 3 (by decide))
  have h1299 := OpeningRowData.storeAs o (a1299 x) .x11 .x13 0 (cell (atBit x.data 3)) (x.word 3) (before x.data 4) (by have := within x.data 3 (by decide);omega) (OpeningRowOps.current x.data 3) rfl (OpeningRowData.aligned x.data 3 align)
  exact LeafModel.combine h1286 (LeafModel.combine h1287 (LeafModel.combine h1288 (LeafModel.combine h1289 (LeafModel.combine h1290 (LeafModel.combine h1291 (LeafModel.combine h1292 (LeafModel.combine h1293 (LeafModel.combine h1294 (LeafModel.combine h1295 (LeafModel.combine h1296 (LeafModel.combine h1297 (LeafModel.combine h1298 (LeafModel.combine h1299 (LeafModel.empty _ _))))))))))))))

def m1247 (x : I) := (entry x).set .x17 (old x.data 0)
def m1248 (x : I) := (m1247 x).set .x5 (x.word 0 <<< off x.data)
def m1249 (x : I) := (m1248 x).set .x17 (merged x.data 0)
def m1250 (x : I) := (m1249 x).set .x5 (((0 : BitVec 32)-(W (off x.data)).truncate 32).signExtend 64)
def m1251 (x : I) := (m1250 x).set .x12 (high x.data 0)
def m1252 (x : I) := withMem (m1251 x) (tailMem x.data 0)
def m1253 (x : I) := withMem (m1252 x) (before x.data 1)
def m1254 (x : I) := (m1253 x).set .x12 (W (atBit x.data 1))
def m1255 (x : I) := (m1254 x).set .x12 (W (atBit x.data 1) >>> (3 : Nat))
def m1256 (x : I) := (m1255 x).set .x12 (((W (atBit x.data 1) >>> (3 : Nat)) &&& signExtend12 4088))
def m1257 (x : I) := (m1256 x).set .x12 (OpeningRowData.addr x.data 1)
def m1258 (x : I) := (m1257 x).set .x14 (old x.data 1)
def m1259 (x : I) := (m1258 x).set .x17 (x.word 1 <<< off x.data)
def m1260 (x : I) := (m1259 x).set .x14 (merged x.data 1)
def m1261 (x : I) := (m1260 x).set .x11 (high x.data 1)
def m1262 (x : I) := withMem (m1261 x) (tailMem x.data 1)
def m1263 (x : I) := withMem (m1262 x) (before x.data 2)
def m1264 (x : I) := (m1263 x).set .x11 (W (atBit x.data 2))
def m1265 (x : I) := (m1264 x).set .x11 (W (atBit x.data 2) >>> (3 : Nat))
def m1266 (x : I) := (m1265 x).set .x11 (((W (atBit x.data 2) >>> (3 : Nat)) &&& signExtend12 4088))
def m1267 (x : I) := (m1266 x).set .x11 (OpeningRowData.addr x.data 2)
def m1268 (x : I) := (m1267 x).set .x12 (old x.data 2)
def m1269 (x : I) := (m1268 x).set .x14 (x.word 2 <<< off x.data)
def m1270 (x : I) := (m1269 x).set .x12 (merged x.data 2)
def m1271 (x : I) := (m1270 x).set .x14 (high x.data 2)
def m1272 (x : I) := withMem (m1271 x) (tailMem x.data 2)
def m1273 (x : I) := withMem (m1272 x) (before x.data 3)
def m1274 (x : I) := (m1273 x).set .x11 (W (atBit x.data 3))
def m1275 (x : I) := (m1274 x).set .x11 (W (atBit x.data 3) >>> (3 : Nat))
def m1276 (x : I) := (m1275 x).set .x11 (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088))
def m1277 (x : I) := (m1276 x).set .x11 (OpeningRowData.addr x.data 3)
def m1278 (x : I) := (m1277 x).set .x12 (old x.data 3)
def m1279 (x : I) := (m1278 x).set .x14 (x.word 3 <<< off x.data)
def m1280 (x : I) := (m1279 x).set .x12 (merged x.data 3)
def m1281 (x : I) := withMem (m1280 x) (headMem x.data 3)

def codem : List Instr := [
  .LD .x17 .x14 0,
  Expr.instr .x5 (.sll .x12 .x15),
  Expr.instr .x17 (.or .x17 .x5),
  Expr.instr .x5 (.subw .x0 .x15),
  Expr.instr .x12 (.srl .x12 .x5),
  .SD .x14 .x12 8,
  .SD .x14 .x17 0,
  Expr.instr .x12 (.addi .x20 983),
  Expr.instr .x12 (.srli .x12 3),
  Expr.instr .x12 (.andi .x12 4088),
  Expr.instr .x12 (.add .x12 .x25),
  .LD .x14 .x12 0,
  Expr.instr .x17 (.sll .x11 .x15),
  Expr.instr .x14 (.or .x14 .x17),
  Expr.instr .x11 (.srl .x11 .x5),
  .SD .x12 .x11 8,
  .SD .x12 .x14 0,
  Expr.instr .x11 (.addi .x20 1047),
  Expr.instr .x11 (.srli .x11 3),
  Expr.instr .x11 (.andi .x11 4088),
  Expr.instr .x11 (.add .x11 .x25),
  .LD .x12 .x11 0,
  Expr.instr .x14 (.sll .x16 .x15),
  Expr.instr .x12 (.or .x12 .x14),
  Expr.instr .x14 (.srl .x16 .x5),
  .SD .x11 .x14 8,
  .SD .x11 .x12 0,
  Expr.instr .x11 (.addi .x20 1111),
  Expr.instr .x11 (.srli .x11 3),
  Expr.instr .x11 (.andi .x11 4088),
  Expr.instr .x11 (.add .x11 .x25),
  .LD .x12 .x11 0,
  Expr.instr .x14 (.sll .x13 .x15),
  Expr.instr .x12 (.or .x12 .x14),
  .SD .x11 .x12 0]
theorem tablem : OpeningStraight.Listed 1246 codem := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem spanm (o : Oracle) (x : I) (nz : off x.data≠0) : Contract o codem (entry x) (m1281 x) := by
  have h1246 := OpeningLinear.read o (entry x) .x17 .x14 0 (cell (atBit x.data 0)) (old x.data 0) (by have := within x.data 0 (by decide);omega) (OpeningRowOps.current x.data 0) rfl
  have h1247 := OpeningLinear.register o (m1247 x) .x5 (.sll .x12 .x15) (x.word 0 <<< off x.data) (OpeningRowOps.left x.data 0)
  have h1248 := OpeningLinear.register o (m1248 x) .x17 (.or .x17 .x5) (merged x.data 0) rfl
  have h1249 := OpeningLinear.register o (m1249 x) .x5 (.subw .x0 .x15) (((0 : BitVec 32)-(W (off x.data)).truncate 32).signExtend 64) rfl
  have h1250 := OpeningLinear.register o (m1250 x) .x12 (.srl .x12 .x5) (high x.data 0) (OpeningRowOps.rightNeg x.data 0 nz)
  have h1251 := OpeningRowData.storeAs o (m1251 x) .x14 .x12 8 (cell (atBit x.data 0)+1) (high x.data 0) (tailMem x.data 0) (within x.data 0 (by decide)) (OpeningRowOps.following x.data 0) rfl rfl
  have h1252 := OpeningRowData.storeAs o (m1252 x) .x14 .x17 0 (cell (atBit x.data 0)) (merged x.data 0) (before x.data 1) (by have := within x.data 0 (by decide);omega) (OpeningRowOps.current x.data 0) rfl (full x.data 0 (by decide) nz)
  have h1253 := OpeningLinear.register o (m1253 x) .x12 (.addi .x20 983) (W (atBit x.data 1)) (OpeningRowOps.plusBit x.root 2051 983 3034 983 rfl rfl)
  have h1254 := OpeningLinear.register o (m1254 x) .x12 (.srli .x12 3) (W (atBit x.data 1) >>> (3 : Nat)) rfl
  have h1255 := OpeningLinear.register o (m1255 x) .x12 (.andi .x12 4088) (((W (atBit x.data 1) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h1256 := OpeningLinear.register o (m1256 x) .x12 (.add .x12 .x25) (OpeningRowData.addr x.data 1) (OpeningRowOps.pointer x.data 1 (by decide))
  have h1257 := OpeningLinear.read o (m1257 x) .x14 .x12 0 (cell (atBit x.data 1)) (old x.data 1) (by have := within x.data 1 (by decide);omega) (OpeningRowOps.current x.data 1) rfl
  have h1258 := OpeningLinear.register o (m1258 x) .x17 (.sll .x11 .x15) (x.word 1 <<< off x.data) (OpeningRowOps.left x.data 1)
  have h1259 := OpeningLinear.register o (m1259 x) .x14 (.or .x14 .x17) (merged x.data 1) rfl
  have h1260 := OpeningLinear.register o (m1260 x) .x11 (.srl .x11 .x5) (high x.data 1) (OpeningRowOps.rightNeg x.data 1 nz)
  have h1261 := OpeningRowData.storeAs o (m1261 x) .x12 .x11 8 (cell (atBit x.data 1)+1) (high x.data 1) (tailMem x.data 1) (within x.data 1 (by decide)) (OpeningRowOps.following x.data 1) rfl rfl
  have h1262 := OpeningRowData.storeAs o (m1262 x) .x12 .x14 0 (cell (atBit x.data 1)) (merged x.data 1) (before x.data 2) (by have := within x.data 1 (by decide);omega) (OpeningRowOps.current x.data 1) rfl (full x.data 1 (by decide) nz)
  have h1263 := OpeningLinear.register o (m1263 x) .x11 (.addi .x20 1047) (W (atBit x.data 2)) (OpeningRowOps.plusBit x.root 2051 1047 3098 1047 rfl rfl)
  have h1264 := OpeningLinear.register o (m1264 x) .x11 (.srli .x11 3) (W (atBit x.data 2) >>> (3 : Nat)) rfl
  have h1265 := OpeningLinear.register o (m1265 x) .x11 (.andi .x11 4088) (((W (atBit x.data 2) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h1266 := OpeningLinear.register o (m1266 x) .x11 (.add .x11 .x25) (OpeningRowData.addr x.data 2) (OpeningRowOps.pointer x.data 2 (by decide))
  have h1267 := OpeningLinear.read o (m1267 x) .x12 .x11 0 (cell (atBit x.data 2)) (old x.data 2) (by have := within x.data 2 (by decide);omega) (OpeningRowOps.current x.data 2) rfl
  have h1268 := OpeningLinear.register o (m1268 x) .x14 (.sll .x16 .x15) (x.word 2 <<< off x.data) (OpeningRowOps.left x.data 2)
  have h1269 := OpeningLinear.register o (m1269 x) .x12 (.or .x12 .x14) (merged x.data 2) rfl
  have h1270 := OpeningLinear.register o (m1270 x) .x14 (.srl .x16 .x5) (high x.data 2) (OpeningRowOps.rightNeg x.data 2 nz)
  have h1271 := OpeningRowData.storeAs o (m1271 x) .x11 .x14 8 (cell (atBit x.data 2)+1) (high x.data 2) (tailMem x.data 2) (within x.data 2 (by decide)) (OpeningRowOps.following x.data 2) rfl rfl
  have h1272 := OpeningRowData.storeAs o (m1272 x) .x11 .x12 0 (cell (atBit x.data 2)) (merged x.data 2) (before x.data 3) (by have := within x.data 2 (by decide);omega) (OpeningRowOps.current x.data 2) rfl (full x.data 2 (by decide) nz)
  have h1273 := OpeningLinear.register o (m1273 x) .x11 (.addi .x20 1111) (W (atBit x.data 3)) (OpeningRowOps.plusBit x.root 2051 1111 3162 1111 rfl rfl)
  have h1274 := OpeningLinear.register o (m1274 x) .x11 (.srli .x11 3) (W (atBit x.data 3) >>> (3 : Nat)) rfl
  have h1275 := OpeningLinear.register o (m1275 x) .x11 (.andi .x11 4088) (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h1276 := OpeningLinear.register o (m1276 x) .x11 (.add .x11 .x25) (OpeningRowData.addr x.data 3) (OpeningRowOps.pointer x.data 3 (by decide))
  have h1277 := OpeningLinear.read o (m1277 x) .x12 .x11 0 (cell (atBit x.data 3)) (old x.data 3) (by have := within x.data 3 (by decide);omega) (OpeningRowOps.current x.data 3) rfl
  have h1278 := OpeningLinear.register o (m1278 x) .x14 (.sll .x13 .x15) (x.word 3 <<< off x.data) (OpeningRowOps.left x.data 3)
  have h1279 := OpeningLinear.register o (m1279 x) .x12 (.or .x12 .x14) (merged x.data 3) rfl
  have h1280 := OpeningRowData.storeAs o (m1280 x) .x11 .x12 0 (cell (atBit x.data 3)) (merged x.data 3) (headMem x.data 3) (by have := within x.data 3 (by decide);omega) (OpeningRowOps.current x.data 3) rfl rfl
  exact LeafModel.combine h1246 (LeafModel.combine h1247 (LeafModel.combine h1248 (LeafModel.combine h1249 (LeafModel.combine h1250 (LeafModel.combine h1251 (LeafModel.combine h1252 (LeafModel.combine h1253 (LeafModel.combine h1254 (LeafModel.combine h1255 (LeafModel.combine h1256 (LeafModel.combine h1257 (LeafModel.combine h1258 (LeafModel.combine h1259 (LeafModel.combine h1260 (LeafModel.combine h1261 (LeafModel.combine h1262 (LeafModel.combine h1263 (LeafModel.combine h1264 (LeafModel.combine h1265 (LeafModel.combine h1266 (LeafModel.combine h1267 (LeafModel.combine h1268 (LeafModel.combine h1269 (LeafModel.combine h1270 (LeafModel.combine h1271 (LeafModel.combine h1272 (LeafModel.combine h1273 (LeafModel.combine h1274 (LeafModel.combine h1275 (LeafModel.combine h1276 (LeafModel.combine h1277 (LeafModel.combine h1278 (LeafModel.combine h1279 (LeafModel.combine h1280 (LeafModel.empty _ _)))))))))))))))))))))))))))))))))))

def s1283 (x : I) := (m1281 x).set .x12 ((64 : Word)-W (off x.data))
def s1284 (x : I) := (s1283 x).set .x12 (high x.data 3)
def s1285 (x : I) := withMem (s1284 x) (before x.data 4)

def codes : List Instr := [
  Expr.instr .x12 (.sub .x18 .x15),
  Expr.instr .x12 (.srl .x13 .x12),
  .SD .x11 .x12 8]
theorem tables : OpeningStraight.Listed 1282 codes := ⟨rfl,rfl,rfl,True.intro⟩
theorem spans (o : Oracle) (x : I) (nz : off x.data≠0) (cross : 64<off x.data+x.data.bits) : Contract o codes (m1281 x) (s1285 x) := by
  have h1282 := OpeningLinear.register o (m1281 x) .x12 (.sub .x18 .x15) ((64 : Word)-W (off x.data)) rfl
  have h1283 := OpeningLinear.register o (s1283 x) .x12 (.srl .x13 .x12) (high x.data 3) (OpeningRowOps.rightSub x.data 3 nz)
  have h1284 := OpeningRowData.storeAs o (s1284 x) .x11 .x12 8 (cell (atBit x.data 3)+1) (high x.data 3) (before x.data 4) (within x.data 3 (by decide)) (OpeningRowOps.following x.data 3) rfl (crosses x.data nz cross)
  exact LeafModel.combine h1282 (LeafModel.combine h1283 (LeafModel.combine h1284 (LeafModel.empty _ _)))


def output (x : I) := if off x.data=0 then a1300 x else if off x.data<36 then m1281 x else s1285 x

theorem run (o : Oracle) (x : I) (u : MachineState) (pc : u.pc=CommitBlocks.addr 1245) (fit : Fits u (entry x)) :
    ∃ t n, n≤64 ∧ CommitExact.Segment o OpeningStraight.image n u t ∧ t.pc=CommitBlocks.addr 1300 ∧
      Fits t (output x) := by
  have zstep := zero_branch o u 1245 1246 1286 .x15 164 pc (by decide) rfl rfl rfl
    (W (off x.data)) (fit.registers _)
  have eqv : W (off x.data)=0 ↔ off x.data=0 := OpeningBranch.word_zero _
  simp only [eqv] at zstep
  unfold output
  by_cases z : off x.data=0
  · simp only [z,ite_true] at zstep ⊢
    obtain ⟨v,rv,pv,hv⟩ := OpeningLinear.block (spana o x z) (i:=1286) (by decide) tablea
      (u.setPC _) rfl (fit.pc _)
    exact ⟨v,1+codea.length,by change 15≤64;decide,CommitExact.compose zstep rv,pv,hv⟩
  · simp only [z,ite_false] at zstep ⊢
    obtain ⟨v,rv,pv,hv⟩ := OpeningLinear.block (spanm o x z) (i:=1246) (by decide) tablem (u.setPC _) rfl (fit.pc _)
    have branch := OpeningBranch.less o v .x15 .x7 1281 1300 76 pv (by decide) rfl rfl
      (off x.data) 36 (by unfold off;omega) (by decide) (hv.registers _) (hv.registers _)
    by_cases little : off x.data<36
    · simp only [little,ite_true] at branch ⊢
      exact ⟨_,1+codem.length+1,by change 37≤64;decide,CommitExact.compose (CommitExact.compose zstep rv) branch,rfl,hv.pc _⟩
    · simp only [little,ite_false] at branch ⊢
      have cross : 64<off x.data+x.data.bits := by change 64<off x.data+29;omega
      obtain ⟨w,rw,pw,hw⟩ := OpeningLinear.block (spans o x z cross) (i:=1282) (by decide) tables
        (v.setPC _) rfl (hv.pc _)
      have jump := OpeningBranch.jump o w 1285 1300 60 pw (by decide) rfl rfl
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

def changed : List Reg := [.x5,.x11,.x12,.x14,.x17]

theorem frame (x : I) (r : Reg) (h : r∉changed) : (output x).reg r=(entry x).reg r := by
  unfold output
  split
  · cases r <;> first | rfl | exact False.elim (h (by decide))
  · split <;> cases r <;> first | rfl | exact False.elim (h (by decide))

end CommitGolfCandidate.Reconstruction.OpeningRow12
