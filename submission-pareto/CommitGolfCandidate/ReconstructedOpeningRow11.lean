import CommitGolfCandidate.ReconstructedOpeningRowOps

namespace CommitGolfCandidate.Reconstruction.OpeningRow11
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningOps OpeningCursor OpeningPut OpeningRowData
open TwoPermutationPrototype.RV64
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000

abbrev I := OpeningRowOps.Input 3191 29
def entry (x : I) : Model := ⟨fun
  | .x0 => W 0
  | .x7 => W 36
  | .x11 => x.word 1
  | .x12 => x.word 3
  | .x13 => W (off x.data)
  | .x14 => x.word 0
  | .x15 => x.word 2
  | .x16 => OpeningRowData.addr x.data 0
  | .x18 => W 64
  | .x20 => W (x.root+2051)
  | .x25 => wordAddress OpeningPut.base
  | r => x.initial.reg r, x.initial.mem⟩

def a1355 (x : I) := withMem (entry x) (before x.data 1)
def a1356 (x : I) := (a1355 x).set .x13 (W (atBit x.data 1))
def a1357 (x : I) := (a1356 x).set .x13 (W (atBit x.data 1) >>> (3 : Nat))
def a1358 (x : I) := (a1357 x).set .x13 (OpeningRowData.addr x.data 1)
def a1359 (x : I) := withMem (a1358 x) (before x.data 2)
def a1360 (x : I) := (a1359 x).set .x11 (W (atBit x.data 2))
def a1361 (x : I) := (a1360 x).set .x11 (W (atBit x.data 2) >>> (3 : Nat))
def a1362 (x : I) := (a1361 x).set .x11 (OpeningRowData.addr x.data 2)
def a1363 (x : I) := withMem (a1362 x) (before x.data 3)
def a1364 (x : I) := (a1363 x).set .x11 (W (atBit x.data 3))
def a1365 (x : I) := (a1364 x).set .x11 (W (atBit x.data 3) >>> (3 : Nat))
def a1366 (x : I) := (a1365 x).set .x11 (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088))
def a1367 (x : I) := (a1366 x).set .x11 (OpeningRowData.addr x.data 3)
def a1368 (x : I) := withMem (a1367 x) (before x.data 4)

def codea : List Instr := [
  .SD .x16 .x14 0,
  Expr.instr .x13 (.addi .x20 1204),
  Expr.instr .x13 (.srli .x13 3),
  Expr.instr .x13 (.add .x13 .x25),
  .SD .x13 .x11 0,
  Expr.instr .x11 (.addi .x20 1268),
  Expr.instr .x11 (.srli .x11 3),
  Expr.instr .x11 (.add .x11 .x25),
  .SD .x11 .x15 0,
  Expr.instr .x11 (.addi .x20 1332),
  Expr.instr .x11 (.srli .x11 3),
  Expr.instr .x11 (.andi .x11 4088),
  Expr.instr .x11 (.add .x11 .x25),
  .SD .x11 .x12 0]
theorem tablea : OpeningStraight.Listed 1354 codea := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem spana (o : Oracle) (x : I) (align : off x.data=0) : Contract o codea (entry x) (a1368 x) := by
  have h1354 := OpeningRowData.storeAs o (entry x) .x16 .x14 0 (cell (atBit x.data 0)) (x.word 0) (before x.data 1) (by have := within x.data 0 (by decide);omega) (OpeningRowOps.current x.data 0) rfl (OpeningRowData.aligned x.data 0 align)
  have h1355 := OpeningLinear.register o (a1355 x) .x13 (.addi .x20 1204) (W (atBit x.data 1)) (OpeningRowOps.plusBit x.root 2051 1204 3255 1204 rfl rfl)
  have h1356 := OpeningLinear.register o (a1356 x) .x13 (.srli .x13 3) (W (atBit x.data 1) >>> (3 : Nat)) rfl
  have h1357 := OpeningLinear.register o (a1357 x) .x13 (.add .x13 .x25) (OpeningRowData.addr x.data 1) (OpeningRowOps.bare x.data 1 (by decide) align)
  have h1358 := OpeningRowData.storeAs o (a1358 x) .x13 .x11 0 (cell (atBit x.data 1)) (x.word 1) (before x.data 2) (by have := within x.data 1 (by decide);omega) (OpeningRowOps.current x.data 1) rfl (OpeningRowData.aligned x.data 1 align)
  have h1359 := OpeningLinear.register o (a1359 x) .x11 (.addi .x20 1268) (W (atBit x.data 2)) (OpeningRowOps.plusBit x.root 2051 1268 3319 1268 rfl rfl)
  have h1360 := OpeningLinear.register o (a1360 x) .x11 (.srli .x11 3) (W (atBit x.data 2) >>> (3 : Nat)) rfl
  have h1361 := OpeningLinear.register o (a1361 x) .x11 (.add .x11 .x25) (OpeningRowData.addr x.data 2) (OpeningRowOps.bare x.data 2 (by decide) align)
  have h1362 := OpeningRowData.storeAs o (a1362 x) .x11 .x15 0 (cell (atBit x.data 2)) (x.word 2) (before x.data 3) (by have := within x.data 2 (by decide);omega) (OpeningRowOps.current x.data 2) rfl (OpeningRowData.aligned x.data 2 align)
  have h1363 := OpeningLinear.register o (a1363 x) .x11 (.addi .x20 1332) (W (atBit x.data 3)) (OpeningRowOps.plusBit x.root 2051 1332 3383 1332 rfl rfl)
  have h1364 := OpeningLinear.register o (a1364 x) .x11 (.srli .x11 3) (W (atBit x.data 3) >>> (3 : Nat)) rfl
  have h1365 := OpeningLinear.register o (a1365 x) .x11 (.andi .x11 4088) (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h1366 := OpeningLinear.register o (a1366 x) .x11 (.add .x11 .x25) (OpeningRowData.addr x.data 3) (OpeningRowOps.pointer x.data 3 (by decide))
  have h1367 := OpeningRowData.storeAs o (a1367 x) .x11 .x12 0 (cell (atBit x.data 3)) (x.word 3) (before x.data 4) (by have := within x.data 3 (by decide);omega) (OpeningRowOps.current x.data 3) rfl (OpeningRowData.aligned x.data 3 align)
  exact LeafModel.combine h1354 (LeafModel.combine h1355 (LeafModel.combine h1356 (LeafModel.combine h1357 (LeafModel.combine h1358 (LeafModel.combine h1359 (LeafModel.combine h1360 (LeafModel.combine h1361 (LeafModel.combine h1362 (LeafModel.combine h1363 (LeafModel.combine h1364 (LeafModel.combine h1365 (LeafModel.combine h1366 (LeafModel.combine h1367 (LeafModel.empty _ _))))))))))))))

def m1315 (x : I) := (entry x).set .x17 (old x.data 0)
def m1316 (x : I) := (m1315 x).set .x5 (x.word 0 <<< off x.data)
def m1317 (x : I) := (m1316 x).set .x17 (merged x.data 0)
def m1318 (x : I) := (m1317 x).set .x5 (((0 : BitVec 32)-(W (off x.data)).truncate 32).signExtend 64)
def m1319 (x : I) := (m1318 x).set .x14 (high x.data 0)
def m1320 (x : I) := withMem (m1319 x) (tailMem x.data 0)
def m1321 (x : I) := withMem (m1320 x) (before x.data 1)
def m1322 (x : I) := (m1321 x).set .x14 (W (atBit x.data 1))
def m1323 (x : I) := (m1322 x).set .x14 (W (atBit x.data 1) >>> (3 : Nat))
def m1324 (x : I) := (m1323 x).set .x14 (((W (atBit x.data 1) >>> (3 : Nat)) &&& signExtend12 4088))
def m1325 (x : I) := (m1324 x).set .x14 (OpeningRowData.addr x.data 1)
def m1326 (x : I) := (m1325 x).set .x16 (old x.data 1)
def m1327 (x : I) := (m1326 x).set .x17 (x.word 1 <<< off x.data)
def m1328 (x : I) := (m1327 x).set .x16 (merged x.data 1)
def m1329 (x : I) := (m1328 x).set .x11 (high x.data 1)
def m1330 (x : I) := withMem (m1329 x) (tailMem x.data 1)
def m1331 (x : I) := withMem (m1330 x) (before x.data 2)
def m1332 (x : I) := (m1331 x).set .x11 (W (atBit x.data 2))
def m1333 (x : I) := (m1332 x).set .x11 (W (atBit x.data 2) >>> (3 : Nat))
def m1334 (x : I) := (m1333 x).set .x11 (((W (atBit x.data 2) >>> (3 : Nat)) &&& signExtend12 4088))
def m1335 (x : I) := (m1334 x).set .x11 (OpeningRowData.addr x.data 2)
def m1336 (x : I) := (m1335 x).set .x14 (old x.data 2)
def m1337 (x : I) := (m1336 x).set .x16 (x.word 2 <<< off x.data)
def m1338 (x : I) := (m1337 x).set .x14 (merged x.data 2)
def m1339 (x : I) := (m1338 x).set .x15 (high x.data 2)
def m1340 (x : I) := withMem (m1339 x) (tailMem x.data 2)
def m1341 (x : I) := withMem (m1340 x) (before x.data 3)
def m1342 (x : I) := (m1341 x).set .x11 (W (atBit x.data 3))
def m1343 (x : I) := (m1342 x).set .x11 (W (atBit x.data 3) >>> (3 : Nat))
def m1344 (x : I) := (m1343 x).set .x11 (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088))
def m1345 (x : I) := (m1344 x).set .x11 (OpeningRowData.addr x.data 3)
def m1346 (x : I) := (m1345 x).set .x14 (old x.data 3)
def m1347 (x : I) := (m1346 x).set .x15 (x.word 3 <<< off x.data)
def m1348 (x : I) := (m1347 x).set .x14 (merged x.data 3)
def m1349 (x : I) := withMem (m1348 x) (headMem x.data 3)

def codem : List Instr := [
  .LD .x17 .x16 0,
  Expr.instr .x5 (.sll .x14 .x13),
  Expr.instr .x17 (.or .x17 .x5),
  Expr.instr .x5 (.subw .x0 .x13),
  Expr.instr .x14 (.srl .x14 .x5),
  .SD .x16 .x14 8,
  .SD .x16 .x17 0,
  Expr.instr .x14 (.addi .x20 1204),
  Expr.instr .x14 (.srli .x14 3),
  Expr.instr .x14 (.andi .x14 4088),
  Expr.instr .x14 (.add .x14 .x25),
  .LD .x16 .x14 0,
  Expr.instr .x17 (.sll .x11 .x13),
  Expr.instr .x16 (.or .x16 .x17),
  Expr.instr .x11 (.srl .x11 .x5),
  .SD .x14 .x11 8,
  .SD .x14 .x16 0,
  Expr.instr .x11 (.addi .x20 1268),
  Expr.instr .x11 (.srli .x11 3),
  Expr.instr .x11 (.andi .x11 4088),
  Expr.instr .x11 (.add .x11 .x25),
  .LD .x14 .x11 0,
  Expr.instr .x16 (.sll .x15 .x13),
  Expr.instr .x14 (.or .x14 .x16),
  Expr.instr .x15 (.srl .x15 .x5),
  .SD .x11 .x15 8,
  .SD .x11 .x14 0,
  Expr.instr .x11 (.addi .x20 1332),
  Expr.instr .x11 (.srli .x11 3),
  Expr.instr .x11 (.andi .x11 4088),
  Expr.instr .x11 (.add .x11 .x25),
  .LD .x14 .x11 0,
  Expr.instr .x15 (.sll .x12 .x13),
  Expr.instr .x14 (.or .x14 .x15),
  .SD .x11 .x14 0]
theorem tablem : OpeningStraight.Listed 1314 codem := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem spanm (o : Oracle) (x : I) (nz : off x.data≠0) : Contract o codem (entry x) (m1349 x) := by
  have h1314 := OpeningLinear.read o (entry x) .x17 .x16 0 (cell (atBit x.data 0)) (old x.data 0) (by have := within x.data 0 (by decide);omega) (OpeningRowOps.current x.data 0) rfl
  have h1315 := OpeningLinear.register o (m1315 x) .x5 (.sll .x14 .x13) (x.word 0 <<< off x.data) (OpeningRowOps.left x.data 0)
  have h1316 := OpeningLinear.register o (m1316 x) .x17 (.or .x17 .x5) (merged x.data 0) rfl
  have h1317 := OpeningLinear.register o (m1317 x) .x5 (.subw .x0 .x13) (((0 : BitVec 32)-(W (off x.data)).truncate 32).signExtend 64) rfl
  have h1318 := OpeningLinear.register o (m1318 x) .x14 (.srl .x14 .x5) (high x.data 0) (OpeningRowOps.rightNeg x.data 0 nz)
  have h1319 := OpeningRowData.storeAs o (m1319 x) .x16 .x14 8 (cell (atBit x.data 0)+1) (high x.data 0) (tailMem x.data 0) (within x.data 0 (by decide)) (OpeningRowOps.following x.data 0) rfl rfl
  have h1320 := OpeningRowData.storeAs o (m1320 x) .x16 .x17 0 (cell (atBit x.data 0)) (merged x.data 0) (before x.data 1) (by have := within x.data 0 (by decide);omega) (OpeningRowOps.current x.data 0) rfl (full x.data 0 (by decide) nz)
  have h1321 := OpeningLinear.register o (m1321 x) .x14 (.addi .x20 1204) (W (atBit x.data 1)) (OpeningRowOps.plusBit x.root 2051 1204 3255 1204 rfl rfl)
  have h1322 := OpeningLinear.register o (m1322 x) .x14 (.srli .x14 3) (W (atBit x.data 1) >>> (3 : Nat)) rfl
  have h1323 := OpeningLinear.register o (m1323 x) .x14 (.andi .x14 4088) (((W (atBit x.data 1) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h1324 := OpeningLinear.register o (m1324 x) .x14 (.add .x14 .x25) (OpeningRowData.addr x.data 1) (OpeningRowOps.pointer x.data 1 (by decide))
  have h1325 := OpeningLinear.read o (m1325 x) .x16 .x14 0 (cell (atBit x.data 1)) (old x.data 1) (by have := within x.data 1 (by decide);omega) (OpeningRowOps.current x.data 1) rfl
  have h1326 := OpeningLinear.register o (m1326 x) .x17 (.sll .x11 .x13) (x.word 1 <<< off x.data) (OpeningRowOps.left x.data 1)
  have h1327 := OpeningLinear.register o (m1327 x) .x16 (.or .x16 .x17) (merged x.data 1) rfl
  have h1328 := OpeningLinear.register o (m1328 x) .x11 (.srl .x11 .x5) (high x.data 1) (OpeningRowOps.rightNeg x.data 1 nz)
  have h1329 := OpeningRowData.storeAs o (m1329 x) .x14 .x11 8 (cell (atBit x.data 1)+1) (high x.data 1) (tailMem x.data 1) (within x.data 1 (by decide)) (OpeningRowOps.following x.data 1) rfl rfl
  have h1330 := OpeningRowData.storeAs o (m1330 x) .x14 .x16 0 (cell (atBit x.data 1)) (merged x.data 1) (before x.data 2) (by have := within x.data 1 (by decide);omega) (OpeningRowOps.current x.data 1) rfl (full x.data 1 (by decide) nz)
  have h1331 := OpeningLinear.register o (m1331 x) .x11 (.addi .x20 1268) (W (atBit x.data 2)) (OpeningRowOps.plusBit x.root 2051 1268 3319 1268 rfl rfl)
  have h1332 := OpeningLinear.register o (m1332 x) .x11 (.srli .x11 3) (W (atBit x.data 2) >>> (3 : Nat)) rfl
  have h1333 := OpeningLinear.register o (m1333 x) .x11 (.andi .x11 4088) (((W (atBit x.data 2) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h1334 := OpeningLinear.register o (m1334 x) .x11 (.add .x11 .x25) (OpeningRowData.addr x.data 2) (OpeningRowOps.pointer x.data 2 (by decide))
  have h1335 := OpeningLinear.read o (m1335 x) .x14 .x11 0 (cell (atBit x.data 2)) (old x.data 2) (by have := within x.data 2 (by decide);omega) (OpeningRowOps.current x.data 2) rfl
  have h1336 := OpeningLinear.register o (m1336 x) .x16 (.sll .x15 .x13) (x.word 2 <<< off x.data) (OpeningRowOps.left x.data 2)
  have h1337 := OpeningLinear.register o (m1337 x) .x14 (.or .x14 .x16) (merged x.data 2) rfl
  have h1338 := OpeningLinear.register o (m1338 x) .x15 (.srl .x15 .x5) (high x.data 2) (OpeningRowOps.rightNeg x.data 2 nz)
  have h1339 := OpeningRowData.storeAs o (m1339 x) .x11 .x15 8 (cell (atBit x.data 2)+1) (high x.data 2) (tailMem x.data 2) (within x.data 2 (by decide)) (OpeningRowOps.following x.data 2) rfl rfl
  have h1340 := OpeningRowData.storeAs o (m1340 x) .x11 .x14 0 (cell (atBit x.data 2)) (merged x.data 2) (before x.data 3) (by have := within x.data 2 (by decide);omega) (OpeningRowOps.current x.data 2) rfl (full x.data 2 (by decide) nz)
  have h1341 := OpeningLinear.register o (m1341 x) .x11 (.addi .x20 1332) (W (atBit x.data 3)) (OpeningRowOps.plusBit x.root 2051 1332 3383 1332 rfl rfl)
  have h1342 := OpeningLinear.register o (m1342 x) .x11 (.srli .x11 3) (W (atBit x.data 3) >>> (3 : Nat)) rfl
  have h1343 := OpeningLinear.register o (m1343 x) .x11 (.andi .x11 4088) (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h1344 := OpeningLinear.register o (m1344 x) .x11 (.add .x11 .x25) (OpeningRowData.addr x.data 3) (OpeningRowOps.pointer x.data 3 (by decide))
  have h1345 := OpeningLinear.read o (m1345 x) .x14 .x11 0 (cell (atBit x.data 3)) (old x.data 3) (by have := within x.data 3 (by decide);omega) (OpeningRowOps.current x.data 3) rfl
  have h1346 := OpeningLinear.register o (m1346 x) .x15 (.sll .x12 .x13) (x.word 3 <<< off x.data) (OpeningRowOps.left x.data 3)
  have h1347 := OpeningLinear.register o (m1347 x) .x14 (.or .x14 .x15) (merged x.data 3) rfl
  have h1348 := OpeningRowData.storeAs o (m1348 x) .x11 .x14 0 (cell (atBit x.data 3)) (merged x.data 3) (headMem x.data 3) (by have := within x.data 3 (by decide);omega) (OpeningRowOps.current x.data 3) rfl rfl
  exact LeafModel.combine h1314 (LeafModel.combine h1315 (LeafModel.combine h1316 (LeafModel.combine h1317 (LeafModel.combine h1318 (LeafModel.combine h1319 (LeafModel.combine h1320 (LeafModel.combine h1321 (LeafModel.combine h1322 (LeafModel.combine h1323 (LeafModel.combine h1324 (LeafModel.combine h1325 (LeafModel.combine h1326 (LeafModel.combine h1327 (LeafModel.combine h1328 (LeafModel.combine h1329 (LeafModel.combine h1330 (LeafModel.combine h1331 (LeafModel.combine h1332 (LeafModel.combine h1333 (LeafModel.combine h1334 (LeafModel.combine h1335 (LeafModel.combine h1336 (LeafModel.combine h1337 (LeafModel.combine h1338 (LeafModel.combine h1339 (LeafModel.combine h1340 (LeafModel.combine h1341 (LeafModel.combine h1342 (LeafModel.combine h1343 (LeafModel.combine h1344 (LeafModel.combine h1345 (LeafModel.combine h1346 (LeafModel.combine h1347 (LeafModel.combine h1348 (LeafModel.empty _ _)))))))))))))))))))))))))))))))))))

def s1351 (x : I) := (m1349 x).set .x13 ((64 : Word)-W (off x.data))
def s1352 (x : I) := (s1351 x).set .x12 (high x.data 3)
def s1353 (x : I) := withMem (s1352 x) (before x.data 4)

def codes : List Instr := [
  Expr.instr .x13 (.sub .x18 .x13),
  Expr.instr .x12 (.srl .x12 .x13),
  .SD .x11 .x12 8]
theorem tables : OpeningStraight.Listed 1350 codes := ⟨rfl,rfl,rfl,True.intro⟩
theorem spans (o : Oracle) (x : I) (nz : off x.data≠0) (cross : 64<off x.data+x.data.bits) : Contract o codes (m1349 x) (s1353 x) := by
  have h1350 := OpeningLinear.register o (m1349 x) .x13 (.sub .x18 .x13) ((64 : Word)-W (off x.data)) rfl
  have h1351 := OpeningLinear.register o (s1351 x) .x12 (.srl .x12 .x13) (high x.data 3) (OpeningRowOps.rightSub x.data 3 nz)
  have h1352 := OpeningRowData.storeAs o (s1352 x) .x11 .x12 8 (cell (atBit x.data 3)+1) (high x.data 3) (before x.data 4) (within x.data 3 (by decide)) (OpeningRowOps.following x.data 3) rfl (crosses x.data nz cross)
  exact LeafModel.combine h1350 (LeafModel.combine h1351 (LeafModel.combine h1352 (LeafModel.empty _ _)))


def output (x : I) := if off x.data=0 then a1368 x else if off x.data<36 then m1349 x else s1353 x

theorem run (o : Oracle) (x : I) (u : MachineState) (pc : u.pc=CommitBlocks.addr 1313) (fit : Fits u (entry x)) :
    ∃ t n, n≤64 ∧ CommitExact.Segment o OpeningStraight.image n u t ∧ t.pc=CommitBlocks.addr 1368 ∧
      Fits t (output x) := by
  have zstep := zero_branch o u 1313 1314 1354 .x13 164 pc (by decide) rfl rfl rfl
    (W (off x.data)) (fit.registers _)
  have eqv : W (off x.data)=0 ↔ off x.data=0 := OpeningBranch.word_zero _
  simp only [eqv] at zstep
  unfold output
  by_cases z : off x.data=0
  · simp only [z,ite_true] at zstep ⊢
    obtain ⟨v,rv,pv,hv⟩ := OpeningLinear.block (spana o x z) (i:=1354) (by decide) tablea
      (u.setPC _) rfl (fit.pc _)
    exact ⟨v,1+codea.length,by change 15≤64;decide,CommitExact.compose zstep rv,pv,hv⟩
  · simp only [z,ite_false] at zstep ⊢
    obtain ⟨v,rv,pv,hv⟩ := OpeningLinear.block (spanm o x z) (i:=1314) (by decide) tablem (u.setPC _) rfl (fit.pc _)
    have branch := OpeningBranch.less o v .x13 .x7 1349 1368 76 pv (by decide) rfl rfl
      (off x.data) 36 (by unfold off;omega) (by decide) (hv.registers _) (hv.registers _)
    by_cases little : off x.data<36
    · simp only [little,ite_true] at branch ⊢
      exact ⟨_,1+codem.length+1,by change 37≤64;decide,CommitExact.compose (CommitExact.compose zstep rv) branch,rfl,hv.pc _⟩
    · simp only [little,ite_false] at branch ⊢
      have cross : 64<off x.data+x.data.bits := by change 64<off x.data+29;omega
      obtain ⟨w,rw,pw,hw⟩ := OpeningLinear.block (spans o x z cross) (i:=1350) (by decide) tables
        (v.setPC _) rfl (hv.pc _)
      have jump := OpeningBranch.jump o w 1353 1368 60 pw (by decide) rfl rfl
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

def changed : List Reg := [.x5,.x11,.x12,.x13,.x14,.x15,.x16,.x17]

theorem frame (x : I) (r : Reg) (h : r∉changed) : (output x).reg r=(entry x).reg r := by
  unfold output
  split
  · cases r <;> first | rfl | exact False.elim (h (by decide))
  · split <;> cases r <;> first | rfl | exact False.elim (h (by decide))

end CommitGolfCandidate.Reconstruction.OpeningRow11
