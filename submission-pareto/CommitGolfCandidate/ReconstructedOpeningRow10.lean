import CommitGolfCandidate.ReconstructedOpeningRowOps

namespace CommitGolfCandidate.Reconstruction.OpeningRow10
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningOps OpeningCursor OpeningPut OpeningRowData
open TwoPermutationPrototype.RV64
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000

abbrev I := OpeningRowOps.Input 3412 29
def entry (x : I) : Model := ⟨fun
  | .x0 => W 0
  | .x7 => W 36
  | .x8 => W 68719476336
  | .x11 => x.word 3
  | .x12 => W (off x.data)
  | .x13 => x.word 2
  | .x14 => x.word 1
  | .x15 => x.word 0
  | .x16 => OpeningRowData.addr x.data 0
  | .x18 => W 64
  | .x20 => W (x.root+2051)
  | .x25 => wordAddress OpeningPut.base
  | r => x.initial.reg r, x.initial.mem⟩

def a112 (x : I) := withMem (entry x) (before x.data 1)
def a113 (x : I) := (a112 x).set .x12 (W (atBit x.data 1))
def a114 (x : I) := (a113 x).set .x12 (W (atBit x.data 1) >>> (3 : Nat))
def a115 (x : I) := (a114 x).set .x12 (OpeningRowData.addr x.data 1)
def a116 (x : I) := withMem (a115 x) (before x.data 2)
def a117 (x : I) := (a116 x).set .x12 (W (atBit x.data 2))
def a118 (x : I) := (a117 x).set .x12 (W (atBit x.data 2) >>> (3 : Nat))
def a119 (x : I) := (a118 x).set .x12 (OpeningRowData.addr x.data 2)
def a120 (x : I) := withMem (a119 x) (before x.data 3)
def a121 (x : I) := (a120 x).set .x12 (W (atBit x.data 3))
def a122 (x : I) := (a121 x).set .x12 (W (atBit x.data 3) >>> (3 : Nat))
def a123 (x : I) := (a122 x).set .x12 (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088))
def a124 (x : I) := (a123 x).set .x12 (OpeningRowData.addr x.data 3)
def a125 (x : I) := withMem (a124 x) (before x.data 4)
def a126 (x : I) := (a125 x).set .x11 (W 4096)
def a127 (x : I) := (a126 x).set .x11 (W 68719472240)
def a128 (x : I) := (a127 x).set .x14 (x.initial.mem 8589934271)
def a129 (x : I) := (a128 x).set .x6 (W 68719474288)
def a130 (x : I) := (a129 x).set .x6 (W 68719474176)

def codea : List Instr := [
  .SD .x16 .x15 0,
  Expr.instr .x12 (.addi .x20 1425),
  Expr.instr .x12 (.srli .x12 3),
  Expr.instr .x12 (.add .x12 .x25),
  .SD .x12 .x14 0,
  Expr.instr .x12 (.addi .x20 1489),
  Expr.instr .x12 (.srli .x12 3),
  Expr.instr .x12 (.add .x12 .x25),
  .SD .x12 .x13 0,
  Expr.instr .x12 (.addi .x20 1553),
  Expr.instr .x12 (.srli .x12 3),
  Expr.instr .x12 (.andi .x12 4088),
  Expr.instr .x12 (.add .x12 .x25),
  .SD .x12 .x11 0,
  Expr.instr .x11 (.lui 1),
  Expr.instr .x11 (.sub .x8 .x11),
  .LD .x14 .x11 1928,
  Expr.instr .x6 (.addi .x8 2048),
  Expr.instr .x6 (.addi .x6 3984)]
theorem tablea : OpeningStraight.Listed 111 codea := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem spana (o : Oracle) (x : I) (align : off x.data=0) : Contract o codea (entry x) (a130 x) := by
  have h111 := OpeningRowData.storeAs o (entry x) .x16 .x15 0 (cell (atBit x.data 0)) (x.word 0) (before x.data 1) (by have := within x.data 0 (by decide);omega) (OpeningRowOps.current x.data 0) rfl (OpeningRowData.aligned x.data 0 align)
  have h112 := OpeningLinear.register o (a112 x) .x12 (.addi .x20 1425) (W (atBit x.data 1)) (OpeningRowOps.plusBit x.root 2051 1425 3476 1425 rfl rfl)
  have h113 := OpeningLinear.register o (a113 x) .x12 (.srli .x12 3) (W (atBit x.data 1) >>> (3 : Nat)) rfl
  have h114 := OpeningLinear.register o (a114 x) .x12 (.add .x12 .x25) (OpeningRowData.addr x.data 1) (OpeningRowOps.bare x.data 1 (by decide) align)
  have h115 := OpeningRowData.storeAs o (a115 x) .x12 .x14 0 (cell (atBit x.data 1)) (x.word 1) (before x.data 2) (by have := within x.data 1 (by decide);omega) (OpeningRowOps.current x.data 1) rfl (OpeningRowData.aligned x.data 1 align)
  have h116 := OpeningLinear.register o (a116 x) .x12 (.addi .x20 1489) (W (atBit x.data 2)) (OpeningRowOps.plusBit x.root 2051 1489 3540 1489 rfl rfl)
  have h117 := OpeningLinear.register o (a117 x) .x12 (.srli .x12 3) (W (atBit x.data 2) >>> (3 : Nat)) rfl
  have h118 := OpeningLinear.register o (a118 x) .x12 (.add .x12 .x25) (OpeningRowData.addr x.data 2) (OpeningRowOps.bare x.data 2 (by decide) align)
  have h119 := OpeningRowData.storeAs o (a119 x) .x12 .x13 0 (cell (atBit x.data 2)) (x.word 2) (before x.data 3) (by have := within x.data 2 (by decide);omega) (OpeningRowOps.current x.data 2) rfl (OpeningRowData.aligned x.data 2 align)
  have h120 := OpeningLinear.register o (a120 x) .x12 (.addi .x20 1553) (W (atBit x.data 3)) (OpeningRowOps.plusBit x.root 2051 1553 3604 1553 rfl rfl)
  have h121 := OpeningLinear.register o (a121 x) .x12 (.srli .x12 3) (W (atBit x.data 3) >>> (3 : Nat)) rfl
  have h122 := OpeningLinear.register o (a122 x) .x12 (.andi .x12 4088) (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h123 := OpeningLinear.register o (a123 x) .x12 (.add .x12 .x25) (OpeningRowData.addr x.data 3) (OpeningRowOps.pointer x.data 3 (by decide))
  have h124 := OpeningRowData.storeAs o (a124 x) .x12 .x11 0 (cell (atBit x.data 3)) (x.word 3) (before x.data 4) (by have := within x.data 3 (by decide);omega) (OpeningRowOps.current x.data 3) rfl (OpeningRowData.aligned x.data 3 align)
  have h125 := OpeningLinear.register o (a125 x) .x11 (.lui 1) (W 4096) rfl
  have h126 := OpeningLinear.register o (a126 x) .x11 (.sub .x8 .x11) (W 68719472240) (by change W 68719476336-W 4096=W 68719472240;decide)
  have h127 := OpeningLinear.read o (a127 x) .x14 .x11 1928 8589934271 (x.initial.mem 8589934271) (by decide) (by change (W 68719472240+signExtend12 1928)=wordAddress 8589934271;decide) (keep_before x.data 4 8589934271 (by decide) (Or.inr (by decide)))
  have h128 := OpeningLinear.register o (a128 x) .x6 (.addi .x8 2048) (W 68719474288) (by change W 68719476336+signExtend12 2048=W 68719474288;decide)
  have h129 := OpeningLinear.register o (a129 x) .x6 (.addi .x6 3984) (W 68719474176) (by change W 68719474288+signExtend12 3984=W 68719474176;decide)
  exact LeafModel.combine h111 (LeafModel.combine h112 (LeafModel.combine h113 (LeafModel.combine h114 (LeafModel.combine h115 (LeafModel.combine h116 (LeafModel.combine h117 (LeafModel.combine h118 (LeafModel.combine h119 (LeafModel.combine h120 (LeafModel.combine h121 (LeafModel.combine h122 (LeafModel.combine h123 (LeafModel.combine h124 (LeafModel.combine h125 (LeafModel.combine h126 (LeafModel.combine h127 (LeafModel.combine h128 (LeafModel.combine h129 (LeafModel.empty _ _)))))))))))))))))))

def m1384 (x : I) := (entry x).set .x17 (old x.data 0)
def m1385 (x : I) := (m1384 x).set .x5 (x.word 0 <<< off x.data)
def m1386 (x : I) := (m1385 x).set .x17 (merged x.data 0)
def m1387 (x : I) := (m1386 x).set .x5 (((0 : BitVec 32)-(W (off x.data)).truncate 32).signExtend 64)
def m1388 (x : I) := (m1387 x).set .x15 (high x.data 0)
def m1389 (x : I) := withMem (m1388 x) (tailMem x.data 0)
def m1390 (x : I) := withMem (m1389 x) (before x.data 1)
def m1391 (x : I) := (m1390 x).set .x15 (W (atBit x.data 1))
def m1392 (x : I) := (m1391 x).set .x15 (W (atBit x.data 1) >>> (3 : Nat))
def m1393 (x : I) := (m1392 x).set .x15 (((W (atBit x.data 1) >>> (3 : Nat)) &&& signExtend12 4088))
def m1394 (x : I) := (m1393 x).set .x15 (OpeningRowData.addr x.data 1)
def m1395 (x : I) := (m1394 x).set .x16 (old x.data 1)
def m1396 (x : I) := (m1395 x).set .x17 (x.word 1 <<< off x.data)
def m1397 (x : I) := (m1396 x).set .x16 (merged x.data 1)
def m1398 (x : I) := (m1397 x).set .x14 (high x.data 1)
def m1399 (x : I) := withMem (m1398 x) (tailMem x.data 1)
def m1400 (x : I) := withMem (m1399 x) (before x.data 2)
def m1401 (x : I) := (m1400 x).set .x14 (W (atBit x.data 2))
def m1402 (x : I) := (m1401 x).set .x14 (W (atBit x.data 2) >>> (3 : Nat))
def m1403 (x : I) := (m1402 x).set .x14 (((W (atBit x.data 2) >>> (3 : Nat)) &&& signExtend12 4088))
def m1404 (x : I) := (m1403 x).set .x14 (OpeningRowData.addr x.data 2)
def m1405 (x : I) := (m1404 x).set .x15 (old x.data 2)
def m1406 (x : I) := (m1405 x).set .x16 (x.word 2 <<< off x.data)
def m1407 (x : I) := (m1406 x).set .x15 (merged x.data 2)
def m1408 (x : I) := (m1407 x).set .x13 (high x.data 2)
def m1409 (x : I) := withMem (m1408 x) (tailMem x.data 2)
def m1410 (x : I) := withMem (m1409 x) (before x.data 3)
def m1411 (x : I) := (m1410 x).set .x13 (W (atBit x.data 3))
def m1412 (x : I) := (m1411 x).set .x13 (W (atBit x.data 3) >>> (3 : Nat))
def m1413 (x : I) := (m1412 x).set .x13 (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088))
def m1414 (x : I) := (m1413 x).set .x13 (OpeningRowData.addr x.data 3)
def m1415 (x : I) := (m1414 x).set .x14 (old x.data 3)
def m1416 (x : I) := (m1415 x).set .x15 (x.word 3 <<< off x.data)
def m1417 (x : I) := (m1416 x).set .x14 (merged x.data 3)
def m1418 (x : I) := withMem (m1417 x) (headMem x.data 3)
def m1419 (x : I) := (m1418 x).set .x14 (W 4096)
def m1420 (x : I) := (m1419 x).set .x14 (W 68719472240)
def m1421 (x : I) := (m1420 x).set .x14 (x.initial.mem 8589934271)
def m1422 (x : I) := (m1421 x).set .x6 (W 68719474288)
def m1423 (x : I) := (m1422 x).set .x6 (W 68719474176)

def codem : List Instr := [
  .LD .x17 .x16 0,
  Expr.instr .x5 (.sll .x15 .x12),
  Expr.instr .x17 (.or .x17 .x5),
  Expr.instr .x5 (.subw .x0 .x12),
  Expr.instr .x15 (.srl .x15 .x5),
  .SD .x16 .x15 8,
  .SD .x16 .x17 0,
  Expr.instr .x15 (.addi .x20 1425),
  Expr.instr .x15 (.srli .x15 3),
  Expr.instr .x15 (.andi .x15 4088),
  Expr.instr .x15 (.add .x15 .x25),
  .LD .x16 .x15 0,
  Expr.instr .x17 (.sll .x14 .x12),
  Expr.instr .x16 (.or .x16 .x17),
  Expr.instr .x14 (.srl .x14 .x5),
  .SD .x15 .x14 8,
  .SD .x15 .x16 0,
  Expr.instr .x14 (.addi .x20 1489),
  Expr.instr .x14 (.srli .x14 3),
  Expr.instr .x14 (.andi .x14 4088),
  Expr.instr .x14 (.add .x14 .x25),
  .LD .x15 .x14 0,
  Expr.instr .x16 (.sll .x13 .x12),
  Expr.instr .x15 (.or .x15 .x16),
  Expr.instr .x13 (.srl .x13 .x5),
  .SD .x14 .x13 8,
  .SD .x14 .x15 0,
  Expr.instr .x13 (.addi .x20 1553),
  Expr.instr .x13 (.srli .x13 3),
  Expr.instr .x13 (.andi .x13 4088),
  Expr.instr .x13 (.add .x13 .x25),
  .LD .x14 .x13 0,
  Expr.instr .x15 (.sll .x11 .x12),
  Expr.instr .x14 (.or .x14 .x15),
  .SD .x13 .x14 0,
  Expr.instr .x14 (.lui 1),
  Expr.instr .x14 (.sub .x8 .x14),
  .LD .x14 .x14 1928,
  Expr.instr .x6 (.addi .x8 2048),
  Expr.instr .x6 (.addi .x6 3984)]
theorem tablem : OpeningStraight.Listed 1383 codem := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem spanm (o : Oracle) (x : I) (nz : off x.data≠0) : Contract o codem (entry x) (m1423 x) := by
  have h1383 := OpeningLinear.read o (entry x) .x17 .x16 0 (cell (atBit x.data 0)) (old x.data 0) (by have := within x.data 0 (by decide);omega) (OpeningRowOps.current x.data 0) rfl
  have h1384 := OpeningLinear.register o (m1384 x) .x5 (.sll .x15 .x12) (x.word 0 <<< off x.data) (OpeningRowOps.left x.data 0)
  have h1385 := OpeningLinear.register o (m1385 x) .x17 (.or .x17 .x5) (merged x.data 0) rfl
  have h1386 := OpeningLinear.register o (m1386 x) .x5 (.subw .x0 .x12) (((0 : BitVec 32)-(W (off x.data)).truncate 32).signExtend 64) rfl
  have h1387 := OpeningLinear.register o (m1387 x) .x15 (.srl .x15 .x5) (high x.data 0) (OpeningRowOps.rightNeg x.data 0 nz)
  have h1388 := OpeningRowData.storeAs o (m1388 x) .x16 .x15 8 (cell (atBit x.data 0)+1) (high x.data 0) (tailMem x.data 0) (within x.data 0 (by decide)) (OpeningRowOps.following x.data 0) rfl rfl
  have h1389 := OpeningRowData.storeAs o (m1389 x) .x16 .x17 0 (cell (atBit x.data 0)) (merged x.data 0) (before x.data 1) (by have := within x.data 0 (by decide);omega) (OpeningRowOps.current x.data 0) rfl (full x.data 0 (by decide) nz)
  have h1390 := OpeningLinear.register o (m1390 x) .x15 (.addi .x20 1425) (W (atBit x.data 1)) (OpeningRowOps.plusBit x.root 2051 1425 3476 1425 rfl rfl)
  have h1391 := OpeningLinear.register o (m1391 x) .x15 (.srli .x15 3) (W (atBit x.data 1) >>> (3 : Nat)) rfl
  have h1392 := OpeningLinear.register o (m1392 x) .x15 (.andi .x15 4088) (((W (atBit x.data 1) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h1393 := OpeningLinear.register o (m1393 x) .x15 (.add .x15 .x25) (OpeningRowData.addr x.data 1) (OpeningRowOps.pointer x.data 1 (by decide))
  have h1394 := OpeningLinear.read o (m1394 x) .x16 .x15 0 (cell (atBit x.data 1)) (old x.data 1) (by have := within x.data 1 (by decide);omega) (OpeningRowOps.current x.data 1) rfl
  have h1395 := OpeningLinear.register o (m1395 x) .x17 (.sll .x14 .x12) (x.word 1 <<< off x.data) (OpeningRowOps.left x.data 1)
  have h1396 := OpeningLinear.register o (m1396 x) .x16 (.or .x16 .x17) (merged x.data 1) rfl
  have h1397 := OpeningLinear.register o (m1397 x) .x14 (.srl .x14 .x5) (high x.data 1) (OpeningRowOps.rightNeg x.data 1 nz)
  have h1398 := OpeningRowData.storeAs o (m1398 x) .x15 .x14 8 (cell (atBit x.data 1)+1) (high x.data 1) (tailMem x.data 1) (within x.data 1 (by decide)) (OpeningRowOps.following x.data 1) rfl rfl
  have h1399 := OpeningRowData.storeAs o (m1399 x) .x15 .x16 0 (cell (atBit x.data 1)) (merged x.data 1) (before x.data 2) (by have := within x.data 1 (by decide);omega) (OpeningRowOps.current x.data 1) rfl (full x.data 1 (by decide) nz)
  have h1400 := OpeningLinear.register o (m1400 x) .x14 (.addi .x20 1489) (W (atBit x.data 2)) (OpeningRowOps.plusBit x.root 2051 1489 3540 1489 rfl rfl)
  have h1401 := OpeningLinear.register o (m1401 x) .x14 (.srli .x14 3) (W (atBit x.data 2) >>> (3 : Nat)) rfl
  have h1402 := OpeningLinear.register o (m1402 x) .x14 (.andi .x14 4088) (((W (atBit x.data 2) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h1403 := OpeningLinear.register o (m1403 x) .x14 (.add .x14 .x25) (OpeningRowData.addr x.data 2) (OpeningRowOps.pointer x.data 2 (by decide))
  have h1404 := OpeningLinear.read o (m1404 x) .x15 .x14 0 (cell (atBit x.data 2)) (old x.data 2) (by have := within x.data 2 (by decide);omega) (OpeningRowOps.current x.data 2) rfl
  have h1405 := OpeningLinear.register o (m1405 x) .x16 (.sll .x13 .x12) (x.word 2 <<< off x.data) (OpeningRowOps.left x.data 2)
  have h1406 := OpeningLinear.register o (m1406 x) .x15 (.or .x15 .x16) (merged x.data 2) rfl
  have h1407 := OpeningLinear.register o (m1407 x) .x13 (.srl .x13 .x5) (high x.data 2) (OpeningRowOps.rightNeg x.data 2 nz)
  have h1408 := OpeningRowData.storeAs o (m1408 x) .x14 .x13 8 (cell (atBit x.data 2)+1) (high x.data 2) (tailMem x.data 2) (within x.data 2 (by decide)) (OpeningRowOps.following x.data 2) rfl rfl
  have h1409 := OpeningRowData.storeAs o (m1409 x) .x14 .x15 0 (cell (atBit x.data 2)) (merged x.data 2) (before x.data 3) (by have := within x.data 2 (by decide);omega) (OpeningRowOps.current x.data 2) rfl (full x.data 2 (by decide) nz)
  have h1410 := OpeningLinear.register o (m1410 x) .x13 (.addi .x20 1553) (W (atBit x.data 3)) (OpeningRowOps.plusBit x.root 2051 1553 3604 1553 rfl rfl)
  have h1411 := OpeningLinear.register o (m1411 x) .x13 (.srli .x13 3) (W (atBit x.data 3) >>> (3 : Nat)) rfl
  have h1412 := OpeningLinear.register o (m1412 x) .x13 (.andi .x13 4088) (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h1413 := OpeningLinear.register o (m1413 x) .x13 (.add .x13 .x25) (OpeningRowData.addr x.data 3) (OpeningRowOps.pointer x.data 3 (by decide))
  have h1414 := OpeningLinear.read o (m1414 x) .x14 .x13 0 (cell (atBit x.data 3)) (old x.data 3) (by have := within x.data 3 (by decide);omega) (OpeningRowOps.current x.data 3) rfl
  have h1415 := OpeningLinear.register o (m1415 x) .x15 (.sll .x11 .x12) (x.word 3 <<< off x.data) (OpeningRowOps.left x.data 3)
  have h1416 := OpeningLinear.register o (m1416 x) .x14 (.or .x14 .x15) (merged x.data 3) rfl
  have h1417 := OpeningRowData.storeAs o (m1417 x) .x13 .x14 0 (cell (atBit x.data 3)) (merged x.data 3) (headMem x.data 3) (by have := within x.data 3 (by decide);omega) (OpeningRowOps.current x.data 3) rfl rfl
  have h1418 := OpeningLinear.register o (m1418 x) .x14 (.lui 1) (W 4096) rfl
  have h1419 := OpeningLinear.register o (m1419 x) .x14 (.sub .x8 .x14) (W 68719472240) (by change W 68719476336-W 4096=W 68719472240;decide)
  have h1420 := OpeningLinear.read o (m1420 x) .x14 .x14 1928 8589934271 (x.initial.mem 8589934271) (by decide) (by change (W 68719472240+signExtend12 1928)=wordAddress 8589934271;decide) (keep_head x.data 3 8589934271 (by decide) (Or.inr (by decide)))
  have h1421 := OpeningLinear.register o (m1421 x) .x6 (.addi .x8 2048) (W 68719474288) (by change W 68719476336+signExtend12 2048=W 68719474288;decide)
  have h1422 := OpeningLinear.register o (m1422 x) .x6 (.addi .x6 3984) (W 68719474176) (by change W 68719474288+signExtend12 3984=W 68719474176;decide)
  exact LeafModel.combine h1383 (LeafModel.combine h1384 (LeafModel.combine h1385 (LeafModel.combine h1386 (LeafModel.combine h1387 (LeafModel.combine h1388 (LeafModel.combine h1389 (LeafModel.combine h1390 (LeafModel.combine h1391 (LeafModel.combine h1392 (LeafModel.combine h1393 (LeafModel.combine h1394 (LeafModel.combine h1395 (LeafModel.combine h1396 (LeafModel.combine h1397 (LeafModel.combine h1398 (LeafModel.combine h1399 (LeafModel.combine h1400 (LeafModel.combine h1401 (LeafModel.combine h1402 (LeafModel.combine h1403 (LeafModel.combine h1404 (LeafModel.combine h1405 (LeafModel.combine h1406 (LeafModel.combine h1407 (LeafModel.combine h1408 (LeafModel.combine h1409 (LeafModel.combine h1410 (LeafModel.combine h1411 (LeafModel.combine h1412 (LeafModel.combine h1413 (LeafModel.combine h1414 (LeafModel.combine h1415 (LeafModel.combine h1416 (LeafModel.combine h1417 (LeafModel.combine h1418 (LeafModel.combine h1419 (LeafModel.combine h1420 (LeafModel.combine h1421 (LeafModel.combine h1422 (LeafModel.empty _ _))))))))))))))))))))))))))))))))))))))))

def s1426 (x : I) := (m1423 x).set .x12 ((64 : Word)-W (off x.data))
def s1427 (x : I) := (s1426 x).set .x11 (high x.data 3)
def s1428 (x : I) := withMem (s1427 x) (before x.data 4)

def codes : List Instr := [
  Expr.instr .x12 (.sub .x18 .x12),
  Expr.instr .x11 (.srl .x11 .x12),
  .SD .x13 .x11 8]
theorem tables : OpeningStraight.Listed 1425 codes := ⟨rfl,rfl,rfl,True.intro⟩
theorem spans (o : Oracle) (x : I) (nz : off x.data≠0) (cross : 64<off x.data+x.data.bits) : Contract o codes (m1423 x) (s1428 x) := by
  have h1425 := OpeningLinear.register o (m1423 x) .x12 (.sub .x18 .x12) ((64 : Word)-W (off x.data)) rfl
  have h1426 := OpeningLinear.register o (s1426 x) .x11 (.srl .x11 .x12) (high x.data 3) (OpeningRowOps.rightSub x.data 3 nz)
  have h1427 := OpeningRowData.storeAs o (s1427 x) .x13 .x11 8 (cell (atBit x.data 3)+1) (high x.data 3) (before x.data 4) (within x.data 3 (by decide)) (OpeningRowOps.following x.data 3) rfl (crosses x.data nz cross)
  exact LeafModel.combine h1425 (LeafModel.combine h1426 (LeafModel.combine h1427 (LeafModel.empty _ _)))


def output (x : I) := if off x.data=0 then a130 x else if off x.data<36 then m1423 x else s1428 x

theorem run (o : Oracle) (x : I) (u : MachineState) (pc : u.pc=CommitBlocks.addr 1381) (fit : Fits u (entry x)) :
    ∃ t n, n≤64 ∧ CommitExact.Segment o OpeningStraight.image n u t ∧ t.pc=CommitBlocks.addr 130 ∧
      Fits t (output x) := by
  have zstep := OpeningBranch.nonzero o u 1381 1382 1383 .x12 8 pc (by decide) rfl rfl rfl
    (W (off x.data)) (fit.registers _)
  have eqv : W (off x.data)=0 ↔ off x.data=0 := OpeningBranch.word_zero _
  simp only [eqv] at zstep
  unfold output
  by_cases z : off x.data=0
  · simp only [z,ite_true] at zstep ⊢
    obtain ⟨v,rv,pv,hv⟩ := OpeningLinear.block (spana o x z) (i:=111) (by decide) tablea
      (u.setPC (CommitBlocks.addr 111)) rfl (fit.pc _)
    have jump := OpeningBranch.jump o (u.setPC (CommitBlocks.addr 1382)) 1382 111 2092068 rfl (by decide) rfl rfl
    exact ⟨v,1+1+codea.length,by decide,CommitExact.compose (CommitExact.compose zstep jump) rv,pv,hv⟩
  · simp only [z,ite_false] at zstep ⊢
    obtain ⟨v,rv,pv,hv⟩ := OpeningLinear.block (spanm o x z) (i:=1383) (by decide) tablem (u.setPC _) rfl (fit.pc _)
    have branch := OpeningBranch.atLeast o v .x12 .x7 1423 1425 8 pv (by decide) rfl rfl
      (off x.data) 36 (by unfold off;omega) (by decide) (hv.registers _) (hv.registers _)
    by_cases little : off x.data<36
    · simp only [little,ite_true] at branch ⊢
      have jump := OpeningBranch.jump o (v.setPC (CommitBlocks.addr 1424)) 1424 130 2091976 rfl (by decide) rfl rfl
      exact ⟨_,1+codem.length+1+1,by decide,CommitExact.compose (CommitExact.compose (CommitExact.compose zstep rv) branch) jump,rfl,hv.pc _⟩
    · simp only [little,ite_false] at branch ⊢
      have cross : 64<off x.data+x.data.bits := by change 64<off x.data+29;omega
      obtain ⟨w,rw,pw,hw⟩ := OpeningLinear.block (spans o x z cross) (i:=1425) (by decide) tables
        (v.setPC _) rfl (hv.pc _)
      have jump := OpeningBranch.jump o w 1428 130 2091960 pw (by decide) rfl rfl
      exact ⟨_,1+codem.length+1+codes.length+1,by decide,CommitExact.compose (CommitExact.compose (CommitExact.compose
        (CommitExact.compose zstep rv) branch) rw) jump,rfl,hw.pc _⟩

theorem memory (x : I) : (output x).mem=before x.data 4 := by
  unfold output
  split
  · rfl
  · rename_i nz;split
    · rename_i little
      exact short x.data nz (by change off x.data+29≤64;omega)
    · rfl

def changed : List Reg := [.x5,.x6,.x11,.x12,.x13,.x14,.x15,.x16,.x17]

theorem frame (x : I) (r : Reg) (h : r∉changed) : (output x).reg r=(entry x).reg r := by
  unfold output
  split
  · cases r <;> first | rfl | exact False.elim (h (by decide))
  · split <;> cases r <;> first | rfl | exact False.elim (h (by decide))

end CommitGolfCandidate.Reconstruction.OpeningRow10
