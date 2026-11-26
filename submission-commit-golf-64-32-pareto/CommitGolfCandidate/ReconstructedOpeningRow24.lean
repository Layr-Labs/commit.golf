import CommitGolfCandidate.ReconstructedOpeningRowOps

namespace CommitGolfCandidate.Reconstruction.OpeningRow24
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningOps OpeningCursor OpeningPut OpeningRowData
open TwoPermutationPrototype.RV64
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000

abbrev I := OpeningRowOps.Input 222 48
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
  | .x29 => x.word 0
  | .x30 => W (atBit x.data 1)
  | .x31 => OpeningRowData.addr x.data 0
  | r => x.initial.reg r, x.initial.mem⟩

def a475 (x : I) := withMem (entry x) (before x.data 1)
def a476 (x : I) := (a475 x).set .x13 (W (atBit x.data 1) >>> (3 : Nat))
def a477 (x : I) := (a476 x).set .x13 (OpeningRowData.addr x.data 1)
def a478 (x : I) := withMem (a477 x) (before x.data 2)
def a479 (x : I) := (a478 x).set .x12 (W (atBit x.data 2) >>> (3 : Nat))
def a480 (x : I) := (a479 x).set .x12 (OpeningRowData.addr x.data 2)
def a481 (x : I) := withMem (a480 x) (before x.data 3)
def a482 (x : I) := (a481 x).set .x11 (W (atBit x.data 3) >>> (3 : Nat))
def a483 (x : I) := (a482 x).set .x11 (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088))
def a484 (x : I) := (a483 x).set .x11 (OpeningRowData.addr x.data 3)
def a485 (x : I) := withMem (a484 x) (before x.data 4)

def codea : List Instr := [
  .SD .x31 .x29 0,
  Expr.instr .x13 (.srli .x30 3),
  Expr.instr .x13 (.add .x13 .x25),
  .SD .x13 .x12 0,
  Expr.instr .x12 (.srli .x6 3),
  Expr.instr .x12 (.add .x12 .x25),
  .SD .x12 .x14 0,
  Expr.instr .x11 (.srli .x11 3),
  Expr.instr .x11 (.andi .x11 4088),
  Expr.instr .x11 (.add .x11 .x25),
  .SD .x11 .x17 0]
theorem tablea : OpeningStraight.Listed 474 codea := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem spana (o : Oracle) (x : I) (align : off x.data=0) : Contract o codea (entry x) (a485 x) := by
  have h474 := OpeningRowData.storeAs o (entry x) .x31 .x29 0 (cell (atBit x.data 0)) (x.word 0) (before x.data 1) (by have := within x.data 0 (by decide);omega) (OpeningRowOps.current x.data 0) rfl (OpeningRowData.aligned x.data 0 align)
  have h475 := OpeningLinear.register o (a475 x) .x13 (.srli .x30 3) (W (atBit x.data 1) >>> (3 : Nat)) rfl
  have h476 := OpeningLinear.register o (a476 x) .x13 (.add .x13 .x25) (OpeningRowData.addr x.data 1) (OpeningRowOps.bare x.data 1 (by decide) align)
  have h477 := OpeningRowData.storeAs o (a477 x) .x13 .x12 0 (cell (atBit x.data 1)) (x.word 1) (before x.data 2) (by have := within x.data 1 (by decide);omega) (OpeningRowOps.current x.data 1) rfl (OpeningRowData.aligned x.data 1 align)
  have h478 := OpeningLinear.register o (a478 x) .x12 (.srli .x6 3) (W (atBit x.data 2) >>> (3 : Nat)) rfl
  have h479 := OpeningLinear.register o (a479 x) .x12 (.add .x12 .x25) (OpeningRowData.addr x.data 2) (OpeningRowOps.bare x.data 2 (by decide) align)
  have h480 := OpeningRowData.storeAs o (a480 x) .x12 .x14 0 (cell (atBit x.data 2)) (x.word 2) (before x.data 3) (by have := within x.data 2 (by decide);omega) (OpeningRowOps.current x.data 2) rfl (OpeningRowData.aligned x.data 2 align)
  have h481 := OpeningLinear.register o (a481 x) .x11 (.srli .x11 3) (W (atBit x.data 3) >>> (3 : Nat)) rfl
  have h482 := OpeningLinear.register o (a482 x) .x11 (.andi .x11 4088) (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h483 := OpeningLinear.register o (a483 x) .x11 (.add .x11 .x25) (OpeningRowData.addr x.data 3) (OpeningRowOps.pointer x.data 3 (by decide))
  have h484 := OpeningRowData.storeAs o (a484 x) .x11 .x17 0 (cell (atBit x.data 3)) (x.word 3) (before x.data 4) (by have := within x.data 3 (by decide);omega) (OpeningRowOps.current x.data 3) rfl (OpeningRowData.aligned x.data 3 align)
  exact LeafModel.combine h474 (LeafModel.combine h475 (LeafModel.combine h476 (LeafModel.combine h477 (LeafModel.combine h478 (LeafModel.combine h479 (LeafModel.combine h480 (LeafModel.combine h481 (LeafModel.combine h482 (LeafModel.combine h483 (LeafModel.combine h484 (LeafModel.empty _ _)))))))))))

def m437 (x : I) := (entry x).set .x13 (old x.data 0)
def m438 (x : I) := (m437 x).set .x5 (x.word 0 <<< off x.data)
def m439 (x : I) := (m438 x).set .x13 (merged x.data 0)
def m440 (x : I) := (m439 x).set .x5 (((0 : BitVec 32)-(W (off x.data)).truncate 32).signExtend 64)
def m441 (x : I) := (m440 x).set .x29 (high x.data 0)
def m442 (x : I) := withMem (m441 x) (tailMem x.data 0)
def m443 (x : I) := withMem (m442 x) (before x.data 1)
def m444 (x : I) := (m443 x).set .x13 (W (atBit x.data 1) >>> (3 : Nat))
def m445 (x : I) := (m444 x).set .x13 (((W (atBit x.data 1) >>> (3 : Nat)) &&& signExtend12 4088))
def m446 (x : I) := (m445 x).set .x13 (OpeningRowData.addr x.data 1)
def m447 (x : I) := (m446 x).set .x29 (old x.data 1)
def m448 (x : I) := (m447 x).set .x30 (x.word 1 <<< off x.data)
def m449 (x : I) := (m448 x).set .x29 (merged x.data 1)
def m450 (x : I) := (m449 x).set .x12 (high x.data 1)
def m451 (x : I) := withMem (m450 x) (tailMem x.data 1)
def m452 (x : I) := withMem (m451 x) (before x.data 2)
def m453 (x : I) := (m452 x).set .x12 (W (atBit x.data 2) >>> (3 : Nat))
def m454 (x : I) := (m453 x).set .x12 (((W (atBit x.data 2) >>> (3 : Nat)) &&& signExtend12 4088))
def m455 (x : I) := (m454 x).set .x12 (OpeningRowData.addr x.data 2)
def m456 (x : I) := (m455 x).set .x13 (old x.data 2)
def m457 (x : I) := (m456 x).set .x6 (x.word 2 <<< off x.data)
def m458 (x : I) := (m457 x).set .x13 (merged x.data 2)
def m459 (x : I) := (m458 x).set .x14 (high x.data 2)
def m460 (x : I) := withMem (m459 x) (tailMem x.data 2)
def m461 (x : I) := withMem (m460 x) (before x.data 3)
def m462 (x : I) := (m461 x).set .x11 (W (atBit x.data 3) >>> (3 : Nat))
def m463 (x : I) := (m462 x).set .x11 (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088))
def m464 (x : I) := (m463 x).set .x11 (OpeningRowData.addr x.data 3)
def m465 (x : I) := (m464 x).set .x12 (old x.data 3)
def m466 (x : I) := (m465 x).set .x13 (x.word 3 <<< off x.data)
def m467 (x : I) := (m466 x).set .x12 (merged x.data 3)
def m468 (x : I) := withMem (m467 x) (headMem x.data 3)
def m469 (x : I) := (m468 x).set .x12 (W 17)

def codem : List Instr := [
  .LD .x13 .x31 0,
  Expr.instr .x5 (.sll .x29 .x16),
  Expr.instr .x13 (.or .x13 .x5),
  Expr.instr .x5 (.subw .x0 .x16),
  Expr.instr .x29 (.srl .x29 .x5),
  .SD .x31 .x29 8,
  .SD .x31 .x13 0,
  Expr.instr .x13 (.srli .x30 3),
  Expr.instr .x13 (.andi .x13 4088),
  Expr.instr .x13 (.add .x13 .x25),
  .LD .x29 .x13 0,
  Expr.instr .x30 (.sll .x12 .x16),
  Expr.instr .x29 (.or .x29 .x30),
  Expr.instr .x12 (.srl .x12 .x5),
  .SD .x13 .x12 8,
  .SD .x13 .x29 0,
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
  Expr.instr .x12 (.addi .x0 17)]
theorem tablem : OpeningStraight.Listed 436 codem := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem spanm (o : Oracle) (x : I) (nz : off x.data≠0) : Contract o codem (entry x) (m469 x) := by
  have h436 := OpeningLinear.read o (entry x) .x13 .x31 0 (cell (atBit x.data 0)) (old x.data 0) (by have := within x.data 0 (by decide);omega) (OpeningRowOps.current x.data 0) rfl
  have h437 := OpeningLinear.register o (m437 x) .x5 (.sll .x29 .x16) (x.word 0 <<< off x.data) (OpeningRowOps.left x.data 0)
  have h438 := OpeningLinear.register o (m438 x) .x13 (.or .x13 .x5) (merged x.data 0) rfl
  have h439 := OpeningLinear.register o (m439 x) .x5 (.subw .x0 .x16) (((0 : BitVec 32)-(W (off x.data)).truncate 32).signExtend 64) rfl
  have h440 := OpeningLinear.register o (m440 x) .x29 (.srl .x29 .x5) (high x.data 0) (OpeningRowOps.rightNeg x.data 0 nz)
  have h441 := OpeningRowData.storeAs o (m441 x) .x31 .x29 8 (cell (atBit x.data 0)+1) (high x.data 0) (tailMem x.data 0) (within x.data 0 (by decide)) (OpeningRowOps.following x.data 0) rfl rfl
  have h442 := OpeningRowData.storeAs o (m442 x) .x31 .x13 0 (cell (atBit x.data 0)) (merged x.data 0) (before x.data 1) (by have := within x.data 0 (by decide);omega) (OpeningRowOps.current x.data 0) rfl (full x.data 0 (by decide) nz)
  have h443 := OpeningLinear.register o (m443 x) .x13 (.srli .x30 3) (W (atBit x.data 1) >>> (3 : Nat)) rfl
  have h444 := OpeningLinear.register o (m444 x) .x13 (.andi .x13 4088) (((W (atBit x.data 1) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h445 := OpeningLinear.register o (m445 x) .x13 (.add .x13 .x25) (OpeningRowData.addr x.data 1) (OpeningRowOps.pointer x.data 1 (by decide))
  have h446 := OpeningLinear.read o (m446 x) .x29 .x13 0 (cell (atBit x.data 1)) (old x.data 1) (by have := within x.data 1 (by decide);omega) (OpeningRowOps.current x.data 1) rfl
  have h447 := OpeningLinear.register o (m447 x) .x30 (.sll .x12 .x16) (x.word 1 <<< off x.data) (OpeningRowOps.left x.data 1)
  have h448 := OpeningLinear.register o (m448 x) .x29 (.or .x29 .x30) (merged x.data 1) rfl
  have h449 := OpeningLinear.register o (m449 x) .x12 (.srl .x12 .x5) (high x.data 1) (OpeningRowOps.rightNeg x.data 1 nz)
  have h450 := OpeningRowData.storeAs o (m450 x) .x13 .x12 8 (cell (atBit x.data 1)+1) (high x.data 1) (tailMem x.data 1) (within x.data 1 (by decide)) (OpeningRowOps.following x.data 1) rfl rfl
  have h451 := OpeningRowData.storeAs o (m451 x) .x13 .x29 0 (cell (atBit x.data 1)) (merged x.data 1) (before x.data 2) (by have := within x.data 1 (by decide);omega) (OpeningRowOps.current x.data 1) rfl (full x.data 1 (by decide) nz)
  have h452 := OpeningLinear.register o (m452 x) .x12 (.srli .x6 3) (W (atBit x.data 2) >>> (3 : Nat)) rfl
  have h453 := OpeningLinear.register o (m453 x) .x12 (.andi .x12 4088) (((W (atBit x.data 2) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h454 := OpeningLinear.register o (m454 x) .x12 (.add .x12 .x25) (OpeningRowData.addr x.data 2) (OpeningRowOps.pointer x.data 2 (by decide))
  have h455 := OpeningLinear.read o (m455 x) .x13 .x12 0 (cell (atBit x.data 2)) (old x.data 2) (by have := within x.data 2 (by decide);omega) (OpeningRowOps.current x.data 2) rfl
  have h456 := OpeningLinear.register o (m456 x) .x6 (.sll .x14 .x16) (x.word 2 <<< off x.data) (OpeningRowOps.left x.data 2)
  have h457 := OpeningLinear.register o (m457 x) .x13 (.or .x13 .x6) (merged x.data 2) rfl
  have h458 := OpeningLinear.register o (m458 x) .x14 (.srl .x14 .x5) (high x.data 2) (OpeningRowOps.rightNeg x.data 2 nz)
  have h459 := OpeningRowData.storeAs o (m459 x) .x12 .x14 8 (cell (atBit x.data 2)+1) (high x.data 2) (tailMem x.data 2) (within x.data 2 (by decide)) (OpeningRowOps.following x.data 2) rfl rfl
  have h460 := OpeningRowData.storeAs o (m460 x) .x12 .x13 0 (cell (atBit x.data 2)) (merged x.data 2) (before x.data 3) (by have := within x.data 2 (by decide);omega) (OpeningRowOps.current x.data 2) rfl (full x.data 2 (by decide) nz)
  have h461 := OpeningLinear.register o (m461 x) .x11 (.srli .x11 3) (W (atBit x.data 3) >>> (3 : Nat)) rfl
  have h462 := OpeningLinear.register o (m462 x) .x11 (.andi .x11 4088) (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h463 := OpeningLinear.register o (m463 x) .x11 (.add .x11 .x25) (OpeningRowData.addr x.data 3) (OpeningRowOps.pointer x.data 3 (by decide))
  have h464 := OpeningLinear.read o (m464 x) .x12 .x11 0 (cell (atBit x.data 3)) (old x.data 3) (by have := within x.data 3 (by decide);omega) (OpeningRowOps.current x.data 3) rfl
  have h465 := OpeningLinear.register o (m465 x) .x13 (.sll .x17 .x16) (x.word 3 <<< off x.data) (OpeningRowOps.left x.data 3)
  have h466 := OpeningLinear.register o (m466 x) .x12 (.or .x12 .x13) (merged x.data 3) rfl
  have h467 := OpeningRowData.storeAs o (m467 x) .x11 .x12 0 (cell (atBit x.data 3)) (merged x.data 3) (headMem x.data 3) (by have := within x.data 3 (by decide);omega) (OpeningRowOps.current x.data 3) rfl rfl
  have h468 := OpeningLinear.register o (m468 x) .x12 (.addi .x0 17) (W 17) rfl
  exact LeafModel.combine h436 (LeafModel.combine h437 (LeafModel.combine h438 (LeafModel.combine h439 (LeafModel.combine h440 (LeafModel.combine h441 (LeafModel.combine h442 (LeafModel.combine h443 (LeafModel.combine h444 (LeafModel.combine h445 (LeafModel.combine h446 (LeafModel.combine h447 (LeafModel.combine h448 (LeafModel.combine h449 (LeafModel.combine h450 (LeafModel.combine h451 (LeafModel.combine h452 (LeafModel.combine h453 (LeafModel.combine h454 (LeafModel.combine h455 (LeafModel.combine h456 (LeafModel.combine h457 (LeafModel.combine h458 (LeafModel.combine h459 (LeafModel.combine h460 (LeafModel.combine h461 (LeafModel.combine h462 (LeafModel.combine h463 (LeafModel.combine h464 (LeafModel.combine h465 (LeafModel.combine h466 (LeafModel.combine h467 (LeafModel.combine h468 (LeafModel.empty _ _)))))))))))))))))))))))))))))))))

def s471 (x : I) := (m469 x).set .x12 ((64 : Word)-W (off x.data))
def s472 (x : I) := (s471 x).set .x12 (high x.data 3)
def s473 (x : I) := withMem (s472 x) (before x.data 4)

def codes : List Instr := [
  Expr.instr .x12 (.sub .x18 .x16),
  Expr.instr .x12 (.srl .x17 .x12),
  .SD .x11 .x12 8]
theorem tables : OpeningStraight.Listed 470 codes := ⟨rfl,rfl,rfl,True.intro⟩
theorem spans (o : Oracle) (x : I) (nz : off x.data≠0) (cross : 64<off x.data+x.data.bits) : Contract o codes (m469 x) (s473 x) := by
  have h470 := OpeningLinear.register o (m469 x) .x12 (.sub .x18 .x16) ((64 : Word)-W (off x.data)) rfl
  have h471 := OpeningLinear.register o (s471 x) .x12 (.srl .x17 .x12) (high x.data 3) (OpeningRowOps.rightSub x.data 3 nz)
  have h472 := OpeningRowData.storeAs o (s472 x) .x11 .x12 8 (cell (atBit x.data 3)+1) (high x.data 3) (before x.data 4) (within x.data 3 (by decide)) (OpeningRowOps.following x.data 3) rfl (crosses x.data nz cross)
  exact LeafModel.combine h470 (LeafModel.combine h471 (LeafModel.combine h472 (LeafModel.empty _ _)))


def output (x : I) := if off x.data=0 then a485 x else if off x.data<17 then m469 x else s473 x

theorem run (o : Oracle) (x : I) (u : MachineState) (pc : u.pc=CommitBlocks.addr 435) (fit : Fits u (entry x)) :
    ∃ t n, n≤64 ∧ CommitExact.Segment o OpeningStraight.image n u t ∧ t.pc=CommitBlocks.addr 485 ∧
      Fits t (output x) := by
  have zstep := zero_branch o u 435 436 474 .x16 156 pc (by decide) rfl rfl rfl
    (W (off x.data)) (fit.registers _)
  have eqv : W (off x.data)=0 ↔ off x.data=0 := OpeningBranch.word_zero _
  simp only [eqv] at zstep
  unfold output
  by_cases z : off x.data=0
  · simp only [z,ite_true] at zstep ⊢
    obtain ⟨v,rv,pv,hv⟩ := OpeningLinear.block (spana o x z) (i:=474) (by decide) tablea
      (u.setPC _) rfl (fit.pc _)
    exact ⟨v,1+codea.length,by change 12≤64;decide,CommitExact.compose zstep rv,pv,hv⟩
  · simp only [z,ite_false] at zstep ⊢
    obtain ⟨v,rv,pv,hv⟩ := OpeningLinear.block (spanm o x z) (i:=436) (by decide) tablem (u.setPC _) rfl (fit.pc _)
    have branch := OpeningBranch.less o v .x16 .x12 469 485 64 pv (by decide) rfl rfl
      (off x.data) 17 (by unfold off;omega) (by decide) (hv.registers _) (hv.registers _)
    by_cases little : off x.data<17
    · simp only [little,ite_true] at branch ⊢
      exact ⟨_,1+codem.length+1,by change 35≤64;decide,CommitExact.compose (CommitExact.compose zstep rv) branch,rfl,hv.pc _⟩
    · simp only [little,ite_false] at branch ⊢
      have cross : 64<off x.data+x.data.bits := by change 64<off x.data+48;omega
      obtain ⟨w,rw,pw,hw⟩ := OpeningLinear.block (spans o x z cross) (i:=470) (by decide) tables
        (v.setPC _) rfl (hv.pc _)
      have jump := OpeningBranch.jump o w 473 485 48 pw (by decide) rfl rfl
      exact ⟨_,1+codem.length+1+codes.length+1,by change 39≤64;decide,CommitExact.compose (CommitExact.compose (CommitExact.compose
        (CommitExact.compose zstep rv) branch) rw) jump,rfl,hw.pc _⟩

theorem memory (x : I) : (output x).mem=before x.data 4 := by
  unfold output
  split
  · rfl
  · rename_i nz;split
    · rename_i little
      exact short x.data nz (by change off x.data+48≤64;omega)
    · rfl

def changed : List Reg := [.x5,.x6,.x11,.x12,.x13,.x14,.x29,.x30]

theorem frame (x : I) (r : Reg) (h : r∉changed) : (output x).reg r=(entry x).reg r := by
  unfold output
  split
  · cases r <;> first | rfl | exact False.elim (h (by decide))
  · split <;> cases r <;> first | rfl | exact False.elim (h (by decide))

end CommitGolfCandidate.Reconstruction.OpeningRow24
