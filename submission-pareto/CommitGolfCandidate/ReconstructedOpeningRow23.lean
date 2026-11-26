import CommitGolfCandidate.ReconstructedOpeningRowOps

namespace CommitGolfCandidate.Reconstruction.OpeningRow23
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningOps OpeningCursor OpeningPut OpeningRowData
open TwoPermutationPrototype.RV64
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000

abbrev I := OpeningRowOps.Input 462 46
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

def a542 (x : I) := withMem (entry x) (before x.data 1)
def a543 (x : I) := (a542 x).set .x13 (W (atBit x.data 1) >>> (3 : Nat))
def a544 (x : I) := (a543 x).set .x13 (OpeningRowData.addr x.data 1)
def a545 (x : I) := withMem (a544 x) (before x.data 2)
def a546 (x : I) := (a545 x).set .x12 (W (atBit x.data 2) >>> (3 : Nat))
def a547 (x : I) := (a546 x).set .x12 (OpeningRowData.addr x.data 2)
def a548 (x : I) := withMem (a547 x) (before x.data 3)
def a549 (x : I) := (a548 x).set .x11 (W (atBit x.data 3) >>> (3 : Nat))
def a550 (x : I) := (a549 x).set .x11 (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088))
def a551 (x : I) := (a550 x).set .x11 (OpeningRowData.addr x.data 3)
def a552 (x : I) := withMem (a551 x) (before x.data 4)

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
theorem tablea : OpeningStraight.Listed 541 codea := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem spana (o : Oracle) (x : I) (align : off x.data=0) : Contract o codea (entry x) (a552 x) := by
  have h541 := OpeningRowData.storeAs o (entry x) .x31 .x29 0 (cell (atBit x.data 0)) (x.word 0) (before x.data 1) (by have := within x.data 0 (by decide);omega) (OpeningRowOps.current x.data 0) rfl (OpeningRowData.aligned x.data 0 align)
  have h542 := OpeningLinear.register o (a542 x) .x13 (.srli .x30 3) (W (atBit x.data 1) >>> (3 : Nat)) rfl
  have h543 := OpeningLinear.register o (a543 x) .x13 (.add .x13 .x25) (OpeningRowData.addr x.data 1) (OpeningRowOps.bare x.data 1 (by decide) align)
  have h544 := OpeningRowData.storeAs o (a544 x) .x13 .x12 0 (cell (atBit x.data 1)) (x.word 1) (before x.data 2) (by have := within x.data 1 (by decide);omega) (OpeningRowOps.current x.data 1) rfl (OpeningRowData.aligned x.data 1 align)
  have h545 := OpeningLinear.register o (a545 x) .x12 (.srli .x6 3) (W (atBit x.data 2) >>> (3 : Nat)) rfl
  have h546 := OpeningLinear.register o (a546 x) .x12 (.add .x12 .x25) (OpeningRowData.addr x.data 2) (OpeningRowOps.bare x.data 2 (by decide) align)
  have h547 := OpeningRowData.storeAs o (a547 x) .x12 .x14 0 (cell (atBit x.data 2)) (x.word 2) (before x.data 3) (by have := within x.data 2 (by decide);omega) (OpeningRowOps.current x.data 2) rfl (OpeningRowData.aligned x.data 2 align)
  have h548 := OpeningLinear.register o (a548 x) .x11 (.srli .x11 3) (W (atBit x.data 3) >>> (3 : Nat)) rfl
  have h549 := OpeningLinear.register o (a549 x) .x11 (.andi .x11 4088) (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h550 := OpeningLinear.register o (a550 x) .x11 (.add .x11 .x25) (OpeningRowData.addr x.data 3) (OpeningRowOps.pointer x.data 3 (by decide))
  have h551 := OpeningRowData.storeAs o (a551 x) .x11 .x17 0 (cell (atBit x.data 3)) (x.word 3) (before x.data 4) (by have := within x.data 3 (by decide);omega) (OpeningRowOps.current x.data 3) rfl (OpeningRowData.aligned x.data 3 align)
  exact LeafModel.combine h541 (LeafModel.combine h542 (LeafModel.combine h543 (LeafModel.combine h544 (LeafModel.combine h545 (LeafModel.combine h546 (LeafModel.combine h547 (LeafModel.combine h548 (LeafModel.combine h549 (LeafModel.combine h550 (LeafModel.combine h551 (LeafModel.empty _ _)))))))))))

def m504 (x : I) := (entry x).set .x13 (old x.data 0)
def m505 (x : I) := (m504 x).set .x5 (x.word 0 <<< off x.data)
def m506 (x : I) := (m505 x).set .x13 (merged x.data 0)
def m507 (x : I) := (m506 x).set .x5 (((0 : BitVec 32)-(W (off x.data)).truncate 32).signExtend 64)
def m508 (x : I) := (m507 x).set .x29 (high x.data 0)
def m509 (x : I) := withMem (m508 x) (tailMem x.data 0)
def m510 (x : I) := withMem (m509 x) (before x.data 1)
def m511 (x : I) := (m510 x).set .x13 (W (atBit x.data 1) >>> (3 : Nat))
def m512 (x : I) := (m511 x).set .x13 (((W (atBit x.data 1) >>> (3 : Nat)) &&& signExtend12 4088))
def m513 (x : I) := (m512 x).set .x13 (OpeningRowData.addr x.data 1)
def m514 (x : I) := (m513 x).set .x29 (old x.data 1)
def m515 (x : I) := (m514 x).set .x30 (x.word 1 <<< off x.data)
def m516 (x : I) := (m515 x).set .x29 (merged x.data 1)
def m517 (x : I) := (m516 x).set .x12 (high x.data 1)
def m518 (x : I) := withMem (m517 x) (tailMem x.data 1)
def m519 (x : I) := withMem (m518 x) (before x.data 2)
def m520 (x : I) := (m519 x).set .x12 (W (atBit x.data 2) >>> (3 : Nat))
def m521 (x : I) := (m520 x).set .x12 (((W (atBit x.data 2) >>> (3 : Nat)) &&& signExtend12 4088))
def m522 (x : I) := (m521 x).set .x12 (OpeningRowData.addr x.data 2)
def m523 (x : I) := (m522 x).set .x13 (old x.data 2)
def m524 (x : I) := (m523 x).set .x6 (x.word 2 <<< off x.data)
def m525 (x : I) := (m524 x).set .x13 (merged x.data 2)
def m526 (x : I) := (m525 x).set .x14 (high x.data 2)
def m527 (x : I) := withMem (m526 x) (tailMem x.data 2)
def m528 (x : I) := withMem (m527 x) (before x.data 3)
def m529 (x : I) := (m528 x).set .x11 (W (atBit x.data 3) >>> (3 : Nat))
def m530 (x : I) := (m529 x).set .x11 (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088))
def m531 (x : I) := (m530 x).set .x11 (OpeningRowData.addr x.data 3)
def m532 (x : I) := (m531 x).set .x12 (old x.data 3)
def m533 (x : I) := (m532 x).set .x13 (x.word 3 <<< off x.data)
def m534 (x : I) := (m533 x).set .x12 (merged x.data 3)
def m535 (x : I) := withMem (m534 x) (headMem x.data 3)
def m536 (x : I) := (m535 x).set .x12 (W 19)

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
  Expr.instr .x12 (.addi .x0 19)]
theorem tablem : OpeningStraight.Listed 503 codem := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem spanm (o : Oracle) (x : I) (nz : off x.data≠0) : Contract o codem (entry x) (m536 x) := by
  have h503 := OpeningLinear.read o (entry x) .x13 .x31 0 (cell (atBit x.data 0)) (old x.data 0) (by have := within x.data 0 (by decide);omega) (OpeningRowOps.current x.data 0) rfl
  have h504 := OpeningLinear.register o (m504 x) .x5 (.sll .x29 .x16) (x.word 0 <<< off x.data) (OpeningRowOps.left x.data 0)
  have h505 := OpeningLinear.register o (m505 x) .x13 (.or .x13 .x5) (merged x.data 0) rfl
  have h506 := OpeningLinear.register o (m506 x) .x5 (.subw .x0 .x16) (((0 : BitVec 32)-(W (off x.data)).truncate 32).signExtend 64) rfl
  have h507 := OpeningLinear.register o (m507 x) .x29 (.srl .x29 .x5) (high x.data 0) (OpeningRowOps.rightNeg x.data 0 nz)
  have h508 := OpeningRowData.storeAs o (m508 x) .x31 .x29 8 (cell (atBit x.data 0)+1) (high x.data 0) (tailMem x.data 0) (within x.data 0 (by decide)) (OpeningRowOps.following x.data 0) rfl rfl
  have h509 := OpeningRowData.storeAs o (m509 x) .x31 .x13 0 (cell (atBit x.data 0)) (merged x.data 0) (before x.data 1) (by have := within x.data 0 (by decide);omega) (OpeningRowOps.current x.data 0) rfl (full x.data 0 (by decide) nz)
  have h510 := OpeningLinear.register o (m510 x) .x13 (.srli .x30 3) (W (atBit x.data 1) >>> (3 : Nat)) rfl
  have h511 := OpeningLinear.register o (m511 x) .x13 (.andi .x13 4088) (((W (atBit x.data 1) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h512 := OpeningLinear.register o (m512 x) .x13 (.add .x13 .x25) (OpeningRowData.addr x.data 1) (OpeningRowOps.pointer x.data 1 (by decide))
  have h513 := OpeningLinear.read o (m513 x) .x29 .x13 0 (cell (atBit x.data 1)) (old x.data 1) (by have := within x.data 1 (by decide);omega) (OpeningRowOps.current x.data 1) rfl
  have h514 := OpeningLinear.register o (m514 x) .x30 (.sll .x12 .x16) (x.word 1 <<< off x.data) (OpeningRowOps.left x.data 1)
  have h515 := OpeningLinear.register o (m515 x) .x29 (.or .x29 .x30) (merged x.data 1) rfl
  have h516 := OpeningLinear.register o (m516 x) .x12 (.srl .x12 .x5) (high x.data 1) (OpeningRowOps.rightNeg x.data 1 nz)
  have h517 := OpeningRowData.storeAs o (m517 x) .x13 .x12 8 (cell (atBit x.data 1)+1) (high x.data 1) (tailMem x.data 1) (within x.data 1 (by decide)) (OpeningRowOps.following x.data 1) rfl rfl
  have h518 := OpeningRowData.storeAs o (m518 x) .x13 .x29 0 (cell (atBit x.data 1)) (merged x.data 1) (before x.data 2) (by have := within x.data 1 (by decide);omega) (OpeningRowOps.current x.data 1) rfl (full x.data 1 (by decide) nz)
  have h519 := OpeningLinear.register o (m519 x) .x12 (.srli .x6 3) (W (atBit x.data 2) >>> (3 : Nat)) rfl
  have h520 := OpeningLinear.register o (m520 x) .x12 (.andi .x12 4088) (((W (atBit x.data 2) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h521 := OpeningLinear.register o (m521 x) .x12 (.add .x12 .x25) (OpeningRowData.addr x.data 2) (OpeningRowOps.pointer x.data 2 (by decide))
  have h522 := OpeningLinear.read o (m522 x) .x13 .x12 0 (cell (atBit x.data 2)) (old x.data 2) (by have := within x.data 2 (by decide);omega) (OpeningRowOps.current x.data 2) rfl
  have h523 := OpeningLinear.register o (m523 x) .x6 (.sll .x14 .x16) (x.word 2 <<< off x.data) (OpeningRowOps.left x.data 2)
  have h524 := OpeningLinear.register o (m524 x) .x13 (.or .x13 .x6) (merged x.data 2) rfl
  have h525 := OpeningLinear.register o (m525 x) .x14 (.srl .x14 .x5) (high x.data 2) (OpeningRowOps.rightNeg x.data 2 nz)
  have h526 := OpeningRowData.storeAs o (m526 x) .x12 .x14 8 (cell (atBit x.data 2)+1) (high x.data 2) (tailMem x.data 2) (within x.data 2 (by decide)) (OpeningRowOps.following x.data 2) rfl rfl
  have h527 := OpeningRowData.storeAs o (m527 x) .x12 .x13 0 (cell (atBit x.data 2)) (merged x.data 2) (before x.data 3) (by have := within x.data 2 (by decide);omega) (OpeningRowOps.current x.data 2) rfl (full x.data 2 (by decide) nz)
  have h528 := OpeningLinear.register o (m528 x) .x11 (.srli .x11 3) (W (atBit x.data 3) >>> (3 : Nat)) rfl
  have h529 := OpeningLinear.register o (m529 x) .x11 (.andi .x11 4088) (((W (atBit x.data 3) >>> (3 : Nat)) &&& signExtend12 4088)) rfl
  have h530 := OpeningLinear.register o (m530 x) .x11 (.add .x11 .x25) (OpeningRowData.addr x.data 3) (OpeningRowOps.pointer x.data 3 (by decide))
  have h531 := OpeningLinear.read o (m531 x) .x12 .x11 0 (cell (atBit x.data 3)) (old x.data 3) (by have := within x.data 3 (by decide);omega) (OpeningRowOps.current x.data 3) rfl
  have h532 := OpeningLinear.register o (m532 x) .x13 (.sll .x17 .x16) (x.word 3 <<< off x.data) (OpeningRowOps.left x.data 3)
  have h533 := OpeningLinear.register o (m533 x) .x12 (.or .x12 .x13) (merged x.data 3) rfl
  have h534 := OpeningRowData.storeAs o (m534 x) .x11 .x12 0 (cell (atBit x.data 3)) (merged x.data 3) (headMem x.data 3) (by have := within x.data 3 (by decide);omega) (OpeningRowOps.current x.data 3) rfl rfl
  have h535 := OpeningLinear.register o (m535 x) .x12 (.addi .x0 19) (W 19) rfl
  exact LeafModel.combine h503 (LeafModel.combine h504 (LeafModel.combine h505 (LeafModel.combine h506 (LeafModel.combine h507 (LeafModel.combine h508 (LeafModel.combine h509 (LeafModel.combine h510 (LeafModel.combine h511 (LeafModel.combine h512 (LeafModel.combine h513 (LeafModel.combine h514 (LeafModel.combine h515 (LeafModel.combine h516 (LeafModel.combine h517 (LeafModel.combine h518 (LeafModel.combine h519 (LeafModel.combine h520 (LeafModel.combine h521 (LeafModel.combine h522 (LeafModel.combine h523 (LeafModel.combine h524 (LeafModel.combine h525 (LeafModel.combine h526 (LeafModel.combine h527 (LeafModel.combine h528 (LeafModel.combine h529 (LeafModel.combine h530 (LeafModel.combine h531 (LeafModel.combine h532 (LeafModel.combine h533 (LeafModel.combine h534 (LeafModel.combine h535 (LeafModel.empty _ _)))))))))))))))))))))))))))))))))

def s538 (x : I) := (m536 x).set .x12 ((64 : Word)-W (off x.data))
def s539 (x : I) := (s538 x).set .x12 (high x.data 3)
def s540 (x : I) := withMem (s539 x) (before x.data 4)

def codes : List Instr := [
  Expr.instr .x12 (.sub .x18 .x16),
  Expr.instr .x12 (.srl .x17 .x12),
  .SD .x11 .x12 8]
theorem tables : OpeningStraight.Listed 537 codes := ⟨rfl,rfl,rfl,True.intro⟩
theorem spans (o : Oracle) (x : I) (nz : off x.data≠0) (cross : 64<off x.data+x.data.bits) : Contract o codes (m536 x) (s540 x) := by
  have h537 := OpeningLinear.register o (m536 x) .x12 (.sub .x18 .x16) ((64 : Word)-W (off x.data)) rfl
  have h538 := OpeningLinear.register o (s538 x) .x12 (.srl .x17 .x12) (high x.data 3) (OpeningRowOps.rightSub x.data 3 nz)
  have h539 := OpeningRowData.storeAs o (s539 x) .x11 .x12 8 (cell (atBit x.data 3)+1) (high x.data 3) (before x.data 4) (within x.data 3 (by decide)) (OpeningRowOps.following x.data 3) rfl (crosses x.data nz cross)
  exact LeafModel.combine h537 (LeafModel.combine h538 (LeafModel.combine h539 (LeafModel.empty _ _)))


def output (x : I) := if off x.data=0 then a552 x else if off x.data<19 then m536 x else s540 x

theorem run (o : Oracle) (x : I) (u : MachineState) (pc : u.pc=CommitBlocks.addr 502) (fit : Fits u (entry x)) :
    ∃ t n, n≤64 ∧ CommitExact.Segment o OpeningStraight.image n u t ∧ t.pc=CommitBlocks.addr 552 ∧
      Fits t (output x) := by
  have zstep := zero_branch o u 502 503 541 .x16 156 pc (by decide) rfl rfl rfl
    (W (off x.data)) (fit.registers _)
  have eqv : W (off x.data)=0 ↔ off x.data=0 := OpeningBranch.word_zero _
  simp only [eqv] at zstep
  unfold output
  by_cases z : off x.data=0
  · simp only [z,ite_true] at zstep ⊢
    obtain ⟨v,rv,pv,hv⟩ := OpeningLinear.block (spana o x z) (i:=541) (by decide) tablea
      (u.setPC _) rfl (fit.pc _)
    exact ⟨v,1+codea.length,by change 12≤64;decide,CommitExact.compose zstep rv,pv,hv⟩
  · simp only [z,ite_false] at zstep ⊢
    obtain ⟨v,rv,pv,hv⟩ := OpeningLinear.block (spanm o x z) (i:=503) (by decide) tablem (u.setPC _) rfl (fit.pc _)
    have branch := OpeningBranch.less o v .x16 .x12 536 552 64 pv (by decide) rfl rfl
      (off x.data) 19 (by unfold off;omega) (by decide) (hv.registers _) (hv.registers _)
    by_cases little : off x.data<19
    · simp only [little,ite_true] at branch ⊢
      exact ⟨_,1+codem.length+1,by change 35≤64;decide,CommitExact.compose (CommitExact.compose zstep rv) branch,rfl,hv.pc _⟩
    · simp only [little,ite_false] at branch ⊢
      have cross : 64<off x.data+x.data.bits := by change 64<off x.data+46;omega
      obtain ⟨w,rw,pw,hw⟩ := OpeningLinear.block (spans o x z cross) (i:=537) (by decide) tables
        (v.setPC _) rfl (hv.pc _)
      have jump := OpeningBranch.jump o w 540 552 48 pw (by decide) rfl rfl
      exact ⟨_,1+codem.length+1+codes.length+1,by change 39≤64;decide,CommitExact.compose (CommitExact.compose (CommitExact.compose
        (CommitExact.compose zstep rv) branch) rw) jump,rfl,hw.pc _⟩

theorem memory (x : I) : (output x).mem=before x.data 4 := by
  unfold output
  split
  · rfl
  · rename_i nz;split
    · rename_i little
      exact short x.data nz (by change off x.data+46≤64;omega)
    · rfl

def changed : List Reg := [.x5,.x6,.x11,.x12,.x13,.x14,.x29,.x30]

theorem frame (x : I) (r : Reg) (h : r∉changed) : (output x).reg r=(entry x).reg r := by
  unfold output
  split
  · cases r <;> first | rfl | exact False.elim (h (by decide))
  · split <;> cases r <;> first | rfl | exact False.elim (h (by decide))

end CommitGolfCandidate.Reconstruction.OpeningRow23
