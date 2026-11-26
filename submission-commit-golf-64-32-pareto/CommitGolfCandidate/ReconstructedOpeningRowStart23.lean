import CommitGolfCandidate.ReconstructedOpeningRow23
import CommitGolfCandidate.ReconstructedOpeningRowEntry

namespace CommitGolfCandidate.Reconstruction.OpeningRowStart23
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningOps OpeningCursor OpeningPut OpeningHeaderAddress
open TwoPermutationPrototype.RV64 OpeningRowEntry
open CommitBlocks (addr)
set_option maxRecDepth 24576
set_option maxHeartbeats 2500000

def start (e : Env) (m : Model) : Model := ⟨fun
  | .x0 => W 0
  | .x2 => W 68719474016
  | .x8 => W 68719476336
  | .x9 => W 70368744177663
  | .x18 => W 64
  | .x22 => W 4294971424
  | .x25 => W 10334769248
  | .x10 => W (2^24+e.index.val)
  | .x7 => W e.cursor
  | .x28 => basePtr e.index 19
  | .x26 => basePtr e.index 18
  | .x20 => basePtr e.index 17
  | .x27 => basePtr e.index 16
  | .x15 => basePtr e.index 15
  | r => m.reg r,m.mem⟩
theorem start_eq (e : Env) (m : Model) (h : Ready23 e m) : start e m=m := by
  refine OpeningRowEntry.equalModel (start e m) m ?_ rfl
  intro r;cases r
  · exact h.r0.symm
  · rfl
  · exact h.r2.symm
  · rfl
  · rfl
  · rfl
  · rfl
  · exact h.r7.symm
  · exact h.r8.symm
  · exact h.r9.symm
  · exact h.r10.symm
  · rfl
  · rfl
  · rfl
  · rfl
  · exact h.r15.symm
  · rfl
  · rfl
  · exact h.r18.symm
  · rfl
  · exact h.r20.symm
  · rfl
  · exact h.r22.symm
  · rfl
  · rfl
  · exact h.r25.symm
  · exact h.r26.symm
  · exact h.r27.symm
  · exact h.r28.symm
  · rfl
  · rfl
  · rfl

def s486 (e : Env) (m : Model) := (start e m).set .x11 (W (e.cursor+462))
def v486 (e : Env) (m : Model) : Word := (W (2^24+e.index.val)) <<< (4 : Nat)
def s487 (e : Env) (m : Model) := (s486 e m).set .x12 (v486 e m)
def v487 (e : Env) (m : Model) : Word := (v486 e m) &&& signExtend12 4064
def s488 (e : Env) (m : Model) := (s487 e m).set .x12 (v487 e m)
def v488 (e : Env) (m : Model) : Word := (v487 e m) ^^^ signExtend12 32
def s489 (e : Env) (m : Model) := (s488 e m).set .x12 (v488 e m)
def s490 (e : Env) (m : Model) := (s489 e m).set .x13 (basePtr e.index 23)
def s491 (e : Env) (m : Model) := (s490 e m).set .x29 (m.mem (wordAt e.index 23 0))
def s492 (e : Env) (m : Model) := (s491 e m).set .x12 (m.mem (wordAt e.index 23 1))
def s493 (e : Env) (m : Model) := (s492 e m).set .x14 (m.mem (wordAt e.index 23 2))
def s494 (e : Env) (m : Model) := (s493 e m).set .x13 (m.mem (wordAt e.index 23 3))
def s495 (e : Env) (m : Model) := (s494 e m).set .x16 (W ((e.cursor+462)%64))
def v495 (e : Env) (m : Model) : Word := (W (e.cursor+462)) >>> (3 : Nat)
def s496 (e : Env) (m : Model) := (s495 e m).set .x11 (v495 e m)
def v496 (e : Env) (m : Model) : Word := (v495 e m) &&& signExtend12 4088
def s497 (e : Env) (m : Model) := (s496 e m).set .x11 (v496 e m)
def s498 (e : Env) (m : Model) := (s497 e m).set .x31 (wordAddress (cell (e.cursor+462)))
def s499 (e : Env) (m : Model) := (s498 e m).set .x30 (W (e.cursor+526))
def s500 (e : Env) (m : Model) := (s499 e m).set .x6 (W (e.cursor+590))
def s501 (e : Env) (m : Model) := (s500 e m).set .x11 (W (e.cursor+654))
def s502 (e : Env) (m : Model) := (s501 e m).set .x17 (m.mem (wordAt e.index 23 3) &&& W 70368744177663)

def ops : List Instr := [
  Expr.instr .x11 (.addi .x7 462),
  Expr.instr .x12 (.slli .x10 4),
  Expr.instr .x12 (.andi .x12 4064),
  Expr.instr .x12 (.xori .x12 32),
  Expr.instr .x13 (.add .x12 .x22),
  .LD .x29 .x13 736,
  .LD .x12 .x13 744,
  .LD .x14 .x13 752,
  .LD .x13 .x13 760,
  Expr.instr .x16 (.andi .x11 63),
  Expr.instr .x11 (.srli .x11 3),
  Expr.instr .x11 (.andi .x11 4088),
  Expr.instr .x31 (.add .x11 .x25),
  Expr.instr .x30 (.addi .x7 526),
  Expr.instr .x6 (.addi .x7 590),
  Expr.instr .x11 (.addi .x7 654),
  Expr.instr .x17 (.and .x13 .x9)]
theorem table : OpeningStraight.Listed 485 ops := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem prepare (o : Oracle) (e : Env) (m : Model) (h : Stack e m.mem) : Contract o ops (start e m) (s502 e m) := by
  have h485 := OpeningLinear.register o (start e m) .x11 (.addi .x7 462) (W (e.cursor+462)) (OpeningRowOps.plusBit e.cursor 0 462 462 462 rfl rfl)
  have h486 := OpeningLinear.register o (s486 e m) .x12 (.slli .x10 4) (v486 e m) rfl
  have h487 := OpeningLinear.register o (s487 e m) .x12 (.andi .x12 4064) (v487 e m) rfl
  have h488 := OpeningLinear.register o (s488 e m) .x12 (.xori .x12 32) (v488 e m) rfl
  have h489 := OpeningLinear.register o (s489 e m) .x13 (.add .x12 .x22) (basePtr e.index 23) (OpeningLowerAddress.previous e.index 23 (by decide) (by decide))
  have h490 := OpeningLinear.read o (s490 e m) .x29 .x13 736 (wordAt e.index 23 0) (m.mem (wordAt e.index 23 0)) (by have := word_room e.index 23 0 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 23 0 736 rfl) rfl
  have h491 := OpeningLinear.read o (s491 e m) .x12 .x13 744 (wordAt e.index 23 1) (m.mem (wordAt e.index 23 1)) (by have := word_room e.index 23 1 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 23 1 744 rfl) rfl
  have h492 := OpeningLinear.read o (s492 e m) .x14 .x13 752 (wordAt e.index 23 2) (m.mem (wordAt e.index 23 2)) (by have := word_room e.index 23 2 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 23 2 752 rfl) rfl
  have h493 := OpeningLinear.read o (s493 e m) .x13 .x13 760 (wordAt e.index 23 3) (m.mem (wordAt e.index 23 3)) (by have := word_room e.index 23 3 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 23 3 760 rfl) rfl
  have h494 := OpeningLinear.register o (s494 e m) .x16 (.andi .x11 63) (W ((e.cursor+462)%64)) (OpeningCursor.offset (e.cursor+462))
  have h495 := OpeningLinear.register o (s495 e m) .x11 (.srli .x11 3) (v495 e m) rfl
  have h496 := OpeningLinear.register o (s496 e m) .x11 (.andi .x11 4088) (v496 e m) rfl
  have h497 := OpeningLinear.register o (s497 e m) .x31 (.add .x11 .x25) (wordAddress (cell (e.cursor+462))) (OpeningCursor.word_address (e.cursor+462) (by have h₀ := e.room;unfold capacity at h₀;omega))
  have h498 := OpeningLinear.register o (s498 e m) .x30 (.addi .x7 526) (W (e.cursor+526)) (OpeningRowOps.plusBit e.cursor 0 526 526 526 rfl rfl)
  have h499 := OpeningLinear.register o (s499 e m) .x6 (.addi .x7 590) (W (e.cursor+590)) (OpeningRowOps.plusBit e.cursor 0 590 590 590 rfl rfl)
  have h500 := OpeningLinear.register o (s500 e m) .x11 (.addi .x7 654) (W (e.cursor+654)) (OpeningRowOps.plusBit e.cursor 0 654 654 654 rfl rfl)
  have h501 := OpeningLinear.register o (s501 e m) .x17 (.and .x13 .x9) (m.mem (wordAt e.index 23 3) &&& W 70368744177663) rfl
  exact LeafModel.combine h485 (LeafModel.combine h486 (LeafModel.combine h487 (LeafModel.combine h488 (LeafModel.combine h489 (LeafModel.combine h490 (LeafModel.combine h491 (LeafModel.combine h492 (LeafModel.combine h493 (LeafModel.combine h494 (LeafModel.combine h495 (LeafModel.combine h496 (LeafModel.combine h497 (LeafModel.combine h498 (LeafModel.combine h499 (LeafModel.combine h500 (LeafModel.combine h501 (LeafModel.empty _ _)))))))))))))))))

def input (e : Env) (m : Model) : OpeningRow23.I where
  root := e.cursor
  initial := s502 e m
  word := fun k => if k=3 then m.mem (wordAt e.index 23 3) &&& W 70368744177663 else m.mem (wordAt e.index 23 k)
  room := by have := e.room;omega
  fits := by decide

theorem entry (e : Env) (m : Model) : OpeningRow23.entry (input e m)=s502 e m := by
  refine OpeningRowEntry.equalModel (OpeningRow23.entry (input e m)) (s502 e m) ?_ rfl
  intro r;cases r <;> rfl

def result (e : Env) (m : Model) := OpeningRow23.output (input e m)

theorem memory (e : Env) (m : Model) :
    (result e m).mem=CapWriter.lowMemory m.mem (e.cursor+462) 23 (OpeningNodeStream.words m.mem e.index 23) := by
  exact OpeningRow23.memory (input e m)

theorem ready (e : Env) (m : Model) (stack : Stack e m.mem) : Ready22 e (result e m) := by
  constructor
  · exact (OpeningRow23.frame (input e m) .x0 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow23.frame (input e m) .x2 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow23.frame (input e m) .x8 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow23.frame (input e m) .x9 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow23.frame (input e m) .x18 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow23.frame (input e m) .x22 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow23.frame (input e m) .x25 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow23.frame (input e m) .x10 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow23.frame (input e m) .x7 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow23.frame (input e m) .x28 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow23.frame (input e m) .x26 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow23.frame (input e m) .x20 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow23.frame (input e m) .x27 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow23.frame (input e m) .x15 (by decide)).trans (by rw [entry];rfl)

theorem run (o : Oracle) (e : Env) (m : Model) (h : Ready23 e m) (stack : Stack e m.mem)
    (s : MachineState) (pc : s.pc=addr 485) (fit : Fits s m) :
    ∃ t n, n≤90 ∧ CommitExact.Segment o OpeningStraight.image n s t ∧ t.pc=addr 552 ∧ Fits t (result e m) := by
  have fit' : Fits s (start e m) := (start_eq e m h).symm ▸ fit
  obtain ⟨v,rv,pv,hv⟩ := OpeningLinear.block (prepare o e m stack) (i:=485) (by decide) table s pc fit'
  obtain ⟨t,n,lim,rt,pt,ht⟩ := OpeningRow23.run o (input e m) v pv ((entry e m).symm ▸ hv)
  exact ⟨t,ops.length+n,by change 17+n≤90;omega,CommitExact.compose rv rt,pt,ht⟩

end CommitGolfCandidate.Reconstruction.OpeningRowStart23
