import CommitGolfCandidate.ReconstructedOpeningRow22
import CommitGolfCandidate.ReconstructedOpeningRowEntry

namespace CommitGolfCandidate.Reconstruction.OpeningRowStart22
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
theorem start_eq (e : Env) (m : Model) (h : Ready22 e m) : start e m=m := by
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

def s553 (e : Env) (m : Model) := (start e m).set .x11 (W (e.cursor+700))
def v553 (e : Env) (m : Model) : Word := (W (2^24+e.index.val)) <<< (3 : Nat)
def s554 (e : Env) (m : Model) := (s553 e m).set .x12 (v553 e m)
def v554 (e : Env) (m : Model) : Word := (v553 e m) &&& signExtend12 4064
def s555 (e : Env) (m : Model) := (s554 e m).set .x12 (v554 e m)
def v555 (e : Env) (m : Model) : Word := (v554 e m) ^^^ signExtend12 32
def s556 (e : Env) (m : Model) := (s555 e m).set .x12 (v555 e m)
def s557 (e : Env) (m : Model) := (s556 e m).set .x13 (basePtr e.index 22)
def s558 (e : Env) (m : Model) := (s557 e m).set .x29 (m.mem (wordAt e.index 22 0))
def s559 (e : Env) (m : Model) := (s558 e m).set .x12 (m.mem (wordAt e.index 22 1))
def s560 (e : Env) (m : Model) := (s559 e m).set .x14 (m.mem (wordAt e.index 22 2))
def s561 (e : Env) (m : Model) := (s560 e m).set .x13 (m.mem (wordAt e.index 22 3))
def s562 (e : Env) (m : Model) := (s561 e m).set .x16 (W ((e.cursor+700)%64))
def v562 (e : Env) (m : Model) : Word := (W (e.cursor+700)) >>> (3 : Nat)
def s563 (e : Env) (m : Model) := (s562 e m).set .x11 (v562 e m)
def v563 (e : Env) (m : Model) : Word := (v562 e m) &&& signExtend12 4088
def s564 (e : Env) (m : Model) := (s563 e m).set .x11 (v563 e m)
def s565 (e : Env) (m : Model) := (s564 e m).set .x31 (wordAddress (cell (e.cursor+700)))
def s566 (e : Env) (m : Model) := (s565 e m).set .x30 (W (e.cursor+764))
def s567 (e : Env) (m : Model) := (s566 e m).set .x6 (W (e.cursor+828))
def s568 (e : Env) (m : Model) := (s567 e m).set .x11 (W (e.cursor+892))
def s569 (e : Env) (m : Model) := (s568 e m).set .x17 (m.mem (wordAt e.index 22 3) &&& W 70368744177663)

def ops : List Instr := [
  Expr.instr .x11 (.addi .x7 700),
  Expr.instr .x12 (.slli .x10 3),
  Expr.instr .x12 (.andi .x12 4064),
  Expr.instr .x12 (.xori .x12 32),
  Expr.instr .x13 (.add .x12 .x22),
  .LD .x29 .x13 704,
  .LD .x12 .x13 712,
  .LD .x14 .x13 720,
  .LD .x13 .x13 728,
  Expr.instr .x16 (.andi .x11 63),
  Expr.instr .x11 (.srli .x11 3),
  Expr.instr .x11 (.andi .x11 4088),
  Expr.instr .x31 (.add .x11 .x25),
  Expr.instr .x30 (.addi .x7 764),
  Expr.instr .x6 (.addi .x7 828),
  Expr.instr .x11 (.addi .x7 892),
  Expr.instr .x17 (.and .x13 .x9)]
theorem table : OpeningStraight.Listed 552 ops := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem prepare (o : Oracle) (e : Env) (m : Model) (h : Stack e m.mem) : Contract o ops (start e m) (s569 e m) := by
  have h552 := OpeningLinear.register o (start e m) .x11 (.addi .x7 700) (W (e.cursor+700)) (OpeningRowOps.plusBit e.cursor 0 700 700 700 rfl rfl)
  have h553 := OpeningLinear.register o (s553 e m) .x12 (.slli .x10 3) (v553 e m) rfl
  have h554 := OpeningLinear.register o (s554 e m) .x12 (.andi .x12 4064) (v554 e m) rfl
  have h555 := OpeningLinear.register o (s555 e m) .x12 (.xori .x12 32) (v555 e m) rfl
  have h556 := OpeningLinear.register o (s556 e m) .x13 (.add .x12 .x22) (basePtr e.index 22) (OpeningLowerAddress.previous e.index 22 (by decide) (by decide))
  have h557 := OpeningLinear.read o (s557 e m) .x29 .x13 704 (wordAt e.index 22 0) (m.mem (wordAt e.index 22 0)) (by have := word_room e.index 22 0 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 22 0 704 rfl) rfl
  have h558 := OpeningLinear.read o (s558 e m) .x12 .x13 712 (wordAt e.index 22 1) (m.mem (wordAt e.index 22 1)) (by have := word_room e.index 22 1 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 22 1 712 rfl) rfl
  have h559 := OpeningLinear.read o (s559 e m) .x14 .x13 720 (wordAt e.index 22 2) (m.mem (wordAt e.index 22 2)) (by have := word_room e.index 22 2 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 22 2 720 rfl) rfl
  have h560 := OpeningLinear.read o (s560 e m) .x13 .x13 728 (wordAt e.index 22 3) (m.mem (wordAt e.index 22 3)) (by have := word_room e.index 22 3 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 22 3 728 rfl) rfl
  have h561 := OpeningLinear.register o (s561 e m) .x16 (.andi .x11 63) (W ((e.cursor+700)%64)) (OpeningCursor.offset (e.cursor+700))
  have h562 := OpeningLinear.register o (s562 e m) .x11 (.srli .x11 3) (v562 e m) rfl
  have h563 := OpeningLinear.register o (s563 e m) .x11 (.andi .x11 4088) (v563 e m) rfl
  have h564 := OpeningLinear.register o (s564 e m) .x31 (.add .x11 .x25) (wordAddress (cell (e.cursor+700))) (OpeningCursor.word_address (e.cursor+700) (by have h₀ := e.room;unfold capacity at h₀;omega))
  have h565 := OpeningLinear.register o (s565 e m) .x30 (.addi .x7 764) (W (e.cursor+764)) (OpeningRowOps.plusBit e.cursor 0 764 764 764 rfl rfl)
  have h566 := OpeningLinear.register o (s566 e m) .x6 (.addi .x7 828) (W (e.cursor+828)) (OpeningRowOps.plusBit e.cursor 0 828 828 828 rfl rfl)
  have h567 := OpeningLinear.register o (s567 e m) .x11 (.addi .x7 892) (W (e.cursor+892)) (OpeningRowOps.plusBit e.cursor 0 892 892 892 rfl rfl)
  have h568 := OpeningLinear.register o (s568 e m) .x17 (.and .x13 .x9) (m.mem (wordAt e.index 22 3) &&& W 70368744177663) rfl
  exact LeafModel.combine h552 (LeafModel.combine h553 (LeafModel.combine h554 (LeafModel.combine h555 (LeafModel.combine h556 (LeafModel.combine h557 (LeafModel.combine h558 (LeafModel.combine h559 (LeafModel.combine h560 (LeafModel.combine h561 (LeafModel.combine h562 (LeafModel.combine h563 (LeafModel.combine h564 (LeafModel.combine h565 (LeafModel.combine h566 (LeafModel.combine h567 (LeafModel.combine h568 (LeafModel.empty _ _)))))))))))))))))

def input (e : Env) (m : Model) : OpeningRow22.I where
  root := e.cursor
  initial := s569 e m
  word := fun k => if k=3 then m.mem (wordAt e.index 22 3) &&& W 70368744177663 else m.mem (wordAt e.index 22 k)
  room := by have := e.room;omega
  fits := by decide

theorem entry (e : Env) (m : Model) : OpeningRow22.entry (input e m)=s569 e m := by
  refine OpeningRowEntry.equalModel (OpeningRow22.entry (input e m)) (s569 e m) ?_ rfl
  intro r;cases r <;> rfl

def result (e : Env) (m : Model) := OpeningRow22.output (input e m)

theorem memory (e : Env) (m : Model) :
    (result e m).mem=CapWriter.lowMemory m.mem (e.cursor+700) 22 (OpeningNodeStream.words m.mem e.index 22) := by
  exact OpeningRow22.memory (input e m)

theorem ready (e : Env) (m : Model) (stack : Stack e m.mem) : Ready21 e (result e m) := by
  constructor
  · exact (OpeningRow22.frame (input e m) .x0 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow22.frame (input e m) .x2 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow22.frame (input e m) .x8 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow22.frame (input e m) .x9 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow22.frame (input e m) .x18 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow22.frame (input e m) .x22 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow22.frame (input e m) .x25 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow22.frame (input e m) .x10 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow22.frame (input e m) .x7 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow22.frame (input e m) .x28 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow22.frame (input e m) .x26 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow22.frame (input e m) .x20 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow22.frame (input e m) .x27 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow22.frame (input e m) .x15 (by decide)).trans (by rw [entry];rfl)

theorem run (o : Oracle) (e : Env) (m : Model) (h : Ready22 e m) (stack : Stack e m.mem)
    (s : MachineState) (pc : s.pc=addr 552) (fit : Fits s m) :
    ∃ t n, n≤90 ∧ CommitExact.Segment o OpeningStraight.image n s t ∧ t.pc=addr 619 ∧ Fits t (result e m) := by
  have fit' : Fits s (start e m) := (start_eq e m h).symm ▸ fit
  obtain ⟨v,rv,pv,hv⟩ := OpeningLinear.block (prepare o e m stack) (i:=552) (by decide) table s pc fit'
  obtain ⟨t,n,lim,rt,pt,ht⟩ := OpeningRow22.run o (input e m) v pv ((entry e m).symm ▸ hv)
  exact ⟨t,ops.length+n,by change 17+n≤90;omega,CommitExact.compose rv rt,pt,ht⟩

end CommitGolfCandidate.Reconstruction.OpeningRowStart22
