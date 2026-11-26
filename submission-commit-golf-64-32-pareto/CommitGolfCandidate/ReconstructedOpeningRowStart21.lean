import CommitGolfCandidate.ReconstructedOpeningRow21
import CommitGolfCandidate.ReconstructedOpeningRowEntry

namespace CommitGolfCandidate.Reconstruction.OpeningRowStart21
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
theorem start_eq (e : Env) (m : Model) (h : Ready21 e m) : start e m=m := by
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

def s620 (e : Env) (m : Model) := (start e m).set .x11 (W (e.cursor+938))
def v620 (e : Env) (m : Model) : Word := (W (2^24+e.index.val)) <<< (2 : Nat)
def s621 (e : Env) (m : Model) := (s620 e m).set .x12 (v620 e m)
def v621 (e : Env) (m : Model) : Word := (v620 e m) &&& signExtend12 4064
def s622 (e : Env) (m : Model) := (s621 e m).set .x12 (v621 e m)
def v622 (e : Env) (m : Model) : Word := (v621 e m) ^^^ signExtend12 32
def s623 (e : Env) (m : Model) := (s622 e m).set .x12 (v622 e m)
def s624 (e : Env) (m : Model) := (s623 e m).set .x13 (basePtr e.index 21)
def s625 (e : Env) (m : Model) := (s624 e m).set .x29 (m.mem (wordAt e.index 21 0))
def s626 (e : Env) (m : Model) := (s625 e m).set .x12 (m.mem (wordAt e.index 21 1))
def s627 (e : Env) (m : Model) := (s626 e m).set .x14 (m.mem (wordAt e.index 21 2))
def s628 (e : Env) (m : Model) := (s627 e m).set .x13 (m.mem (wordAt e.index 21 3))
def s629 (e : Env) (m : Model) := (s628 e m).set .x16 (W ((e.cursor+938)%64))
def v629 (e : Env) (m : Model) : Word := (W (e.cursor+938)) >>> (3 : Nat)
def s630 (e : Env) (m : Model) := (s629 e m).set .x11 (v629 e m)
def v630 (e : Env) (m : Model) : Word := (v629 e m) &&& signExtend12 4088
def s631 (e : Env) (m : Model) := (s630 e m).set .x11 (v630 e m)
def s632 (e : Env) (m : Model) := (s631 e m).set .x31 (wordAddress (cell (e.cursor+938)))
def s633 (e : Env) (m : Model) := (s632 e m).set .x30 (W (e.cursor+1002))
def s634 (e : Env) (m : Model) := (s633 e m).set .x6 (W (e.cursor+1066))
def s635 (e : Env) (m : Model) := (s634 e m).set .x11 (W (e.cursor+1130))
def s636 (e : Env) (m : Model) := (s635 e m).set .x17 (m.mem (wordAt e.index 21 3) &&& W 70368744177663)

def ops : List Instr := [
  Expr.instr .x11 (.addi .x7 938),
  Expr.instr .x12 (.slli .x10 2),
  Expr.instr .x12 (.andi .x12 4064),
  Expr.instr .x12 (.xori .x12 32),
  Expr.instr .x13 (.add .x12 .x22),
  .LD .x29 .x13 672,
  .LD .x12 .x13 680,
  .LD .x14 .x13 688,
  .LD .x13 .x13 696,
  Expr.instr .x16 (.andi .x11 63),
  Expr.instr .x11 (.srli .x11 3),
  Expr.instr .x11 (.andi .x11 4088),
  Expr.instr .x31 (.add .x11 .x25),
  Expr.instr .x30 (.addi .x7 1002),
  Expr.instr .x6 (.addi .x7 1066),
  Expr.instr .x11 (.addi .x7 1130),
  Expr.instr .x17 (.and .x13 .x9)]
theorem table : OpeningStraight.Listed 619 ops := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem prepare (o : Oracle) (e : Env) (m : Model) (h : Stack e m.mem) : Contract o ops (start e m) (s636 e m) := by
  have h619 := OpeningLinear.register o (start e m) .x11 (.addi .x7 938) (W (e.cursor+938)) (OpeningRowOps.plusBit e.cursor 0 938 938 938 rfl rfl)
  have h620 := OpeningLinear.register o (s620 e m) .x12 (.slli .x10 2) (v620 e m) rfl
  have h621 := OpeningLinear.register o (s621 e m) .x12 (.andi .x12 4064) (v621 e m) rfl
  have h622 := OpeningLinear.register o (s622 e m) .x12 (.xori .x12 32) (v622 e m) rfl
  have h623 := OpeningLinear.register o (s623 e m) .x13 (.add .x12 .x22) (basePtr e.index 21) (OpeningLowerAddress.previous e.index 21 (by decide) (by decide))
  have h624 := OpeningLinear.read o (s624 e m) .x29 .x13 672 (wordAt e.index 21 0) (m.mem (wordAt e.index 21 0)) (by have := word_room e.index 21 0 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 21 0 672 rfl) rfl
  have h625 := OpeningLinear.read o (s625 e m) .x12 .x13 680 (wordAt e.index 21 1) (m.mem (wordAt e.index 21 1)) (by have := word_room e.index 21 1 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 21 1 680 rfl) rfl
  have h626 := OpeningLinear.read o (s626 e m) .x14 .x13 688 (wordAt e.index 21 2) (m.mem (wordAt e.index 21 2)) (by have := word_room e.index 21 2 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 21 2 688 rfl) rfl
  have h627 := OpeningLinear.read o (s627 e m) .x13 .x13 696 (wordAt e.index 21 3) (m.mem (wordAt e.index 21 3)) (by have := word_room e.index 21 3 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 21 3 696 rfl) rfl
  have h628 := OpeningLinear.register o (s628 e m) .x16 (.andi .x11 63) (W ((e.cursor+938)%64)) (OpeningCursor.offset (e.cursor+938))
  have h629 := OpeningLinear.register o (s629 e m) .x11 (.srli .x11 3) (v629 e m) rfl
  have h630 := OpeningLinear.register o (s630 e m) .x11 (.andi .x11 4088) (v630 e m) rfl
  have h631 := OpeningLinear.register o (s631 e m) .x31 (.add .x11 .x25) (wordAddress (cell (e.cursor+938))) (OpeningCursor.word_address (e.cursor+938) (by have h₀ := e.room;unfold capacity at h₀;omega))
  have h632 := OpeningLinear.register o (s632 e m) .x30 (.addi .x7 1002) (W (e.cursor+1002)) (OpeningRowOps.plusBit e.cursor 0 1002 1002 1002 rfl rfl)
  have h633 := OpeningLinear.register o (s633 e m) .x6 (.addi .x7 1066) (W (e.cursor+1066)) (OpeningRowOps.plusBit e.cursor 0 1066 1066 1066 rfl rfl)
  have h634 := OpeningLinear.register o (s634 e m) .x11 (.addi .x7 1130) (W (e.cursor+1130)) (OpeningRowOps.plusBit e.cursor 0 1130 1130 1130 rfl rfl)
  have h635 := OpeningLinear.register o (s635 e m) .x17 (.and .x13 .x9) (m.mem (wordAt e.index 21 3) &&& W 70368744177663) rfl
  exact LeafModel.combine h619 (LeafModel.combine h620 (LeafModel.combine h621 (LeafModel.combine h622 (LeafModel.combine h623 (LeafModel.combine h624 (LeafModel.combine h625 (LeafModel.combine h626 (LeafModel.combine h627 (LeafModel.combine h628 (LeafModel.combine h629 (LeafModel.combine h630 (LeafModel.combine h631 (LeafModel.combine h632 (LeafModel.combine h633 (LeafModel.combine h634 (LeafModel.combine h635 (LeafModel.empty _ _)))))))))))))))))

def input (e : Env) (m : Model) : OpeningRow21.I where
  root := e.cursor
  initial := s636 e m
  word := fun k => if k=3 then m.mem (wordAt e.index 21 3) &&& W 70368744177663 else m.mem (wordAt e.index 21 k)
  room := by have := e.room;omega
  fits := by decide

theorem entry (e : Env) (m : Model) : OpeningRow21.entry (input e m)=s636 e m := by
  refine OpeningRowEntry.equalModel (OpeningRow21.entry (input e m)) (s636 e m) ?_ rfl
  intro r;cases r <;> rfl

def result (e : Env) (m : Model) := OpeningRow21.output (input e m)

theorem memory (e : Env) (m : Model) :
    (result e m).mem=CapWriter.lowMemory m.mem (e.cursor+938) 21 (OpeningNodeStream.words m.mem e.index 21) := by
  exact OpeningRow21.memory (input e m)

theorem ready (e : Env) (m : Model) (stack : Stack e m.mem) : Ready20 e (result e m) := by
  constructor
  · exact (OpeningRow21.frame (input e m) .x0 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow21.frame (input e m) .x2 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow21.frame (input e m) .x8 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow21.frame (input e m) .x9 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow21.frame (input e m) .x18 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow21.frame (input e m) .x22 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow21.frame (input e m) .x25 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow21.frame (input e m) .x10 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow21.frame (input e m) .x7 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow21.frame (input e m) .x28 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow21.frame (input e m) .x26 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow21.frame (input e m) .x20 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow21.frame (input e m) .x27 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow21.frame (input e m) .x15 (by decide)).trans (by rw [entry];rfl)

theorem run (o : Oracle) (e : Env) (m : Model) (h : Ready21 e m) (stack : Stack e m.mem)
    (s : MachineState) (pc : s.pc=addr 619) (fit : Fits s m) :
    ∃ t n, n≤90 ∧ CommitExact.Segment o OpeningStraight.image n s t ∧ t.pc=addr 686 ∧ Fits t (result e m) := by
  have fit' : Fits s (start e m) := (start_eq e m h).symm ▸ fit
  obtain ⟨v,rv,pv,hv⟩ := OpeningLinear.block (prepare o e m stack) (i:=619) (by decide) table s pc fit'
  obtain ⟨t,n,lim,rt,pt,ht⟩ := OpeningRow21.run o (input e m) v pv ((entry e m).symm ▸ hv)
  exact ⟨t,ops.length+n,by change 17+n≤90;omega,CommitExact.compose rv rt,pt,ht⟩

end CommitGolfCandidate.Reconstruction.OpeningRowStart21
