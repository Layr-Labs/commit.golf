import CommitGolfCandidate.ReconstructedOpeningRow20
import CommitGolfCandidate.ReconstructedOpeningRowEntry

namespace CommitGolfCandidate.Reconstruction.OpeningRowStart20
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
theorem start_eq (e : Env) (m : Model) (h : Ready20 e m) : start e m=m := by
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

def s687 (e : Env) (m : Model) := (start e m).set .x11 (W (e.cursor+1176))
def v687 (e : Env) (m : Model) : Word := (W (2^24+e.index.val)) <<< (1 : Nat)
def s688 (e : Env) (m : Model) := (s687 e m).set .x12 (v687 e m)
def v688 (e : Env) (m : Model) : Word := (v687 e m) &&& signExtend12 4064
def s689 (e : Env) (m : Model) := (s688 e m).set .x12 (v688 e m)
def v689 (e : Env) (m : Model) : Word := (v688 e m) ^^^ signExtend12 32
def s690 (e : Env) (m : Model) := (s689 e m).set .x12 (v689 e m)
def s691 (e : Env) (m : Model) := (s690 e m).set .x13 (basePtr e.index 20)
def s692 (e : Env) (m : Model) := (s691 e m).set .x29 (m.mem (wordAt e.index 20 0))
def s693 (e : Env) (m : Model) := (s692 e m).set .x12 (m.mem (wordAt e.index 20 1))
def s694 (e : Env) (m : Model) := (s693 e m).set .x14 (m.mem (wordAt e.index 20 2))
def s695 (e : Env) (m : Model) := (s694 e m).set .x13 (m.mem (wordAt e.index 20 3))
def s696 (e : Env) (m : Model) := (s695 e m).set .x16 (W ((e.cursor+1176)%64))
def v696 (e : Env) (m : Model) : Word := (W (e.cursor+1176)) >>> (3 : Nat)
def s697 (e : Env) (m : Model) := (s696 e m).set .x11 (v696 e m)
def v697 (e : Env) (m : Model) : Word := (v696 e m) &&& signExtend12 4088
def s698 (e : Env) (m : Model) := (s697 e m).set .x11 (v697 e m)
def s699 (e : Env) (m : Model) := (s698 e m).set .x31 (wordAddress (cell (e.cursor+1176)))
def s700 (e : Env) (m : Model) := (s699 e m).set .x30 (W (e.cursor+1240))
def s701 (e : Env) (m : Model) := (s700 e m).set .x6 (W (e.cursor+1304))
def s702 (e : Env) (m : Model) := (s701 e m).set .x11 (W (e.cursor+1368))
def s703 (e : Env) (m : Model) := (s702 e m).set .x17 (W 4096)
def s704 (e : Env) (m : Model) := (s703 e m).set .x17 (W 68719472240)
def s705 (e : Env) (m : Model) := (s704 e m).set .x17 (W 17592186044415)
def s706 (e : Env) (m : Model) := (s705 e m).set .x17 (m.mem (wordAt e.index 20 3) &&& W 17592186044415)

def ops : List Instr := [
  Expr.instr .x11 (.addi .x7 1176),
  Expr.instr .x12 (.slli .x10 1),
  Expr.instr .x12 (.andi .x12 4064),
  Expr.instr .x12 (.xori .x12 32),
  Expr.instr .x13 (.add .x12 .x22),
  .LD .x29 .x13 640,
  .LD .x12 .x13 648,
  .LD .x14 .x13 656,
  .LD .x13 .x13 664,
  Expr.instr .x16 (.andi .x11 63),
  Expr.instr .x11 (.srli .x11 3),
  Expr.instr .x11 (.andi .x11 4088),
  Expr.instr .x31 (.add .x11 .x25),
  Expr.instr .x30 (.addi .x7 1240),
  Expr.instr .x6 (.addi .x7 1304),
  Expr.instr .x11 (.addi .x7 1368),
  Expr.instr .x17 (.lui 1),
  Expr.instr .x17 (.sub .x8 .x17),
  .LD .x17 .x17 1840,
  Expr.instr .x17 (.and .x13 .x17)]
theorem table : OpeningStraight.Listed 686 ops := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem prepare (o : Oracle) (e : Env) (m : Model) (h : Stack e m.mem) : Contract o ops (start e m) (s706 e m) := by
  have h686 := OpeningLinear.register o (start e m) .x11 (.addi .x7 1176) (W (e.cursor+1176)) (OpeningRowOps.plusBit e.cursor 0 1176 1176 1176 rfl rfl)
  have h687 := OpeningLinear.register o (s687 e m) .x12 (.slli .x10 1) (v687 e m) rfl
  have h688 := OpeningLinear.register o (s688 e m) .x12 (.andi .x12 4064) (v688 e m) rfl
  have h689 := OpeningLinear.register o (s689 e m) .x12 (.xori .x12 32) (v689 e m) rfl
  have h690 := OpeningLinear.register o (s690 e m) .x13 (.add .x12 .x22) (basePtr e.index 20) (OpeningLowerAddress.previous e.index 20 (by decide) (by decide))
  have h691 := OpeningLinear.read o (s691 e m) .x29 .x13 640 (wordAt e.index 20 0) (m.mem (wordAt e.index 20 0)) (by have := word_room e.index 20 0 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 20 0 640 rfl) rfl
  have h692 := OpeningLinear.read o (s692 e m) .x12 .x13 648 (wordAt e.index 20 1) (m.mem (wordAt e.index 20 1)) (by have := word_room e.index 20 1 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 20 1 648 rfl) rfl
  have h693 := OpeningLinear.read o (s693 e m) .x14 .x13 656 (wordAt e.index 20 2) (m.mem (wordAt e.index 20 2)) (by have := word_room e.index 20 2 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 20 2 656 rfl) rfl
  have h694 := OpeningLinear.read o (s694 e m) .x13 .x13 664 (wordAt e.index 20 3) (m.mem (wordAt e.index 20 3)) (by have := word_room e.index 20 3 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 20 3 664 rfl) rfl
  have h695 := OpeningLinear.register o (s695 e m) .x16 (.andi .x11 63) (W ((e.cursor+1176)%64)) (OpeningCursor.offset (e.cursor+1176))
  have h696 := OpeningLinear.register o (s696 e m) .x11 (.srli .x11 3) (v696 e m) rfl
  have h697 := OpeningLinear.register o (s697 e m) .x11 (.andi .x11 4088) (v697 e m) rfl
  have h698 := OpeningLinear.register o (s698 e m) .x31 (.add .x11 .x25) (wordAddress (cell (e.cursor+1176))) (OpeningCursor.word_address (e.cursor+1176) (by have h₀ := e.room;unfold capacity at h₀;omega))
  have h699 := OpeningLinear.register o (s699 e m) .x30 (.addi .x7 1240) (W (e.cursor+1240)) (OpeningRowOps.plusBit e.cursor 0 1240 1240 1240 rfl rfl)
  have h700 := OpeningLinear.register o (s700 e m) .x6 (.addi .x7 1304) (W (e.cursor+1304)) (OpeningRowOps.plusBit e.cursor 0 1304 1304 1304 rfl rfl)
  have h701 := OpeningLinear.register o (s701 e m) .x11 (.addi .x7 1368) (W (e.cursor+1368)) (OpeningRowOps.plusBit e.cursor 0 1368 1368 1368 rfl rfl)
  have h702 := OpeningLinear.register o (s702 e m) .x17 (.lui 1) (W 4096) rfl
  have h703 := OpeningLinear.register o (s703 e m) .x17 (.sub .x8 .x17) (W 68719472240) (by change W 68719476336-W 4096=W 68719472240;decide)
  have h704 := OpeningLinear.read o (s704 e m) .x17 .x17 1840 8589934260 (W 17592186044415) (by decide) (by change W 68719472240+signExtend12 1840=wordAddress 8589934260;decide) h.stack1840
  have h705 := OpeningLinear.register o (s705 e m) .x17 (.and .x13 .x17) (m.mem (wordAt e.index 20 3) &&& W 17592186044415) rfl
  exact LeafModel.combine h686 (LeafModel.combine h687 (LeafModel.combine h688 (LeafModel.combine h689 (LeafModel.combine h690 (LeafModel.combine h691 (LeafModel.combine h692 (LeafModel.combine h693 (LeafModel.combine h694 (LeafModel.combine h695 (LeafModel.combine h696 (LeafModel.combine h697 (LeafModel.combine h698 (LeafModel.combine h699 (LeafModel.combine h700 (LeafModel.combine h701 (LeafModel.combine h702 (LeafModel.combine h703 (LeafModel.combine h704 (LeafModel.combine h705 (LeafModel.empty _ _))))))))))))))))))))

def input (e : Env) (m : Model) : OpeningRow20.I where
  root := e.cursor
  initial := s706 e m
  word := fun k => if k=3 then m.mem (wordAt e.index 20 3) &&& W 17592186044415 else m.mem (wordAt e.index 20 k)
  room := by have := e.room;omega
  fits := by decide

theorem entry (e : Env) (m : Model) : OpeningRow20.entry (input e m)=s706 e m := by
  refine OpeningRowEntry.equalModel (OpeningRow20.entry (input e m)) (s706 e m) ?_ rfl
  intro r;cases r <;> rfl

def result (e : Env) (m : Model) := OpeningRow20.output (input e m)

theorem memory (e : Env) (m : Model) :
    (result e m).mem=CapWriter.lowMemory m.mem (e.cursor+1176) 20 (OpeningNodeStream.words m.mem e.index 20) := by
  exact OpeningRow20.memory (input e m)

theorem ready (e : Env) (m : Model) (stack : Stack e m.mem) : Ready19 e (result e m) := by
  constructor
  · exact (OpeningRow20.frame (input e m) .x0 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow20.frame (input e m) .x2 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow20.frame (input e m) .x8 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow20.frame (input e m) .x9 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow20.frame (input e m) .x18 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow20.frame (input e m) .x22 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow20.frame (input e m) .x25 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow20.frame (input e m) .x10 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow20.frame (input e m) .x7 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow20.frame (input e m) .x28 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow20.frame (input e m) .x26 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow20.frame (input e m) .x20 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow20.frame (input e m) .x27 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow20.frame (input e m) .x15 (by decide)).trans (by rw [entry];rfl)

theorem run (o : Oracle) (e : Env) (m : Model) (h : Ready20 e m) (stack : Stack e m.mem)
    (s : MachineState) (pc : s.pc=addr 686) (fit : Fits s m) :
    ∃ t n, n≤90 ∧ CommitExact.Segment o OpeningStraight.image n s t ∧ t.pc=addr 756 ∧ Fits t (result e m) := by
  have fit' : Fits s (start e m) := (start_eq e m h).symm ▸ fit
  obtain ⟨v,rv,pv,hv⟩ := OpeningLinear.block (prepare o e m stack) (i:=686) (by decide) table s pc fit'
  obtain ⟨t,n,lim,rt,pt,ht⟩ := OpeningRow20.run o (input e m) v pv ((entry e m).symm ▸ hv)
  exact ⟨t,ops.length+n,by change 20+n≤90;omega,CommitExact.compose rv rt,pt,ht⟩

end CommitGolfCandidate.Reconstruction.OpeningRowStart20
