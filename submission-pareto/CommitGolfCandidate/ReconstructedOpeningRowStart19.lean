import CommitGolfCandidate.ReconstructedOpeningRow19
import CommitGolfCandidate.ReconstructedOpeningRowEntry

namespace CommitGolfCandidate.Reconstruction.OpeningRowStart19
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
theorem start_eq (e : Env) (m : Model) (h : Ready19 e m) : start e m=m := by
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

def s757 (e : Env) (m : Model) := (start e m).set .x11 (W (e.cursor+1412))
def s758 (e : Env) (m : Model) := (s757 e m).set .x29 (m.mem (wordAt e.index 19 0))
def s759 (e : Env) (m : Model) := (s758 e m).set .x12 (m.mem (wordAt e.index 19 1))
def s760 (e : Env) (m : Model) := (s759 e m).set .x14 (m.mem (wordAt e.index 19 2))
def s761 (e : Env) (m : Model) := (s760 e m).set .x13 (m.mem (wordAt e.index 19 3))
def s762 (e : Env) (m : Model) := (s761 e m).set .x16 (W ((e.cursor+1412)%64))
def v762 (e : Env) (m : Model) : Word := (W (e.cursor+1412)) >>> (3 : Nat)
def s763 (e : Env) (m : Model) := (s762 e m).set .x11 (v762 e m)
def v763 (e : Env) (m : Model) : Word := (v762 e m) &&& signExtend12 4088
def s764 (e : Env) (m : Model) := (s763 e m).set .x11 (v763 e m)
def s765 (e : Env) (m : Model) := (s764 e m).set .x30 (wordAddress (cell (e.cursor+1412)))
def s766 (e : Env) (m : Model) := (s765 e m).set .x28 (W (e.cursor+1476))
def s767 (e : Env) (m : Model) := (s766 e m).set .x6 (W (e.cursor+1540))
def s768 (e : Env) (m : Model) := (s767 e m).set .x11 (W (e.cursor+1604))
def s769 (e : Env) (m : Model) := (s768 e m).set .x17 (W 4096)
def s770 (e : Env) (m : Model) := (s769 e m).set .x17 (W 68719472240)
def s771 (e : Env) (m : Model) := (s770 e m).set .x17 (W 4294967295)
def s772 (e : Env) (m : Model) := (s771 e m).set .x17 (m.mem (wordAt e.index 19 3) &&& W 4294967295)
def s773 (e : Env) (m : Model) := (s772 e m).set .x13 (W 4096)
def s774 (e : Env) (m : Model) := (s773 e m).set .x13 (W 68719472240)
def s775 (e : Env) (m : Model) := (s774 e m).set .x31 (W 2051)

def ops : List Instr := [
  Expr.instr .x11 (.addi .x7 1412),
  .LD .x29 .x28 608,
  .LD .x12 .x28 616,
  .LD .x14 .x28 624,
  .LD .x13 .x28 632,
  Expr.instr .x16 (.andi .x11 63),
  Expr.instr .x11 (.srli .x11 3),
  Expr.instr .x11 (.andi .x11 4088),
  Expr.instr .x30 (.add .x11 .x25),
  Expr.instr .x28 (.addi .x7 1476),
  Expr.instr .x6 (.addi .x7 1540),
  Expr.instr .x11 (.addi .x7 1604),
  Expr.instr .x17 (.lui 1),
  Expr.instr .x17 (.sub .x8 .x17),
  .LD .x17 .x17 1872,
  Expr.instr .x17 (.and .x13 .x17),
  Expr.instr .x13 (.lui 1),
  Expr.instr .x13 (.sub .x8 .x13),
  .LD .x31 .x13 1800]
theorem table : OpeningStraight.Listed 756 ops := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem prepare (o : Oracle) (e : Env) (m : Model) (h : Stack e m.mem) : Contract o ops (start e m) (s775 e m) := by
  have h756 := OpeningLinear.register o (start e m) .x11 (.addi .x7 1412) (W (e.cursor+1412)) (OpeningRowOps.plusBit e.cursor 0 1412 1412 1412 rfl rfl)
  have h757 := OpeningLinear.read o (s757 e m) .x29 .x28 608 (wordAt e.index 19 0) (m.mem (wordAt e.index 19 0)) (by have := word_room e.index 19 0 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 19 0 608 rfl) rfl
  have h758 := OpeningLinear.read o (s758 e m) .x12 .x28 616 (wordAt e.index 19 1) (m.mem (wordAt e.index 19 1)) (by have := word_room e.index 19 1 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 19 1 616 rfl) rfl
  have h759 := OpeningLinear.read o (s759 e m) .x14 .x28 624 (wordAt e.index 19 2) (m.mem (wordAt e.index 19 2)) (by have := word_room e.index 19 2 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 19 2 624 rfl) rfl
  have h760 := OpeningLinear.read o (s760 e m) .x13 .x28 632 (wordAt e.index 19 3) (m.mem (wordAt e.index 19 3)) (by have := word_room e.index 19 3 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 19 3 632 rfl) rfl
  have h761 := OpeningLinear.register o (s761 e m) .x16 (.andi .x11 63) (W ((e.cursor+1412)%64)) (OpeningCursor.offset (e.cursor+1412))
  have h762 := OpeningLinear.register o (s762 e m) .x11 (.srli .x11 3) (v762 e m) rfl
  have h763 := OpeningLinear.register o (s763 e m) .x11 (.andi .x11 4088) (v763 e m) rfl
  have h764 := OpeningLinear.register o (s764 e m) .x30 (.add .x11 .x25) (wordAddress (cell (e.cursor+1412))) (OpeningCursor.word_address (e.cursor+1412) (by have h₀ := e.room;unfold capacity at h₀;omega))
  have h765 := OpeningLinear.register o (s765 e m) .x28 (.addi .x7 1476) (W (e.cursor+1476)) (OpeningRowOps.plusBit e.cursor 0 1476 1476 1476 rfl rfl)
  have h766 := OpeningLinear.register o (s766 e m) .x6 (.addi .x7 1540) (W (e.cursor+1540)) (OpeningRowOps.plusBit e.cursor 0 1540 1540 1540 rfl rfl)
  have h767 := OpeningLinear.register o (s767 e m) .x11 (.addi .x7 1604) (W (e.cursor+1604)) (OpeningRowOps.plusBit e.cursor 0 1604 1604 1604 rfl rfl)
  have h768 := OpeningLinear.register o (s768 e m) .x17 (.lui 1) (W 4096) rfl
  have h769 := OpeningLinear.register o (s769 e m) .x17 (.sub .x8 .x17) (W 68719472240) (by change W 68719476336-W 4096=W 68719472240;decide)
  have h770 := OpeningLinear.read o (s770 e m) .x17 .x17 1872 8589934264 (W 4294967295) (by decide) (by change W 68719472240+signExtend12 1872=wordAddress 8589934264;decide) h.stack1872
  have h771 := OpeningLinear.register o (s771 e m) .x17 (.and .x13 .x17) (m.mem (wordAt e.index 19 3) &&& W 4294967295) rfl
  have h772 := OpeningLinear.register o (s772 e m) .x13 (.lui 1) (W 4096) rfl
  have h773 := OpeningLinear.register o (s773 e m) .x13 (.sub .x8 .x13) (W 68719472240) (by change W 68719476336-W 4096=W 68719472240;decide)
  have h774 := OpeningLinear.read o (s774 e m) .x31 .x13 1800 8589934255 (W 2051) (by decide) (by change W 68719472240+signExtend12 1800=wordAddress 8589934255;decide) h.stack1800
  exact LeafModel.combine h756 (LeafModel.combine h757 (LeafModel.combine h758 (LeafModel.combine h759 (LeafModel.combine h760 (LeafModel.combine h761 (LeafModel.combine h762 (LeafModel.combine h763 (LeafModel.combine h764 (LeafModel.combine h765 (LeafModel.combine h766 (LeafModel.combine h767 (LeafModel.combine h768 (LeafModel.combine h769 (LeafModel.combine h770 (LeafModel.combine h771 (LeafModel.combine h772 (LeafModel.combine h773 (LeafModel.combine h774 (LeafModel.empty _ _)))))))))))))))))))

def input (e : Env) (m : Model) : OpeningRow19.I where
  root := e.cursor
  initial := s775 e m
  word := fun k => if k=3 then m.mem (wordAt e.index 19 3) &&& W 4294967295 else m.mem (wordAt e.index 19 k)
  room := by have := e.room;omega
  fits := by decide

theorem entry (e : Env) (m : Model) : OpeningRow19.entry (input e m)=s775 e m := by
  refine OpeningRowEntry.equalModel (OpeningRow19.entry (input e m)) (s775 e m) ?_ rfl
  intro r;cases r <;> rfl

def result (e : Env) (m : Model) := OpeningRow19.output (input e m)

theorem memory (e : Env) (m : Model) :
    (result e m).mem=CapWriter.lowMemory m.mem (e.cursor+1412) 19 (OpeningNodeStream.words m.mem e.index 19) := by
  exact OpeningRow19.memory (input e m)

theorem ready (e : Env) (m : Model) (stack : Stack e m.mem) : Ready18 e (result e m) := by
  constructor
  · exact (OpeningRow19.frame (input e m) .x0 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow19.frame (input e m) .x2 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow19.frame (input e m) .x8 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow19.frame (input e m) .x9 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow19.frame (input e m) .x18 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow19.frame (input e m) .x22 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow19.frame (input e m) .x25 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow19.frame (input e m) .x10 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow19.frame (input e m) .x7 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow19.frame (input e m) .x26 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow19.frame (input e m) .x20 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow19.frame (input e m) .x27 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow19.frame (input e m) .x15 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow19.frame (input e m) .x31 (by decide)).trans (by rw [entry];rfl)

theorem run (o : Oracle) (e : Env) (m : Model) (h : Ready19 e m) (stack : Stack e m.mem)
    (s : MachineState) (pc : s.pc=addr 756) (fit : Fits s m) :
    ∃ t n, n≤90 ∧ CommitExact.Segment o OpeningStraight.image n s t ∧ t.pc=addr 825 ∧ Fits t (result e m) := by
  have fit' : Fits s (start e m) := (start_eq e m h).symm ▸ fit
  obtain ⟨v,rv,pv,hv⟩ := OpeningLinear.block (prepare o e m stack) (i:=756) (by decide) table s pc fit'
  obtain ⟨t,n,lim,rt,pt,ht⟩ := OpeningRow19.run o (input e m) v pv ((entry e m).symm ▸ hv)
  exact ⟨t,ops.length+n,by change 19+n≤90;omega,CommitExact.compose rv rt,pt,ht⟩

end CommitGolfCandidate.Reconstruction.OpeningRowStart19
