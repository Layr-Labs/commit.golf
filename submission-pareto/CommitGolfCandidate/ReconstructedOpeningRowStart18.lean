import CommitGolfCandidate.ReconstructedOpeningRow18
import CommitGolfCandidate.ReconstructedOpeningRowEntry

namespace CommitGolfCandidate.Reconstruction.OpeningRowStart18
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
  | .x26 => basePtr e.index 18
  | .x20 => basePtr e.index 17
  | .x27 => basePtr e.index 16
  | .x15 => basePtr e.index 15
  | .x31 => W 2051
  | r => m.reg r,m.mem⟩
theorem start_eq (e : Env) (m : Model) (h : Ready18 e m) : start e m=m := by
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
  · rfl
  · rfl
  · rfl
  · exact h.r31.symm

def s826 (e : Env) (m : Model) := (start e m).set .x11 (W (e.cursor+1636))
def s827 (e : Env) (m : Model) := (s826 e m).set .x28 (m.mem (wordAt e.index 18 0))
def s828 (e : Env) (m : Model) := (s827 e m).set .x12 (m.mem (wordAt e.index 18 1))
def s829 (e : Env) (m : Model) := (s828 e m).set .x14 (m.mem (wordAt e.index 18 2))
def s830 (e : Env) (m : Model) := (s829 e m).set .x13 (m.mem (wordAt e.index 18 3))
def s831 (e : Env) (m : Model) := (s830 e m).set .x16 (W ((e.cursor+1636)%64))
def v831 (e : Env) (m : Model) : Word := (W (e.cursor+1636)) >>> (3 : Nat)
def s832 (e : Env) (m : Model) := (s831 e m).set .x11 (v831 e m)
def v832 (e : Env) (m : Model) : Word := (v831 e m) &&& signExtend12 4088
def s833 (e : Env) (m : Model) := (s832 e m).set .x11 (v832 e m)
def s834 (e : Env) (m : Model) := (s833 e m).set .x30 (wordAddress (cell (e.cursor+1636)))
def s835 (e : Env) (m : Model) := (s834 e m).set .x29 (W (e.cursor+1700))
def s836 (e : Env) (m : Model) := (s835 e m).set .x6 (W (e.cursor+1764))
def s837 (e : Env) (m : Model) := (s836 e m).set .x11 (W (e.cursor+1828))
def s838 (e : Env) (m : Model) := (s837 e m).set .x17 (W 4096)
def s839 (e : Env) (m : Model) := (s838 e m).set .x17 (W 68719472240)
def s840 (e : Env) (m : Model) := (s839 e m).set .x17 (W 2147483647)
def s841 (e : Env) (m : Model) := (s840 e m).set .x17 (m.mem (wordAt e.index 18 3) &&& W 2147483647)

def ops : List Instr := [
  Expr.instr .x11 (.addi .x7 1636),
  .LD .x28 .x26 576,
  .LD .x12 .x26 584,
  .LD .x14 .x26 592,
  .LD .x13 .x26 600,
  Expr.instr .x16 (.andi .x11 63),
  Expr.instr .x11 (.srli .x11 3),
  Expr.instr .x11 (.andi .x11 4088),
  Expr.instr .x30 (.add .x11 .x25),
  Expr.instr .x29 (.addi .x7 1700),
  Expr.instr .x6 (.addi .x7 1764),
  Expr.instr .x11 (.addi .x7 1828),
  Expr.instr .x17 (.lui 1),
  Expr.instr .x17 (.sub .x8 .x17),
  .LD .x17 .x17 1864,
  Expr.instr .x17 (.and .x13 .x17)]
theorem table : OpeningStraight.Listed 825 ops := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem prepare (o : Oracle) (e : Env) (m : Model) (h : Stack e m.mem) : Contract o ops (start e m) (s841 e m) := by
  have h825 := OpeningLinear.register o (start e m) .x11 (.addi .x7 1636) (W (e.cursor+1636)) (OpeningRowOps.plusBit e.cursor 0 1636 1636 1636 rfl rfl)
  have h826 := OpeningLinear.read o (s826 e m) .x28 .x26 576 (wordAt e.index 18 0) (m.mem (wordAt e.index 18 0)) (by have := word_room e.index 18 0 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 18 0 576 rfl) rfl
  have h827 := OpeningLinear.read o (s827 e m) .x12 .x26 584 (wordAt e.index 18 1) (m.mem (wordAt e.index 18 1)) (by have := word_room e.index 18 1 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 18 1 584 rfl) rfl
  have h828 := OpeningLinear.read o (s828 e m) .x14 .x26 592 (wordAt e.index 18 2) (m.mem (wordAt e.index 18 2)) (by have := word_room e.index 18 2 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 18 2 592 rfl) rfl
  have h829 := OpeningLinear.read o (s829 e m) .x13 .x26 600 (wordAt e.index 18 3) (m.mem (wordAt e.index 18 3)) (by have := word_room e.index 18 3 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 18 3 600 rfl) rfl
  have h830 := OpeningLinear.register o (s830 e m) .x16 (.andi .x11 63) (W ((e.cursor+1636)%64)) (OpeningCursor.offset (e.cursor+1636))
  have h831 := OpeningLinear.register o (s831 e m) .x11 (.srli .x11 3) (v831 e m) rfl
  have h832 := OpeningLinear.register o (s832 e m) .x11 (.andi .x11 4088) (v832 e m) rfl
  have h833 := OpeningLinear.register o (s833 e m) .x30 (.add .x11 .x25) (wordAddress (cell (e.cursor+1636))) (OpeningCursor.word_address (e.cursor+1636) (by have h₀ := e.room;unfold capacity at h₀;omega))
  have h834 := OpeningLinear.register o (s834 e m) .x29 (.addi .x7 1700) (W (e.cursor+1700)) (OpeningRowOps.plusBit e.cursor 0 1700 1700 1700 rfl rfl)
  have h835 := OpeningLinear.register o (s835 e m) .x6 (.addi .x7 1764) (W (e.cursor+1764)) (OpeningRowOps.plusBit e.cursor 0 1764 1764 1764 rfl rfl)
  have h836 := OpeningLinear.register o (s836 e m) .x11 (.addi .x7 1828) (W (e.cursor+1828)) (OpeningRowOps.plusBit e.cursor 0 1828 1828 1828 rfl rfl)
  have h837 := OpeningLinear.register o (s837 e m) .x17 (.lui 1) (W 4096) rfl
  have h838 := OpeningLinear.register o (s838 e m) .x17 (.sub .x8 .x17) (W 68719472240) (by change W 68719476336-W 4096=W 68719472240;decide)
  have h839 := OpeningLinear.read o (s839 e m) .x17 .x17 1864 8589934263 (W 2147483647) (by decide) (by change W 68719472240+signExtend12 1864=wordAddress 8589934263;decide) h.stack1864
  have h840 := OpeningLinear.register o (s840 e m) .x17 (.and .x13 .x17) (m.mem (wordAt e.index 18 3) &&& W 2147483647) rfl
  exact LeafModel.combine h825 (LeafModel.combine h826 (LeafModel.combine h827 (LeafModel.combine h828 (LeafModel.combine h829 (LeafModel.combine h830 (LeafModel.combine h831 (LeafModel.combine h832 (LeafModel.combine h833 (LeafModel.combine h834 (LeafModel.combine h835 (LeafModel.combine h836 (LeafModel.combine h837 (LeafModel.combine h838 (LeafModel.combine h839 (LeafModel.combine h840 (LeafModel.empty _ _))))))))))))))))

def input (e : Env) (m : Model) : OpeningRow18.I where
  root := e.cursor
  initial := s841 e m
  word := fun k => if k=3 then m.mem (wordAt e.index 18 3) &&& W 2147483647 else m.mem (wordAt e.index 18 k)
  room := by have := e.room;omega
  fits := by decide

theorem entry (e : Env) (m : Model) : OpeningRow18.entry (input e m)=s841 e m := by
  refine OpeningRowEntry.equalModel (OpeningRow18.entry (input e m)) (s841 e m) ?_ rfl
  intro r;cases r <;> rfl

def result (e : Env) (m : Model) := OpeningRow18.output (input e m)

theorem memory (e : Env) (m : Model) :
    (result e m).mem=CapWriter.lowMemory m.mem (e.cursor+1636) 18 (OpeningNodeStream.words m.mem e.index 18) := by
  exact OpeningRow18.memory (input e m)

theorem ready (e : Env) (m : Model) (stack : Stack e m.mem) : Ready17 e (result e m) := by
  constructor
  · exact (OpeningRow18.frame (input e m) .x0 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow18.frame (input e m) .x2 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow18.frame (input e m) .x8 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow18.frame (input e m) .x9 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow18.frame (input e m) .x18 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow18.frame (input e m) .x22 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow18.frame (input e m) .x25 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow18.frame (input e m) .x10 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow18.frame (input e m) .x7 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow18.frame (input e m) .x20 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow18.frame (input e m) .x27 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow18.frame (input e m) .x15 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow18.frame (input e m) .x31 (by decide)).trans (by rw [entry];rfl)

theorem run (o : Oracle) (e : Env) (m : Model) (h : Ready18 e m) (stack : Stack e m.mem)
    (s : MachineState) (pc : s.pc=addr 825) (fit : Fits s m) :
    ∃ t n, n≤90 ∧ CommitExact.Segment o OpeningStraight.image n s t ∧ t.pc=addr 891 ∧ Fits t (result e m) := by
  have fit' : Fits s (start e m) := (start_eq e m h).symm ▸ fit
  obtain ⟨v,rv,pv,hv⟩ := OpeningLinear.block (prepare o e m stack) (i:=825) (by decide) table s pc fit'
  obtain ⟨t,n,lim,rt,pt,ht⟩ := OpeningRow18.run o (input e m) v pv ((entry e m).symm ▸ hv)
  exact ⟨t,ops.length+n,by change 16+n≤90;omega,CommitExact.compose rv rt,pt,ht⟩

end CommitGolfCandidate.Reconstruction.OpeningRowStart18
