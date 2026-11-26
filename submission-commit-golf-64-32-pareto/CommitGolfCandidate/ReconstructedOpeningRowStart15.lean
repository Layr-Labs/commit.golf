import CommitGolfCandidate.ReconstructedOpeningRow15
import CommitGolfCandidate.ReconstructedOpeningRowEntry

namespace CommitGolfCandidate.Reconstruction.OpeningRowStart15
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
  | .x7 => W 36
  | .x20 => W (e.cursor+2051)
  | .x15 => basePtr e.index 15
  | .x31 => W 2051
  | r => m.reg r,m.mem⟩
theorem start_eq (e : Env) (m : Model) (h : Ready15 e m) : start e m=m := by
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
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact h.r31.symm

def s1025 (e : Env) (m : Model) := (start e m).set .x13 (W (e.cursor+2303))
def s1026 (e : Env) (m : Model) := (s1025 e m).set .x12 (m.mem (wordAt e.index 15 0))
def s1027 (e : Env) (m : Model) := (s1026 e m).set .x11 (m.mem (wordAt e.index 15 1))
def s1028 (e : Env) (m : Model) := (s1027 e m).set .x17 (m.mem (wordAt e.index 15 2))
def s1029 (e : Env) (m : Model) := (s1028 e m).set .x15 (m.mem (wordAt e.index 15 3))
def s1030 (e : Env) (m : Model) := (s1029 e m).set .x16 (W ((e.cursor+2303)%64))
def v1030 (e : Env) (m : Model) : Word := (W (e.cursor+2303)) >>> (3 : Nat)
def s1031 (e : Env) (m : Model) := (s1030 e m).set .x13 (v1030 e m)
def v1031 (e : Env) (m : Model) : Word := (v1030 e m) &&& signExtend12 4088
def s1032 (e : Env) (m : Model) := (s1031 e m).set .x13 (v1031 e m)
def s1033 (e : Env) (m : Model) := (s1032 e m).set .x14 (wordAddress (cell (e.cursor+2303)))
def s1034 (e : Env) (m : Model) := (s1033 e m).set .x13 (W 4096)
def s1035 (e : Env) (m : Model) := (s1034 e m).set .x13 (W 68719472240)
def s1036 (e : Env) (m : Model) := (s1035 e m).set .x13 (W 8589934591)
def s1037 (e : Env) (m : Model) := (s1036 e m).set .x15 (m.mem (wordAt e.index 15 3) &&& W 8589934591)
def s1038 (e : Env) (m : Model) := (s1037 e m).set .x13 (W 4096)
def s1039 (e : Env) (m : Model) := (s1038 e m).set .x13 (W 68719472240)
def s1040 (e : Env) (m : Model) := (s1039 e m).set .x6 (W 536870911)

def ops : List Instr := [
  Expr.instr .x13 (.addi .x20 252),
  .LD .x12 .x15 480,
  .LD .x11 .x15 488,
  .LD .x17 .x15 496,
  .LD .x15 .x15 504,
  Expr.instr .x16 (.andi .x13 63),
  Expr.instr .x13 (.srli .x13 3),
  Expr.instr .x13 (.andi .x13 4088),
  Expr.instr .x14 (.add .x13 .x25),
  Expr.instr .x13 (.lui 1),
  Expr.instr .x13 (.sub .x8 .x13),
  .LD .x13 .x13 1832,
  Expr.instr .x15 (.and .x15 .x13),
  Expr.instr .x13 (.lui 1),
  Expr.instr .x13 (.sub .x8 .x13),
  .LD .x6 .x13 1808]
theorem table : OpeningStraight.Listed 1024 ops := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem prepare (o : Oracle) (e : Env) (m : Model) (h : Stack e m.mem) : Contract o ops (start e m) (s1040 e m) := by
  have h1024 := OpeningLinear.register o (start e m) .x13 (.addi .x20 252) (W (e.cursor+2303)) (OpeningRowOps.plusBit e.cursor 2051 252 2303 252 rfl rfl)
  have h1025 := OpeningLinear.read o (s1025 e m) .x12 .x15 480 (wordAt e.index 15 0) (m.mem (wordAt e.index 15 0)) (by have := word_room e.index 15 0 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 15 0 480 rfl) rfl
  have h1026 := OpeningLinear.read o (s1026 e m) .x11 .x15 488 (wordAt e.index 15 1) (m.mem (wordAt e.index 15 1)) (by have := word_room e.index 15 1 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 15 1 488 rfl) rfl
  have h1027 := OpeningLinear.read o (s1027 e m) .x17 .x15 496 (wordAt e.index 15 2) (m.mem (wordAt e.index 15 2)) (by have := word_room e.index 15 2 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 15 2 496 rfl) rfl
  have h1028 := OpeningLinear.read o (s1028 e m) .x15 .x15 504 (wordAt e.index 15 3) (m.mem (wordAt e.index 15 3)) (by have := word_room e.index 15 3 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 15 3 504 rfl) rfl
  have h1029 := OpeningLinear.register o (s1029 e m) .x16 (.andi .x13 63) (W ((e.cursor+2303)%64)) (OpeningCursor.offset (e.cursor+2303))
  have h1030 := OpeningLinear.register o (s1030 e m) .x13 (.srli .x13 3) (v1030 e m) rfl
  have h1031 := OpeningLinear.register o (s1031 e m) .x13 (.andi .x13 4088) (v1031 e m) rfl
  have h1032 := OpeningLinear.register o (s1032 e m) .x14 (.add .x13 .x25) (wordAddress (cell (e.cursor+2303))) (OpeningCursor.word_address (e.cursor+2303) (by have h₀ := e.room;unfold capacity at h₀;omega))
  have h1033 := OpeningLinear.register o (s1033 e m) .x13 (.lui 1) (W 4096) rfl
  have h1034 := OpeningLinear.register o (s1034 e m) .x13 (.sub .x8 .x13) (W 68719472240) (by change W 68719476336-W 4096=W 68719472240;decide)
  have h1035 := OpeningLinear.read o (s1035 e m) .x13 .x13 1832 8589934259 (W 8589934591) (by decide) (by change W 68719472240+signExtend12 1832=wordAddress 8589934259;decide) h.stack1832
  have h1036 := OpeningLinear.register o (s1036 e m) .x15 (.and .x15 .x13) (m.mem (wordAt e.index 15 3) &&& W 8589934591) rfl
  have h1037 := OpeningLinear.register o (s1037 e m) .x13 (.lui 1) (W 4096) rfl
  have h1038 := OpeningLinear.register o (s1038 e m) .x13 (.sub .x8 .x13) (W 68719472240) (by change W 68719476336-W 4096=W 68719472240;decide)
  have h1039 := OpeningLinear.read o (s1039 e m) .x6 .x13 1808 8589934256 (W 536870911) (by decide) (by change W 68719472240+signExtend12 1808=wordAddress 8589934256;decide) h.stack1808
  exact LeafModel.combine h1024 (LeafModel.combine h1025 (LeafModel.combine h1026 (LeafModel.combine h1027 (LeafModel.combine h1028 (LeafModel.combine h1029 (LeafModel.combine h1030 (LeafModel.combine h1031 (LeafModel.combine h1032 (LeafModel.combine h1033 (LeafModel.combine h1034 (LeafModel.combine h1035 (LeafModel.combine h1036 (LeafModel.combine h1037 (LeafModel.combine h1038 (LeafModel.combine h1039 (LeafModel.empty _ _))))))))))))))))

def input (e : Env) (m : Model) : OpeningRow15.I where
  root := e.cursor
  initial := s1040 e m
  word := fun k => if k=3 then m.mem (wordAt e.index 15 3) &&& W 8589934591 else m.mem (wordAt e.index 15 k)
  room := by have := e.room;omega
  fits := by decide

theorem entry (e : Env) (m : Model) : OpeningRow15.entry (input e m)=s1040 e m := by
  refine OpeningRowEntry.equalModel (OpeningRow15.entry (input e m)) (s1040 e m) ?_ rfl
  intro r;cases r <;> rfl

def result (e : Env) (m : Model) := OpeningRow15.output (input e m)

theorem memory (e : Env) (m : Model) :
    (result e m).mem=CapWriter.lowMemory m.mem (e.cursor+2303) 15 (OpeningNodeStream.words m.mem e.index 15) := by
  exact OpeningRow15.memory (input e m)

theorem ready (e : Env) (m : Model) (stack : Stack e m.mem) : Ready14 e (result e m) := by
  constructor
  · exact (OpeningRow15.frame (input e m) .x0 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow15.frame (input e m) .x2 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow15.frame (input e m) .x8 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow15.frame (input e m) .x9 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow15.frame (input e m) .x18 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow15.frame (input e m) .x22 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow15.frame (input e m) .x25 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow15.frame (input e m) .x10 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow15.frame (input e m) .x7 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow15.frame (input e m) .x20 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow15.frame (input e m) .x31 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow15.frame (input e m) .x6 (by decide)).trans (by rw [entry];rfl)

theorem run (o : Oracle) (e : Env) (m : Model) (h : Ready15 e m) (stack : Stack e m.mem)
    (s : MachineState) (pc : s.pc=addr 1024) (fit : Fits s m) :
    ∃ t n, n≤90 ∧ CommitExact.Segment o OpeningStraight.image n s t ∧ t.pc=addr 1096 ∧ Fits t (result e m) := by
  have fit' : Fits s (start e m) := (start_eq e m h).symm ▸ fit
  obtain ⟨v,rv,pv,hv⟩ := OpeningLinear.block (prepare o e m stack) (i:=1024) (by decide) table s pc fit'
  obtain ⟨t,n,lim,rt,pt,ht⟩ := OpeningRow15.run o (input e m) v pv ((entry e m).symm ▸ hv)
  exact ⟨t,ops.length+n,by change 16+n≤90;omega,CommitExact.compose rv rt,pt,ht⟩

end CommitGolfCandidate.Reconstruction.OpeningRowStart15
