import CommitGolfCandidate.ReconstructedOpeningRow14
import CommitGolfCandidate.ReconstructedOpeningRowEntry

namespace CommitGolfCandidate.Reconstruction.OpeningRowStart14
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
  | .x31 => W 2051
  | .x6 => W 536870911
  | r => m.reg r,m.mem⟩
theorem start_eq (e : Env) (m : Model) (h : Ready14 e m) : start e m=m := by
  refine OpeningRowEntry.equalModel (start e m) m ?_ rfl
  intro r;cases r
  · exact h.r0.symm
  · rfl
  · exact h.r2.symm
  · rfl
  · rfl
  · rfl
  · exact h.r6.symm
  · exact h.r7.symm
  · exact h.r8.symm
  · exact h.r9.symm
  · exact h.r10.symm
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
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

def s1097 (e : Env) (m : Model) := (start e m).set .x13 (W (e.cursor+2528))
def s1098 (e : Env) (m : Model) := (s1097 e m).set .x11 (W 4096)
def s1099 (e : Env) (m : Model) := (s1098 e m).set .x11 (W 68719472240)
def s1100 (e : Env) (m : Model) := (s1099 e m).set .x14 (basePtr e.index 14)
def s1101 (e : Env) (m : Model) := (s1100 e m).set .x12 (m.mem (wordAt e.index 14 0))
def s1102 (e : Env) (m : Model) := (s1101 e m).set .x11 (m.mem (wordAt e.index 14 1))
def s1103 (e : Env) (m : Model) := (s1102 e m).set .x17 (m.mem (wordAt e.index 14 2))
def s1104 (e : Env) (m : Model) := (s1103 e m).set .x15 (m.mem (wordAt e.index 14 3))
def s1105 (e : Env) (m : Model) := (s1104 e m).set .x16 (W ((e.cursor+2528)%64))
def v1105 (e : Env) (m : Model) : Word := (W (e.cursor+2528)) >>> (3 : Nat)
def s1106 (e : Env) (m : Model) := (s1105 e m).set .x13 (v1105 e m)
def v1106 (e : Env) (m : Model) : Word := (v1105 e m) &&& signExtend12 4088
def s1107 (e : Env) (m : Model) := (s1106 e m).set .x13 (v1106 e m)
def s1108 (e : Env) (m : Model) := (s1107 e m).set .x14 (wordAddress (cell (e.cursor+2528)))
def s1109 (e : Env) (m : Model) := (s1108 e m).set .x15 (m.mem (wordAt e.index 14 3) &&& W 536870911)

def ops : List Instr := [
  Expr.instr .x13 (.addi .x20 477),
  Expr.instr .x11 (.lui 1),
  Expr.instr .x11 (.sub .x8 .x11),
  .LD .x14 .x11 1880,
  .LD .x12 .x14 448,
  .LD .x11 .x14 456,
  .LD .x17 .x14 464,
  .LD .x15 .x14 472,
  Expr.instr .x16 (.andi .x13 63),
  Expr.instr .x13 (.srli .x13 3),
  Expr.instr .x13 (.andi .x13 4088),
  Expr.instr .x14 (.add .x13 .x25),
  Expr.instr .x15 (.and .x15 .x6)]
theorem table : OpeningStraight.Listed 1096 ops := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem prepare (o : Oracle) (e : Env) (m : Model) (h : Stack e m.mem) : Contract o ops (start e m) (s1109 e m) := by
  have h1096 := OpeningLinear.register o (start e m) .x13 (.addi .x20 477) (W (e.cursor+2528)) (OpeningRowOps.plusBit e.cursor 2051 477 2528 477 rfl rfl)
  have h1097 := OpeningLinear.register o (s1097 e m) .x11 (.lui 1) (W 4096) rfl
  have h1098 := OpeningLinear.register o (s1098 e m) .x11 (.sub .x8 .x11) (W 68719472240) (by change W 68719476336-W 4096=W 68719472240;decide)
  have h1099 := OpeningLinear.read o (s1099 e m) .x14 .x11 1880 8589934265 (basePtr e.index 14) (by decide) (by change W 68719472240+signExtend12 1880=wordAddress 8589934265;decide) h.stack1880
  have h1100 := OpeningLinear.read o (s1100 e m) .x12 .x14 448 (wordAt e.index 14 0) (m.mem (wordAt e.index 14 0)) (by have := word_room e.index 14 0 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 14 0 448 rfl) rfl
  have h1101 := OpeningLinear.read o (s1101 e m) .x11 .x14 456 (wordAt e.index 14 1) (m.mem (wordAt e.index 14 1)) (by have := word_room e.index 14 1 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 14 1 456 rfl) rfl
  have h1102 := OpeningLinear.read o (s1102 e m) .x17 .x14 464 (wordAt e.index 14 2) (m.mem (wordAt e.index 14 2)) (by have := word_room e.index 14 2 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 14 2 464 rfl) rfl
  have h1103 := OpeningLinear.read o (s1103 e m) .x15 .x14 472 (wordAt e.index 14 3) (m.mem (wordAt e.index 14 3)) (by have := word_room e.index 14 3 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 14 3 472 rfl) rfl
  have h1104 := OpeningLinear.register o (s1104 e m) .x16 (.andi .x13 63) (W ((e.cursor+2528)%64)) (OpeningCursor.offset (e.cursor+2528))
  have h1105 := OpeningLinear.register o (s1105 e m) .x13 (.srli .x13 3) (v1105 e m) rfl
  have h1106 := OpeningLinear.register o (s1106 e m) .x13 (.andi .x13 4088) (v1106 e m) rfl
  have h1107 := OpeningLinear.register o (s1107 e m) .x14 (.add .x13 .x25) (wordAddress (cell (e.cursor+2528))) (OpeningCursor.word_address (e.cursor+2528) (by have h₀ := e.room;unfold capacity at h₀;omega))
  have h1108 := OpeningLinear.register o (s1108 e m) .x15 (.and .x15 .x6) (m.mem (wordAt e.index 14 3) &&& W 536870911) rfl
  exact LeafModel.combine h1096 (LeafModel.combine h1097 (LeafModel.combine h1098 (LeafModel.combine h1099 (LeafModel.combine h1100 (LeafModel.combine h1101 (LeafModel.combine h1102 (LeafModel.combine h1103 (LeafModel.combine h1104 (LeafModel.combine h1105 (LeafModel.combine h1106 (LeafModel.combine h1107 (LeafModel.combine h1108 (LeafModel.empty _ _)))))))))))))

def input (e : Env) (m : Model) : OpeningRow14.I where
  root := e.cursor
  initial := s1109 e m
  word := fun k => if k=3 then m.mem (wordAt e.index 14 3) &&& W 536870911 else m.mem (wordAt e.index 14 k)
  room := by have := e.room;omega
  fits := by decide

theorem entry (e : Env) (m : Model) : OpeningRow14.entry (input e m)=s1109 e m := by
  refine OpeningRowEntry.equalModel (OpeningRow14.entry (input e m)) (s1109 e m) ?_ rfl
  intro r;cases r <;> rfl

def result (e : Env) (m : Model) := OpeningRow14.output (input e m)

theorem memory (e : Env) (m : Model) :
    (result e m).mem=CapWriter.lowMemory m.mem (e.cursor+2528) 14 (OpeningNodeStream.words m.mem e.index 14) := by
  exact OpeningRow14.memory (input e m)

theorem ready (e : Env) (m : Model) (stack : Stack e m.mem) : Ready13 e (result e m) := by
  constructor
  · exact (OpeningRow14.frame (input e m) .x0 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow14.frame (input e m) .x2 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow14.frame (input e m) .x8 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow14.frame (input e m) .x9 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow14.frame (input e m) .x18 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow14.frame (input e m) .x22 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow14.frame (input e m) .x25 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow14.frame (input e m) .x10 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow14.frame (input e m) .x7 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow14.frame (input e m) .x20 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow14.frame (input e m) .x31 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow14.frame (input e m) .x6 (by decide)).trans (by rw [entry];rfl)

theorem run (o : Oracle) (e : Env) (m : Model) (h : Ready14 e m) (stack : Stack e m.mem)
    (s : MachineState) (pc : s.pc=addr 1096) (fit : Fits s m) :
    ∃ t n, n≤90 ∧ CommitExact.Segment o OpeningStraight.image n s t ∧ t.pc=addr 1164 ∧ Fits t (result e m) := by
  have fit' : Fits s (start e m) := (start_eq e m h).symm ▸ fit
  obtain ⟨v,rv,pv,hv⟩ := OpeningLinear.block (prepare o e m stack) (i:=1096) (by decide) table s pc fit'
  obtain ⟨t,n,lim,rt,pt,ht⟩ := OpeningRow14.run o (input e m) v pv ((entry e m).symm ▸ hv)
  exact ⟨t,ops.length+n,by change 13+n≤90;omega,CommitExact.compose rv rt,pt,ht⟩

end CommitGolfCandidate.Reconstruction.OpeningRowStart14
