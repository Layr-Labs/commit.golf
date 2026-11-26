import CommitGolfCandidate.ReconstructedOpeningRow13
import CommitGolfCandidate.ReconstructedOpeningRowEntry

namespace CommitGolfCandidate.Reconstruction.OpeningRowStart13
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
theorem start_eq (e : Env) (m : Model) (h : Ready13 e m) : start e m=m := by
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

def s1165 (e : Env) (m : Model) := (start e m).set .x13 (W (e.cursor+2749))
def s1166 (e : Env) (m : Model) := (s1165 e m).set .x11 (W 4096)
def s1167 (e : Env) (m : Model) := (s1166 e m).set .x11 (W 68719472240)
def s1168 (e : Env) (m : Model) := (s1167 e m).set .x14 (basePtr e.index 13)
def s1169 (e : Env) (m : Model) := (s1168 e m).set .x12 (m.mem (wordAt e.index 13 0))
def s1170 (e : Env) (m : Model) := (s1169 e m).set .x11 (m.mem (wordAt e.index 13 1))
def s1171 (e : Env) (m : Model) := (s1170 e m).set .x17 (m.mem (wordAt e.index 13 2))
def s1172 (e : Env) (m : Model) := (s1171 e m).set .x15 (m.mem (wordAt e.index 13 3))
def s1173 (e : Env) (m : Model) := (s1172 e m).set .x16 (W ((e.cursor+2749)%64))
def v1173 (e : Env) (m : Model) : Word := (W (e.cursor+2749)) >>> (3 : Nat)
def s1174 (e : Env) (m : Model) := (s1173 e m).set .x13 (v1173 e m)
def v1174 (e : Env) (m : Model) : Word := (v1173 e m) &&& signExtend12 4088
def s1175 (e : Env) (m : Model) := (s1174 e m).set .x13 (v1174 e m)
def s1176 (e : Env) (m : Model) := (s1175 e m).set .x14 (wordAddress (cell (e.cursor+2749)))
def s1177 (e : Env) (m : Model) := (s1176 e m).set .x15 (m.mem (wordAt e.index 13 3) &&& W 536870911)

def ops : List Instr := [
  Expr.instr .x13 (.addi .x20 698),
  Expr.instr .x11 (.lui 1),
  Expr.instr .x11 (.sub .x8 .x11),
  .LD .x14 .x11 1888,
  .LD .x12 .x14 416,
  .LD .x11 .x14 424,
  .LD .x17 .x14 432,
  .LD .x15 .x14 440,
  Expr.instr .x16 (.andi .x13 63),
  Expr.instr .x13 (.srli .x13 3),
  Expr.instr .x13 (.andi .x13 4088),
  Expr.instr .x14 (.add .x13 .x25),
  Expr.instr .x15 (.and .x15 .x6)]
theorem table : OpeningStraight.Listed 1164 ops := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem prepare (o : Oracle) (e : Env) (m : Model) (h : Stack e m.mem) : Contract o ops (start e m) (s1177 e m) := by
  have h1164 := OpeningLinear.register o (start e m) .x13 (.addi .x20 698) (W (e.cursor+2749)) (OpeningRowOps.plusBit e.cursor 2051 698 2749 698 rfl rfl)
  have h1165 := OpeningLinear.register o (s1165 e m) .x11 (.lui 1) (W 4096) rfl
  have h1166 := OpeningLinear.register o (s1166 e m) .x11 (.sub .x8 .x11) (W 68719472240) (by change W 68719476336-W 4096=W 68719472240;decide)
  have h1167 := OpeningLinear.read o (s1167 e m) .x14 .x11 1888 8589934266 (basePtr e.index 13) (by decide) (by change W 68719472240+signExtend12 1888=wordAddress 8589934266;decide) h.stack1888
  have h1168 := OpeningLinear.read o (s1168 e m) .x12 .x14 416 (wordAt e.index 13 0) (m.mem (wordAt e.index 13 0)) (by have := word_room e.index 13 0 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 13 0 416 rfl) rfl
  have h1169 := OpeningLinear.read o (s1169 e m) .x11 .x14 424 (wordAt e.index 13 1) (m.mem (wordAt e.index 13 1)) (by have := word_room e.index 13 1 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 13 1 424 rfl) rfl
  have h1170 := OpeningLinear.read o (s1170 e m) .x17 .x14 432 (wordAt e.index 13 2) (m.mem (wordAt e.index 13 2)) (by have := word_room e.index 13 2 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 13 2 432 rfl) rfl
  have h1171 := OpeningLinear.read o (s1171 e m) .x15 .x14 440 (wordAt e.index 13 3) (m.mem (wordAt e.index 13 3)) (by have := word_room e.index 13 3 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 13 3 440 rfl) rfl
  have h1172 := OpeningLinear.register o (s1172 e m) .x16 (.andi .x13 63) (W ((e.cursor+2749)%64)) (OpeningCursor.offset (e.cursor+2749))
  have h1173 := OpeningLinear.register o (s1173 e m) .x13 (.srli .x13 3) (v1173 e m) rfl
  have h1174 := OpeningLinear.register o (s1174 e m) .x13 (.andi .x13 4088) (v1174 e m) rfl
  have h1175 := OpeningLinear.register o (s1175 e m) .x14 (.add .x13 .x25) (wordAddress (cell (e.cursor+2749))) (OpeningCursor.word_address (e.cursor+2749) (by have h₀ := e.room;unfold capacity at h₀;omega))
  have h1176 := OpeningLinear.register o (s1176 e m) .x15 (.and .x15 .x6) (m.mem (wordAt e.index 13 3) &&& W 536870911) rfl
  exact LeafModel.combine h1164 (LeafModel.combine h1165 (LeafModel.combine h1166 (LeafModel.combine h1167 (LeafModel.combine h1168 (LeafModel.combine h1169 (LeafModel.combine h1170 (LeafModel.combine h1171 (LeafModel.combine h1172 (LeafModel.combine h1173 (LeafModel.combine h1174 (LeafModel.combine h1175 (LeafModel.combine h1176 (LeafModel.empty _ _)))))))))))))

def input (e : Env) (m : Model) : OpeningRow13.I where
  root := e.cursor
  initial := s1177 e m
  word := fun k => if k=3 then m.mem (wordAt e.index 13 3) &&& W 536870911 else m.mem (wordAt e.index 13 k)
  room := by have := e.room;omega
  fits := by decide

theorem entry (e : Env) (m : Model) : OpeningRow13.entry (input e m)=s1177 e m := by
  refine OpeningRowEntry.equalModel (OpeningRow13.entry (input e m)) (s1177 e m) ?_ rfl
  intro r;cases r <;> rfl

def result (e : Env) (m : Model) := OpeningRow13.output (input e m)

theorem memory (e : Env) (m : Model) :
    (result e m).mem=CapWriter.lowMemory m.mem (e.cursor+2749) 13 (OpeningNodeStream.words m.mem e.index 13) := by
  exact OpeningRow13.memory (input e m)

theorem ready (e : Env) (m : Model) (stack : Stack e m.mem) : Ready12 e (result e m) := by
  constructor
  · exact (OpeningRow13.frame (input e m) .x0 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow13.frame (input e m) .x2 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow13.frame (input e m) .x8 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow13.frame (input e m) .x9 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow13.frame (input e m) .x18 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow13.frame (input e m) .x22 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow13.frame (input e m) .x25 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow13.frame (input e m) .x10 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow13.frame (input e m) .x7 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow13.frame (input e m) .x20 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow13.frame (input e m) .x31 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow13.frame (input e m) .x6 (by decide)).trans (by rw [entry];rfl)

theorem run (o : Oracle) (e : Env) (m : Model) (h : Ready13 e m) (stack : Stack e m.mem)
    (s : MachineState) (pc : s.pc=addr 1164) (fit : Fits s m) :
    ∃ t n, n≤90 ∧ CommitExact.Segment o OpeningStraight.image n s t ∧ t.pc=addr 1232 ∧ Fits t (result e m) := by
  have fit' : Fits s (start e m) := (start_eq e m h).symm ▸ fit
  obtain ⟨v,rv,pv,hv⟩ := OpeningLinear.block (prepare o e m stack) (i:=1164) (by decide) table s pc fit'
  obtain ⟨t,n,lim,rt,pt,ht⟩ := OpeningRow13.run o (input e m) v pv ((entry e m).symm ▸ hv)
  exact ⟨t,ops.length+n,by change 13+n≤90;omega,CommitExact.compose rv rt,pt,ht⟩

end CommitGolfCandidate.Reconstruction.OpeningRowStart13
