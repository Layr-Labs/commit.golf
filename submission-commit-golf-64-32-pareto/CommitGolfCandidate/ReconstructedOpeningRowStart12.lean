import CommitGolfCandidate.ReconstructedOpeningRow12
import CommitGolfCandidate.ReconstructedOpeningRowEntry

namespace CommitGolfCandidate.Reconstruction.OpeningRowStart12
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
theorem start_eq (e : Env) (m : Model) (h : Ready12 e m) : start e m=m := by
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

def s1233 (e : Env) (m : Model) := (start e m).set .x13 (W (e.cursor+2970))
def s1234 (e : Env) (m : Model) := (s1233 e m).set .x11 (W 4096)
def s1235 (e : Env) (m : Model) := (s1234 e m).set .x11 (W 68719472240)
def s1236 (e : Env) (m : Model) := (s1235 e m).set .x14 (basePtr e.index 12)
def s1237 (e : Env) (m : Model) := (s1236 e m).set .x12 (m.mem (wordAt e.index 12 0))
def s1238 (e : Env) (m : Model) := (s1237 e m).set .x11 (m.mem (wordAt e.index 12 1))
def s1239 (e : Env) (m : Model) := (s1238 e m).set .x16 (m.mem (wordAt e.index 12 2))
def s1240 (e : Env) (m : Model) := (s1239 e m).set .x17 (m.mem (wordAt e.index 12 3))
def s1241 (e : Env) (m : Model) := (s1240 e m).set .x15 (W ((e.cursor+2970)%64))
def v1241 (e : Env) (m : Model) : Word := (W (e.cursor+2970)) >>> (3 : Nat)
def s1242 (e : Env) (m : Model) := (s1241 e m).set .x13 (v1241 e m)
def v1242 (e : Env) (m : Model) : Word := (v1241 e m) &&& signExtend12 4088
def s1243 (e : Env) (m : Model) := (s1242 e m).set .x13 (v1242 e m)
def s1244 (e : Env) (m : Model) := (s1243 e m).set .x14 (wordAddress (cell (e.cursor+2970)))
def s1245 (e : Env) (m : Model) := (s1244 e m).set .x13 (m.mem (wordAt e.index 12 3) &&& W 536870911)

def ops : List Instr := [
  Expr.instr .x13 (.addi .x20 919),
  Expr.instr .x11 (.lui 1),
  Expr.instr .x11 (.sub .x8 .x11),
  .LD .x14 .x11 1896,
  .LD .x12 .x14 384,
  .LD .x11 .x14 392,
  .LD .x16 .x14 400,
  .LD .x17 .x14 408,
  Expr.instr .x15 (.andi .x13 63),
  Expr.instr .x13 (.srli .x13 3),
  Expr.instr .x13 (.andi .x13 4088),
  Expr.instr .x14 (.add .x13 .x25),
  Expr.instr .x13 (.and .x17 .x6)]
theorem table : OpeningStraight.Listed 1232 ops := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem prepare (o : Oracle) (e : Env) (m : Model) (h : Stack e m.mem) : Contract o ops (start e m) (s1245 e m) := by
  have h1232 := OpeningLinear.register o (start e m) .x13 (.addi .x20 919) (W (e.cursor+2970)) (OpeningRowOps.plusBit e.cursor 2051 919 2970 919 rfl rfl)
  have h1233 := OpeningLinear.register o (s1233 e m) .x11 (.lui 1) (W 4096) rfl
  have h1234 := OpeningLinear.register o (s1234 e m) .x11 (.sub .x8 .x11) (W 68719472240) (by change W 68719476336-W 4096=W 68719472240;decide)
  have h1235 := OpeningLinear.read o (s1235 e m) .x14 .x11 1896 8589934267 (basePtr e.index 12) (by decide) (by change W 68719472240+signExtend12 1896=wordAddress 8589934267;decide) h.stack1896
  have h1236 := OpeningLinear.read o (s1236 e m) .x12 .x14 384 (wordAt e.index 12 0) (m.mem (wordAt e.index 12 0)) (by have := word_room e.index 12 0 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 12 0 384 rfl) rfl
  have h1237 := OpeningLinear.read o (s1237 e m) .x11 .x14 392 (wordAt e.index 12 1) (m.mem (wordAt e.index 12 1)) (by have := word_room e.index 12 1 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 12 1 392 rfl) rfl
  have h1238 := OpeningLinear.read o (s1238 e m) .x16 .x14 400 (wordAt e.index 12 2) (m.mem (wordAt e.index 12 2)) (by have := word_room e.index 12 2 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 12 2 400 rfl) rfl
  have h1239 := OpeningLinear.read o (s1239 e m) .x17 .x14 408 (wordAt e.index 12 3) (m.mem (wordAt e.index 12 3)) (by have := word_room e.index 12 3 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 12 3 408 rfl) rfl
  have h1240 := OpeningLinear.register o (s1240 e m) .x15 (.andi .x13 63) (W ((e.cursor+2970)%64)) (OpeningCursor.offset (e.cursor+2970))
  have h1241 := OpeningLinear.register o (s1241 e m) .x13 (.srli .x13 3) (v1241 e m) rfl
  have h1242 := OpeningLinear.register o (s1242 e m) .x13 (.andi .x13 4088) (v1242 e m) rfl
  have h1243 := OpeningLinear.register o (s1243 e m) .x14 (.add .x13 .x25) (wordAddress (cell (e.cursor+2970))) (OpeningCursor.word_address (e.cursor+2970) (by have h₀ := e.room;unfold capacity at h₀;omega))
  have h1244 := OpeningLinear.register o (s1244 e m) .x13 (.and .x17 .x6) (m.mem (wordAt e.index 12 3) &&& W 536870911) rfl
  exact LeafModel.combine h1232 (LeafModel.combine h1233 (LeafModel.combine h1234 (LeafModel.combine h1235 (LeafModel.combine h1236 (LeafModel.combine h1237 (LeafModel.combine h1238 (LeafModel.combine h1239 (LeafModel.combine h1240 (LeafModel.combine h1241 (LeafModel.combine h1242 (LeafModel.combine h1243 (LeafModel.combine h1244 (LeafModel.empty _ _)))))))))))))

def input (e : Env) (m : Model) : OpeningRow12.I where
  root := e.cursor
  initial := s1245 e m
  word := fun k => if k=3 then m.mem (wordAt e.index 12 3) &&& W 536870911 else m.mem (wordAt e.index 12 k)
  room := by have := e.room;omega
  fits := by decide

theorem entry (e : Env) (m : Model) : OpeningRow12.entry (input e m)=s1245 e m := by
  refine OpeningRowEntry.equalModel (OpeningRow12.entry (input e m)) (s1245 e m) ?_ rfl
  intro r;cases r <;> rfl

def result (e : Env) (m : Model) := OpeningRow12.output (input e m)

theorem memory (e : Env) (m : Model) :
    (result e m).mem=CapWriter.lowMemory m.mem (e.cursor+2970) 12 (OpeningNodeStream.words m.mem e.index 12) := by
  exact OpeningRow12.memory (input e m)

theorem ready (e : Env) (m : Model) (stack : Stack e m.mem) : Ready11 e (result e m) := by
  constructor
  · exact (OpeningRow12.frame (input e m) .x0 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow12.frame (input e m) .x2 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow12.frame (input e m) .x8 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow12.frame (input e m) .x9 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow12.frame (input e m) .x18 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow12.frame (input e m) .x22 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow12.frame (input e m) .x25 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow12.frame (input e m) .x10 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow12.frame (input e m) .x7 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow12.frame (input e m) .x20 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow12.frame (input e m) .x31 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow12.frame (input e m) .x6 (by decide)).trans (by rw [entry];rfl)

theorem run (o : Oracle) (e : Env) (m : Model) (h : Ready12 e m) (stack : Stack e m.mem)
    (s : MachineState) (pc : s.pc=addr 1232) (fit : Fits s m) :
    ∃ t n, n≤90 ∧ CommitExact.Segment o OpeningStraight.image n s t ∧ t.pc=addr 1300 ∧ Fits t (result e m) := by
  have fit' : Fits s (start e m) := (start_eq e m h).symm ▸ fit
  obtain ⟨v,rv,pv,hv⟩ := OpeningLinear.block (prepare o e m stack) (i:=1232) (by decide) table s pc fit'
  obtain ⟨t,n,lim,rt,pt,ht⟩ := OpeningRow12.run o (input e m) v pv ((entry e m).symm ▸ hv)
  exact ⟨t,ops.length+n,by change 13+n≤90;omega,CommitExact.compose rv rt,pt,ht⟩

end CommitGolfCandidate.Reconstruction.OpeningRowStart12
