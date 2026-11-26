import CommitGolfCandidate.ReconstructedOpeningRow10
import CommitGolfCandidate.ReconstructedOpeningRowEntry

namespace CommitGolfCandidate.Reconstruction.OpeningRowStart10
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
theorem start_eq (e : Env) (m : Model) (h : Ready10 e m) : start e m=m := by
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

def s1369 (e : Env) (m : Model) := (start e m).set .x11 (W (e.cursor+3412))
def s1370 (e : Env) (m : Model) := (s1369 e m).set .x12 (W 4096)
def s1371 (e : Env) (m : Model) := (s1370 e m).set .x12 (W 68719472240)
def s1372 (e : Env) (m : Model) := (s1371 e m).set .x12 (basePtr e.index 10)
def s1373 (e : Env) (m : Model) := (s1372 e m).set .x15 (m.mem (wordAt e.index 10 0))
def s1374 (e : Env) (m : Model) := (s1373 e m).set .x14 (m.mem (wordAt e.index 10 1))
def s1375 (e : Env) (m : Model) := (s1374 e m).set .x13 (m.mem (wordAt e.index 10 2))
def s1376 (e : Env) (m : Model) := (s1375 e m).set .x17 (m.mem (wordAt e.index 10 3))
def s1377 (e : Env) (m : Model) := (s1376 e m).set .x12 (W ((e.cursor+3412)%64))
def v1377 (e : Env) (m : Model) : Word := (W (e.cursor+3412)) >>> (3 : Nat)
def s1378 (e : Env) (m : Model) := (s1377 e m).set .x11 (v1377 e m)
def v1378 (e : Env) (m : Model) : Word := (v1377 e m) &&& signExtend12 4088
def s1379 (e : Env) (m : Model) := (s1378 e m).set .x11 (v1378 e m)
def s1380 (e : Env) (m : Model) := (s1379 e m).set .x16 (wordAddress (cell (e.cursor+3412)))
def s1381 (e : Env) (m : Model) := (s1380 e m).set .x11 (m.mem (wordAt e.index 10 3) &&& W 536870911)

def ops : List Instr := [
  Expr.instr .x11 (.addi .x20 1361),
  Expr.instr .x12 (.lui 1),
  Expr.instr .x12 (.sub .x8 .x12),
  .LD .x12 .x12 1912,
  .LD .x15 .x12 320,
  .LD .x14 .x12 328,
  .LD .x13 .x12 336,
  .LD .x17 .x12 344,
  Expr.instr .x12 (.andi .x11 63),
  Expr.instr .x11 (.srli .x11 3),
  Expr.instr .x11 (.andi .x11 4088),
  Expr.instr .x16 (.add .x11 .x25),
  Expr.instr .x11 (.and .x17 .x6)]
theorem table : OpeningStraight.Listed 1368 ops := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem prepare (o : Oracle) (e : Env) (m : Model) (h : Stack e m.mem) : Contract o ops (start e m) (s1381 e m) := by
  have h1368 := OpeningLinear.register o (start e m) .x11 (.addi .x20 1361) (W (e.cursor+3412)) (OpeningRowOps.plusBit e.cursor 2051 1361 3412 1361 rfl rfl)
  have h1369 := OpeningLinear.register o (s1369 e m) .x12 (.lui 1) (W 4096) rfl
  have h1370 := OpeningLinear.register o (s1370 e m) .x12 (.sub .x8 .x12) (W 68719472240) (by change W 68719476336-W 4096=W 68719472240;decide)
  have h1371 := OpeningLinear.read o (s1371 e m) .x12 .x12 1912 8589934269 (basePtr e.index 10) (by decide) (by change W 68719472240+signExtend12 1912=wordAddress 8589934269;decide) h.stack1912
  have h1372 := OpeningLinear.read o (s1372 e m) .x15 .x12 320 (wordAt e.index 10 0) (m.mem (wordAt e.index 10 0)) (by have := word_room e.index 10 0 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 10 0 320 rfl) rfl
  have h1373 := OpeningLinear.read o (s1373 e m) .x14 .x12 328 (wordAt e.index 10 1) (m.mem (wordAt e.index 10 1)) (by have := word_room e.index 10 1 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 10 1 328 rfl) rfl
  have h1374 := OpeningLinear.read o (s1374 e m) .x13 .x12 336 (wordAt e.index 10 2) (m.mem (wordAt e.index 10 2)) (by have := word_room e.index 10 2 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 10 2 336 rfl) rfl
  have h1375 := OpeningLinear.read o (s1375 e m) .x17 .x12 344 (wordAt e.index 10 3) (m.mem (wordAt e.index 10 3)) (by have := word_room e.index 10 3 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 10 3 344 rfl) rfl
  have h1376 := OpeningLinear.register o (s1376 e m) .x12 (.andi .x11 63) (W ((e.cursor+3412)%64)) (OpeningCursor.offset (e.cursor+3412))
  have h1377 := OpeningLinear.register o (s1377 e m) .x11 (.srli .x11 3) (v1377 e m) rfl
  have h1378 := OpeningLinear.register o (s1378 e m) .x11 (.andi .x11 4088) (v1378 e m) rfl
  have h1379 := OpeningLinear.register o (s1379 e m) .x16 (.add .x11 .x25) (wordAddress (cell (e.cursor+3412))) (OpeningCursor.word_address (e.cursor+3412) (by have h₀ := e.room;unfold capacity at h₀;omega))
  have h1380 := OpeningLinear.register o (s1380 e m) .x11 (.and .x17 .x6) (m.mem (wordAt e.index 10 3) &&& W 536870911) rfl
  exact LeafModel.combine h1368 (LeafModel.combine h1369 (LeafModel.combine h1370 (LeafModel.combine h1371 (LeafModel.combine h1372 (LeafModel.combine h1373 (LeafModel.combine h1374 (LeafModel.combine h1375 (LeafModel.combine h1376 (LeafModel.combine h1377 (LeafModel.combine h1378 (LeafModel.combine h1379 (LeafModel.combine h1380 (LeafModel.empty _ _)))))))))))))

def input (e : Env) (m : Model) : OpeningRow10.I where
  root := e.cursor
  initial := s1381 e m
  word := fun k => if k=3 then m.mem (wordAt e.index 10 3) &&& W 536870911 else m.mem (wordAt e.index 10 k)
  room := by have := e.room;omega
  fits := by decide

theorem entry (e : Env) (m : Model) : OpeningRow10.entry (input e m)=s1381 e m := by
  refine OpeningRowEntry.equalModel (OpeningRow10.entry (input e m)) (s1381 e m) ?_ rfl
  intro r;cases r <;> rfl

def result (e : Env) (m : Model) := OpeningRow10.output (input e m)

theorem memory (e : Env) (m : Model) :
    (result e m).mem=CapWriter.lowMemory m.mem (e.cursor+3412) 10 (OpeningNodeStream.words m.mem e.index 10) := by
  exact OpeningRow10.memory (input e m)

theorem ready (e : Env) (m : Model) (stack : Stack e m.mem) : Ready9 e (result e m) := by
  constructor
  · exact (OpeningRow10.frame (input e m) .x0 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow10.frame (input e m) .x2 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow10.frame (input e m) .x8 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow10.frame (input e m) .x9 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow10.frame (input e m) .x18 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow10.frame (input e m) .x22 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow10.frame (input e m) .x25 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow10.frame (input e m) .x10 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow10.frame (input e m) .x7 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow10.frame (input e m) .x20 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow10.frame (input e m) .x31 (by decide)).trans (by rw [entry];rfl)
  · unfold result OpeningRow10.output;split <;> first | rfl | exact stack.stack1928 | (split <;> first | rfl | exact stack.stack1928)
  · unfold result OpeningRow10.output;split <;> first | rfl | exact stack.stack1928 | (split <;> first | rfl | exact stack.stack1928)

theorem run (o : Oracle) (e : Env) (m : Model) (h : Ready10 e m) (stack : Stack e m.mem)
    (s : MachineState) (pc : s.pc=addr 1368) (fit : Fits s m) :
    ∃ t n, n≤90 ∧ CommitExact.Segment o OpeningStraight.image n s t ∧ t.pc=addr 130 ∧ Fits t (result e m) := by
  have fit' : Fits s (start e m) := (start_eq e m h).symm ▸ fit
  obtain ⟨v,rv,pv,hv⟩ := OpeningLinear.block (prepare o e m stack) (i:=1368) (by decide) table s pc fit'
  obtain ⟨t,n,lim,rt,pt,ht⟩ := OpeningRow10.run o (input e m) v pv ((entry e m).symm ▸ hv)
  exact ⟨t,ops.length+n,by change 13+n≤90;omega,CommitExact.compose rv rt,pt,ht⟩

end CommitGolfCandidate.Reconstruction.OpeningRowStart10
