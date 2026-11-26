import CommitGolfCandidate.ReconstructedOpeningRow11
import CommitGolfCandidate.ReconstructedOpeningRowEntry

namespace CommitGolfCandidate.Reconstruction.OpeningRowStart11
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
theorem start_eq (e : Env) (m : Model) (h : Ready11 e m) : start e m=m := by
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

def s1301 (e : Env) (m : Model) := (start e m).set .x12 (W (e.cursor+3191))
def s1302 (e : Env) (m : Model) := (s1301 e m).set .x11 (W 4096)
def s1303 (e : Env) (m : Model) := (s1302 e m).set .x11 (W 68719472240)
def s1304 (e : Env) (m : Model) := (s1303 e m).set .x13 (basePtr e.index 11)
def s1305 (e : Env) (m : Model) := (s1304 e m).set .x14 (m.mem (wordAt e.index 11 0))
def s1306 (e : Env) (m : Model) := (s1305 e m).set .x11 (m.mem (wordAt e.index 11 1))
def s1307 (e : Env) (m : Model) := (s1306 e m).set .x15 (m.mem (wordAt e.index 11 2))
def s1308 (e : Env) (m : Model) := (s1307 e m).set .x17 (m.mem (wordAt e.index 11 3))
def s1309 (e : Env) (m : Model) := (s1308 e m).set .x13 (W ((e.cursor+3191)%64))
def v1309 (e : Env) (m : Model) : Word := (W (e.cursor+3191)) >>> (3 : Nat)
def s1310 (e : Env) (m : Model) := (s1309 e m).set .x12 (v1309 e m)
def v1310 (e : Env) (m : Model) : Word := (v1309 e m) &&& signExtend12 4088
def s1311 (e : Env) (m : Model) := (s1310 e m).set .x12 (v1310 e m)
def s1312 (e : Env) (m : Model) := (s1311 e m).set .x16 (wordAddress (cell (e.cursor+3191)))
def s1313 (e : Env) (m : Model) := (s1312 e m).set .x12 (m.mem (wordAt e.index 11 3) &&& W 536870911)

def ops : List Instr := [
  Expr.instr .x12 (.addi .x20 1140),
  Expr.instr .x11 (.lui 1),
  Expr.instr .x11 (.sub .x8 .x11),
  .LD .x13 .x11 1904,
  .LD .x14 .x13 352,
  .LD .x11 .x13 360,
  .LD .x15 .x13 368,
  .LD .x17 .x13 376,
  Expr.instr .x13 (.andi .x12 63),
  Expr.instr .x12 (.srli .x12 3),
  Expr.instr .x12 (.andi .x12 4088),
  Expr.instr .x16 (.add .x12 .x25),
  Expr.instr .x12 (.and .x17 .x6)]
theorem table : OpeningStraight.Listed 1300 ops := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem prepare (o : Oracle) (e : Env) (m : Model) (h : Stack e m.mem) : Contract o ops (start e m) (s1313 e m) := by
  have h1300 := OpeningLinear.register o (start e m) .x12 (.addi .x20 1140) (W (e.cursor+3191)) (OpeningRowOps.plusBit e.cursor 2051 1140 3191 1140 rfl rfl)
  have h1301 := OpeningLinear.register o (s1301 e m) .x11 (.lui 1) (W 4096) rfl
  have h1302 := OpeningLinear.register o (s1302 e m) .x11 (.sub .x8 .x11) (W 68719472240) (by change W 68719476336-W 4096=W 68719472240;decide)
  have h1303 := OpeningLinear.read o (s1303 e m) .x13 .x11 1904 8589934268 (basePtr e.index 11) (by decide) (by change W 68719472240+signExtend12 1904=wordAddress 8589934268;decide) h.stack1904
  have h1304 := OpeningLinear.read o (s1304 e m) .x14 .x13 352 (wordAt e.index 11 0) (m.mem (wordAt e.index 11 0)) (by have := word_room e.index 11 0 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 11 0 352 rfl) rfl
  have h1305 := OpeningLinear.read o (s1305 e m) .x11 .x13 360 (wordAt e.index 11 1) (m.mem (wordAt e.index 11 1)) (by have := word_room e.index 11 1 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 11 1 360 rfl) rfl
  have h1306 := OpeningLinear.read o (s1306 e m) .x15 .x13 368 (wordAt e.index 11 2) (m.mem (wordAt e.index 11 2)) (by have := word_room e.index 11 2 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 11 2 368 rfl) rfl
  have h1307 := OpeningLinear.read o (s1307 e m) .x17 .x13 376 (wordAt e.index 11 3) (m.mem (wordAt e.index 11 3)) (by have := word_room e.index 11 3 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 11 3 376 rfl) rfl
  have h1308 := OpeningLinear.register o (s1308 e m) .x13 (.andi .x12 63) (W ((e.cursor+3191)%64)) (OpeningCursor.offset (e.cursor+3191))
  have h1309 := OpeningLinear.register o (s1309 e m) .x12 (.srli .x12 3) (v1309 e m) rfl
  have h1310 := OpeningLinear.register o (s1310 e m) .x12 (.andi .x12 4088) (v1310 e m) rfl
  have h1311 := OpeningLinear.register o (s1311 e m) .x16 (.add .x12 .x25) (wordAddress (cell (e.cursor+3191))) (OpeningCursor.word_address (e.cursor+3191) (by have h₀ := e.room;unfold capacity at h₀;omega))
  have h1312 := OpeningLinear.register o (s1312 e m) .x12 (.and .x17 .x6) (m.mem (wordAt e.index 11 3) &&& W 536870911) rfl
  exact LeafModel.combine h1300 (LeafModel.combine h1301 (LeafModel.combine h1302 (LeafModel.combine h1303 (LeafModel.combine h1304 (LeafModel.combine h1305 (LeafModel.combine h1306 (LeafModel.combine h1307 (LeafModel.combine h1308 (LeafModel.combine h1309 (LeafModel.combine h1310 (LeafModel.combine h1311 (LeafModel.combine h1312 (LeafModel.empty _ _)))))))))))))

def input (e : Env) (m : Model) : OpeningRow11.I where
  root := e.cursor
  initial := s1313 e m
  word := fun k => if k=3 then m.mem (wordAt e.index 11 3) &&& W 536870911 else m.mem (wordAt e.index 11 k)
  room := by have := e.room;omega
  fits := by decide

theorem entry (e : Env) (m : Model) : OpeningRow11.entry (input e m)=s1313 e m := by
  refine OpeningRowEntry.equalModel (OpeningRow11.entry (input e m)) (s1313 e m) ?_ rfl
  intro r;cases r <;> rfl

def result (e : Env) (m : Model) := OpeningRow11.output (input e m)

theorem memory (e : Env) (m : Model) :
    (result e m).mem=CapWriter.lowMemory m.mem (e.cursor+3191) 11 (OpeningNodeStream.words m.mem e.index 11) := by
  exact OpeningRow11.memory (input e m)

theorem ready (e : Env) (m : Model) (stack : Stack e m.mem) : Ready10 e (result e m) := by
  constructor
  · exact (OpeningRow11.frame (input e m) .x0 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow11.frame (input e m) .x2 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow11.frame (input e m) .x8 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow11.frame (input e m) .x9 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow11.frame (input e m) .x18 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow11.frame (input e m) .x22 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow11.frame (input e m) .x25 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow11.frame (input e m) .x10 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow11.frame (input e m) .x7 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow11.frame (input e m) .x20 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow11.frame (input e m) .x31 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow11.frame (input e m) .x6 (by decide)).trans (by rw [entry];rfl)

theorem run (o : Oracle) (e : Env) (m : Model) (h : Ready11 e m) (stack : Stack e m.mem)
    (s : MachineState) (pc : s.pc=addr 1300) (fit : Fits s m) :
    ∃ t n, n≤90 ∧ CommitExact.Segment o OpeningStraight.image n s t ∧ t.pc=addr 1368 ∧ Fits t (result e m) := by
  have fit' : Fits s (start e m) := (start_eq e m h).symm ▸ fit
  obtain ⟨v,rv,pv,hv⟩ := OpeningLinear.block (prepare o e m stack) (i:=1300) (by decide) table s pc fit'
  obtain ⟨t,n,lim,rt,pt,ht⟩ := OpeningRow11.run o (input e m) v pv ((entry e m).symm ▸ hv)
  exact ⟨t,ops.length+n,by change 13+n≤90;omega,CommitExact.compose rv rt,pt,ht⟩

end CommitGolfCandidate.Reconstruction.OpeningRowStart11
