import CommitGolfCandidate.ReconstructedOpeningRow24
import CommitGolfCandidate.ReconstructedOpeningRowEntry

namespace CommitGolfCandidate.Reconstruction.OpeningRowStart24
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
theorem start_eq (e : Env) (m : Model) (h : Ready24 e m) : start e m=m := by
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

def s417 (e : Env) (m : Model) := (start e m).set .x11 (W (e.cursor+222))
def v417 (e : Env) (m : Model) : Word := (W (2^24+e.index.val)) ^^^ signExtend12 1
def s418 (e : Env) (m : Model) := (s417 e m).set .x12 (v417 e m)
def v418 (e : Env) (m : Model) : Word := (v417 e m) <<< (5 : Nat)
def s419 (e : Env) (m : Model) := (s418 e m).set .x12 (v418 e m)
def s420 (e : Env) (m : Model) := (s419 e m).set .x13 (basePtr e.index 24)
def s421 (e : Env) (m : Model) := (s420 e m).set .x29 (m.mem (wordAt e.index 24 0))
def s422 (e : Env) (m : Model) := (s421 e m).set .x12 (m.mem (wordAt e.index 24 1))
def s423 (e : Env) (m : Model) := (s422 e m).set .x14 (m.mem (wordAt e.index 24 2))
def s424 (e : Env) (m : Model) := (s423 e m).set .x13 (m.mem (wordAt e.index 24 3))
def s425 (e : Env) (m : Model) := (s424 e m).set .x16 (W ((e.cursor+222)%64))
def v425 (e : Env) (m : Model) : Word := (W (e.cursor+222)) >>> (3 : Nat)
def s426 (e : Env) (m : Model) := (s425 e m).set .x11 (v425 e m)
def v426 (e : Env) (m : Model) : Word := (v425 e m) &&& signExtend12 4088
def s427 (e : Env) (m : Model) := (s426 e m).set .x11 (v426 e m)
def s428 (e : Env) (m : Model) := (s427 e m).set .x31 (wordAddress (cell (e.cursor+222)))
def s429 (e : Env) (m : Model) := (s428 e m).set .x30 (W (e.cursor+286))
def s430 (e : Env) (m : Model) := (s429 e m).set .x6 (W (e.cursor+350))
def s431 (e : Env) (m : Model) := (s430 e m).set .x11 (W (e.cursor+414))
def s432 (e : Env) (m : Model) := (s431 e m).set .x17 (W 4096)
def s433 (e : Env) (m : Model) := (s432 e m).set .x17 (W 68719472240)
def s434 (e : Env) (m : Model) := (s433 e m).set .x17 (W 281474976710655)
def s435 (e : Env) (m : Model) := (s434 e m).set .x17 (m.mem (wordAt e.index 24 3) &&& W 281474976710655)

def ops : List Instr := [
  Expr.instr .x11 (.addi .x7 222),
  Expr.instr .x12 (.xori .x10 1),
  Expr.instr .x12 (.slli .x12 5),
  Expr.instr .x13 (.add .x12 .x22),
  .LD .x29 .x13 768,
  .LD .x12 .x13 776,
  .LD .x14 .x13 784,
  .LD .x13 .x13 792,
  Expr.instr .x16 (.andi .x11 63),
  Expr.instr .x11 (.srli .x11 3),
  Expr.instr .x11 (.andi .x11 4088),
  Expr.instr .x31 (.add .x11 .x25),
  Expr.instr .x30 (.addi .x7 286),
  Expr.instr .x6 (.addi .x7 350),
  Expr.instr .x11 (.addi .x7 414),
  Expr.instr .x17 (.lui 1),
  Expr.instr .x17 (.sub .x8 .x17),
  .LD .x17 .x17 1856,
  Expr.instr .x17 (.and .x13 .x17)]
theorem table : OpeningStraight.Listed 416 ops := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem prepare (o : Oracle) (e : Env) (m : Model) (h : Stack e m.mem) : Contract o ops (start e m) (s435 e m) := by
  have h416 := OpeningLinear.register o (start e m) .x11 (.addi .x7 222) (W (e.cursor+222)) (OpeningRowOps.plusBit e.cursor 0 222 222 222 rfl rfl)
  have h417 := OpeningLinear.register o (s417 e m) .x12 (.xori .x10 1) (v417 e m) rfl
  have h418 := OpeningLinear.register o (s418 e m) .x12 (.slli .x12 5) (v418 e m) rfl
  have h419 := OpeningLinear.register o (s419 e m) .x13 (.add .x12 .x22) (basePtr e.index 24) (OpeningLowerAddress.last e.index)
  have h420 := OpeningLinear.read o (s420 e m) .x29 .x13 768 (wordAt e.index 24 0) (m.mem (wordAt e.index 24 0)) (by have := word_room e.index 24 0 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 24 0 768 rfl) rfl
  have h421 := OpeningLinear.read o (s421 e m) .x12 .x13 776 (wordAt e.index 24 1) (m.mem (wordAt e.index 24 1)) (by have := word_room e.index 24 1 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 24 1 776 rfl) rfl
  have h422 := OpeningLinear.read o (s422 e m) .x14 .x13 784 (wordAt e.index 24 2) (m.mem (wordAt e.index 24 2)) (by have := word_room e.index 24 2 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 24 2 784 rfl) rfl
  have h423 := OpeningLinear.read o (s423 e m) .x13 .x13 792 (wordAt e.index 24 3) (m.mem (wordAt e.index 24 3)) (by have := word_room e.index 24 3 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 24 3 792 rfl) rfl
  have h424 := OpeningLinear.register o (s424 e m) .x16 (.andi .x11 63) (W ((e.cursor+222)%64)) (OpeningCursor.offset (e.cursor+222))
  have h425 := OpeningLinear.register o (s425 e m) .x11 (.srli .x11 3) (v425 e m) rfl
  have h426 := OpeningLinear.register o (s426 e m) .x11 (.andi .x11 4088) (v426 e m) rfl
  have h427 := OpeningLinear.register o (s427 e m) .x31 (.add .x11 .x25) (wordAddress (cell (e.cursor+222))) (OpeningCursor.word_address (e.cursor+222) (by have h₀ := e.room;unfold capacity at h₀;omega))
  have h428 := OpeningLinear.register o (s428 e m) .x30 (.addi .x7 286) (W (e.cursor+286)) (OpeningRowOps.plusBit e.cursor 0 286 286 286 rfl rfl)
  have h429 := OpeningLinear.register o (s429 e m) .x6 (.addi .x7 350) (W (e.cursor+350)) (OpeningRowOps.plusBit e.cursor 0 350 350 350 rfl rfl)
  have h430 := OpeningLinear.register o (s430 e m) .x11 (.addi .x7 414) (W (e.cursor+414)) (OpeningRowOps.plusBit e.cursor 0 414 414 414 rfl rfl)
  have h431 := OpeningLinear.register o (s431 e m) .x17 (.lui 1) (W 4096) rfl
  have h432 := OpeningLinear.register o (s432 e m) .x17 (.sub .x8 .x17) (W 68719472240) (by change W 68719476336-W 4096=W 68719472240;decide)
  have h433 := OpeningLinear.read o (s433 e m) .x17 .x17 1856 8589934262 (W 281474976710655) (by decide) (by change W 68719472240+signExtend12 1856=wordAddress 8589934262;decide) h.stack1856
  have h434 := OpeningLinear.register o (s434 e m) .x17 (.and .x13 .x17) (m.mem (wordAt e.index 24 3) &&& W 281474976710655) rfl
  exact LeafModel.combine h416 (LeafModel.combine h417 (LeafModel.combine h418 (LeafModel.combine h419 (LeafModel.combine h420 (LeafModel.combine h421 (LeafModel.combine h422 (LeafModel.combine h423 (LeafModel.combine h424 (LeafModel.combine h425 (LeafModel.combine h426 (LeafModel.combine h427 (LeafModel.combine h428 (LeafModel.combine h429 (LeafModel.combine h430 (LeafModel.combine h431 (LeafModel.combine h432 (LeafModel.combine h433 (LeafModel.combine h434 (LeafModel.empty _ _)))))))))))))))))))

def input (e : Env) (m : Model) : OpeningRow24.I where
  root := e.cursor
  initial := s435 e m
  word := fun k => if k=3 then m.mem (wordAt e.index 24 3) &&& W 281474976710655 else m.mem (wordAt e.index 24 k)
  room := by have := e.room;omega
  fits := by decide

theorem entry (e : Env) (m : Model) : OpeningRow24.entry (input e m)=s435 e m := by
  refine OpeningRowEntry.equalModel (OpeningRow24.entry (input e m)) (s435 e m) ?_ rfl
  intro r;cases r <;> rfl

def result (e : Env) (m : Model) := OpeningRow24.output (input e m)

theorem memory (e : Env) (m : Model) :
    (result e m).mem=CapWriter.lowMemory m.mem (e.cursor+222) 24 (OpeningNodeStream.words m.mem e.index 24) := by
  exact OpeningRow24.memory (input e m)

theorem ready (e : Env) (m : Model) (stack : Stack e m.mem) : Ready23 e (result e m) := by
  constructor
  · exact (OpeningRow24.frame (input e m) .x0 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow24.frame (input e m) .x2 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow24.frame (input e m) .x8 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow24.frame (input e m) .x9 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow24.frame (input e m) .x18 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow24.frame (input e m) .x22 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow24.frame (input e m) .x25 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow24.frame (input e m) .x10 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow24.frame (input e m) .x7 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow24.frame (input e m) .x28 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow24.frame (input e m) .x26 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow24.frame (input e m) .x20 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow24.frame (input e m) .x27 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow24.frame (input e m) .x15 (by decide)).trans (by rw [entry];rfl)

theorem run (o : Oracle) (e : Env) (m : Model) (h : Ready24 e m) (stack : Stack e m.mem)
    (s : MachineState) (pc : s.pc=addr 416) (fit : Fits s m) :
    ∃ t n, n≤90 ∧ CommitExact.Segment o OpeningStraight.image n s t ∧ t.pc=addr 485 ∧ Fits t (result e m) := by
  have fit' : Fits s (start e m) := (start_eq e m h).symm ▸ fit
  obtain ⟨v,rv,pv,hv⟩ := OpeningLinear.block (prepare o e m stack) (i:=416) (by decide) table s pc fit'
  obtain ⟨t,n,lim,rt,pt,ht⟩ := OpeningRow24.run o (input e m) v pv ((entry e m).symm ▸ hv)
  exact ⟨t,ops.length+n,by change 19+n≤90;omega,CommitExact.compose rv rt,pt,ht⟩

end CommitGolfCandidate.Reconstruction.OpeningRowStart24
