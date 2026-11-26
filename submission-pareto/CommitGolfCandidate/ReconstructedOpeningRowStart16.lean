import CommitGolfCandidate.ReconstructedOpeningRow16
import CommitGolfCandidate.ReconstructedOpeningRowEntry

namespace CommitGolfCandidate.Reconstruction.OpeningRowStart16
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
  | .x20 => W (e.cursor+2051)
  | .x27 => basePtr e.index 16
  | .x15 => basePtr e.index 15
  | .x31 => W 2051
  | .x30 => W 1073741823
  | r => m.reg r,m.mem⟩
theorem start_eq (e : Env) (m : Model) (h : Ready16 e m) : start e m=m := by
  refine OpeningRowEntry.equalModel (start e m) m ?_ rfl
  intro r;cases r
  · exact h.r0.symm
  · rfl
  · exact h.r2.symm
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
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
  · exact h.r27.symm
  · rfl
  · rfl
  · exact h.r30.symm
  · exact h.r31.symm

def s958 (e : Env) (m : Model) := (start e m).set .x13 (W (e.cursor+2081))
def s959 (e : Env) (m : Model) := (s958 e m).set .x12 (m.mem (wordAt e.index 16 0))
def s960 (e : Env) (m : Model) := (s959 e m).set .x11 (m.mem (wordAt e.index 16 1))
def s961 (e : Env) (m : Model) := (s960 e m).set .x6 (m.mem (wordAt e.index 16 2))
def s962 (e : Env) (m : Model) := (s961 e m).set .x17 (m.mem (wordAt e.index 16 3))
def s963 (e : Env) (m : Model) := (s962 e m).set .x16 (W ((e.cursor+2081)%64))
def v963 (e : Env) (m : Model) : Word := (W (e.cursor+2081)) >>> (3 : Nat)
def s964 (e : Env) (m : Model) := (s963 e m).set .x13 (v963 e m)
def v964 (e : Env) (m : Model) : Word := (v963 e m) &&& signExtend12 4088
def s965 (e : Env) (m : Model) := (s964 e m).set .x13 (v964 e m)
def s966 (e : Env) (m : Model) := (s965 e m).set .x14 (wordAddress (cell (e.cursor+2081)))
def s967 (e : Env) (m : Model) := (s966 e m).set .x17 (m.mem (wordAt e.index 16 3) &&& W 1073741823)
def s968 (e : Env) (m : Model) := (s967 e m).set .x7 (W 36)

def ops : List Instr := [
  Expr.instr .x13 (.addi .x20 30),
  .LD .x12 .x27 512,
  .LD .x11 .x27 520,
  .LD .x6 .x27 528,
  .LD .x17 .x27 536,
  Expr.instr .x16 (.andi .x13 63),
  Expr.instr .x13 (.srli .x13 3),
  Expr.instr .x13 (.andi .x13 4088),
  Expr.instr .x14 (.add .x13 .x25),
  Expr.instr .x17 (.and .x17 .x30),
  Expr.instr .x7 (.addi .x0 36)]
theorem table : OpeningStraight.Listed 957 ops := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem prepare (o : Oracle) (e : Env) (m : Model) (h : Stack e m.mem) : Contract o ops (start e m) (s968 e m) := by
  have h957 := OpeningLinear.register o (start e m) .x13 (.addi .x20 30) (W (e.cursor+2081)) (OpeningRowOps.plusBit e.cursor 2051 30 2081 30 rfl rfl)
  have h958 := OpeningLinear.read o (s958 e m) .x12 .x27 512 (wordAt e.index 16 0) (m.mem (wordAt e.index 16 0)) (by have := word_room e.index 16 0 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 16 0 512 rfl) rfl
  have h959 := OpeningLinear.read o (s959 e m) .x11 .x27 520 (wordAt e.index 16 1) (m.mem (wordAt e.index 16 1)) (by have := word_room e.index 16 1 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 16 1 520 rfl) rfl
  have h960 := OpeningLinear.read o (s960 e m) .x6 .x27 528 (wordAt e.index 16 2) (m.mem (wordAt e.index 16 2)) (by have := word_room e.index 16 2 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 16 2 528 rfl) rfl
  have h961 := OpeningLinear.read o (s961 e m) .x17 .x27 536 (wordAt e.index 16 3) (m.mem (wordAt e.index 16 3)) (by have := word_room e.index 16 3 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 16 3 536 rfl) rfl
  have h962 := OpeningLinear.register o (s962 e m) .x16 (.andi .x13 63) (W ((e.cursor+2081)%64)) (OpeningCursor.offset (e.cursor+2081))
  have h963 := OpeningLinear.register o (s963 e m) .x13 (.srli .x13 3) (v963 e m) rfl
  have h964 := OpeningLinear.register o (s964 e m) .x13 (.andi .x13 4088) (v964 e m) rfl
  have h965 := OpeningLinear.register o (s965 e m) .x14 (.add .x13 .x25) (wordAddress (cell (e.cursor+2081))) (OpeningCursor.word_address (e.cursor+2081) (by have h₀ := e.room;unfold capacity at h₀;omega))
  have h966 := OpeningLinear.register o (s966 e m) .x17 (.and .x17 .x30) (m.mem (wordAt e.index 16 3) &&& W 1073741823) rfl
  have h967 := OpeningLinear.register o (s967 e m) .x7 (.addi .x0 36) (W 36) rfl
  exact LeafModel.combine h957 (LeafModel.combine h958 (LeafModel.combine h959 (LeafModel.combine h960 (LeafModel.combine h961 (LeafModel.combine h962 (LeafModel.combine h963 (LeafModel.combine h964 (LeafModel.combine h965 (LeafModel.combine h966 (LeafModel.combine h967 (LeafModel.empty _ _)))))))))))

def input (e : Env) (m : Model) : OpeningRow16.I where
  root := e.cursor
  initial := s968 e m
  word := fun k => if k=3 then m.mem (wordAt e.index 16 3) &&& W 1073741823 else m.mem (wordAt e.index 16 k)
  room := by have := e.room;omega
  fits := by decide

theorem entry (e : Env) (m : Model) : OpeningRow16.entry (input e m)=s968 e m := by
  refine OpeningRowEntry.equalModel (OpeningRow16.entry (input e m)) (s968 e m) ?_ rfl
  intro r;cases r <;> rfl

def result (e : Env) (m : Model) := OpeningRow16.output (input e m)

theorem memory (e : Env) (m : Model) :
    (result e m).mem=CapWriter.lowMemory m.mem (e.cursor+2081) 16 (OpeningNodeStream.words m.mem e.index 16) := by
  exact OpeningRow16.memory (input e m)

theorem ready (e : Env) (m : Model) (stack : Stack e m.mem) : Ready15 e (result e m) := by
  constructor
  · exact (OpeningRow16.frame (input e m) .x0 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow16.frame (input e m) .x2 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow16.frame (input e m) .x8 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow16.frame (input e m) .x9 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow16.frame (input e m) .x18 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow16.frame (input e m) .x22 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow16.frame (input e m) .x25 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow16.frame (input e m) .x10 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow16.frame (input e m) .x7 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow16.frame (input e m) .x20 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow16.frame (input e m) .x15 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow16.frame (input e m) .x31 (by decide)).trans (by rw [entry];rfl)

theorem run (o : Oracle) (e : Env) (m : Model) (h : Ready16 e m) (stack : Stack e m.mem)
    (s : MachineState) (pc : s.pc=addr 957) (fit : Fits s m) :
    ∃ t n, n≤90 ∧ CommitExact.Segment o OpeningStraight.image n s t ∧ t.pc=addr 1024 ∧ Fits t (result e m) := by
  have fit' : Fits s (start e m) := (start_eq e m h).symm ▸ fit
  obtain ⟨v,rv,pv,hv⟩ := OpeningLinear.block (prepare o e m stack) (i:=957) (by decide) table s pc fit'
  obtain ⟨t,n,lim,rt,pt,ht⟩ := OpeningRow16.run o (input e m) v pv ((entry e m).symm ▸ hv)
  exact ⟨t,ops.length+n,by change 11+n≤90;omega,CommitExact.compose rv rt,pt,ht⟩

end CommitGolfCandidate.Reconstruction.OpeningRowStart16
