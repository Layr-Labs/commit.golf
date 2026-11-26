import CommitGolfCandidate.ReconstructedOpeningRow17
import CommitGolfCandidate.ReconstructedOpeningRowEntry

namespace CommitGolfCandidate.Reconstruction.OpeningRowStart17
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
  | .x20 => basePtr e.index 17
  | .x27 => basePtr e.index 16
  | .x15 => basePtr e.index 15
  | .x31 => W 2051
  | r => m.reg r,m.mem⟩
theorem start_eq (e : Env) (m : Model) (h : Ready17 e m) : start e m=m := by
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
  · exact h.r27.symm
  · rfl
  · rfl
  · rfl
  · exact h.r31.symm

def s892 (e : Env) (m : Model) := (start e m).set .x12 (W (e.cursor+1859))
def s893 (e : Env) (m : Model) := (s892 e m).set .x6 (m.mem (wordAt e.index 17 0))
def s894 (e : Env) (m : Model) := (s893 e m).set .x11 (m.mem (wordAt e.index 17 1))
def s895 (e : Env) (m : Model) := (s894 e m).set .x14 (m.mem (wordAt e.index 17 2))
def s896 (e : Env) (m : Model) := (s895 e m).set .x13 (m.mem (wordAt e.index 17 3))
def s897 (e : Env) (m : Model) := (s896 e m).set .x16 (W ((e.cursor+1859)%64))
def v897 (e : Env) (m : Model) : Word := (W (e.cursor+1859)) >>> (3 : Nat)
def s898 (e : Env) (m : Model) := (s897 e m).set .x12 (v897 e m)
def v898 (e : Env) (m : Model) : Word := (v897 e m) &&& signExtend12 4088
def s899 (e : Env) (m : Model) := (s898 e m).set .x12 (v898 e m)
def s900 (e : Env) (m : Model) := (s899 e m).set .x28 (wordAddress (cell (e.cursor+1859)))
def s901 (e : Env) (m : Model) := (s900 e m).set .x20 (W (e.cursor+2051))
def s902 (e : Env) (m : Model) := (s901 e m).set .x29 (W (e.cursor+1923))
def s903 (e : Env) (m : Model) := (s902 e m).set .x12 (W (e.cursor+1987))
def s904 (e : Env) (m : Model) := (s903 e m).set .x17 (W 4096)
def s905 (e : Env) (m : Model) := (s904 e m).set .x17 (W 68719472240)
def s906 (e : Env) (m : Model) := (s905 e m).set .x30 (W 1073741823)
def s907 (e : Env) (m : Model) := (s906 e m).set .x17 (m.mem (wordAt e.index 17 3) &&& W 1073741823)

def ops : List Instr := [
  Expr.instr .x12 (.addi .x7 1859),
  .LD .x6 .x20 544,
  .LD .x11 .x20 552,
  .LD .x14 .x20 560,
  .LD .x13 .x20 568,
  Expr.instr .x16 (.andi .x12 63),
  Expr.instr .x12 (.srli .x12 3),
  Expr.instr .x12 (.andi .x12 4088),
  Expr.instr .x28 (.add .x12 .x25),
  Expr.instr .x20 (.add .x7 .x31),
  Expr.instr .x29 (.addi .x7 1923),
  Expr.instr .x12 (.addi .x7 1987),
  Expr.instr .x17 (.lui 1),
  Expr.instr .x17 (.sub .x8 .x17),
  .LD .x30 .x17 1816,
  Expr.instr .x17 (.and .x13 .x30)]
theorem table : OpeningStraight.Listed 891 ops := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem prepare (o : Oracle) (e : Env) (m : Model) (h : Stack e m.mem) : Contract o ops (start e m) (s907 e m) := by
  have h891 := OpeningLinear.register o (start e m) .x12 (.addi .x7 1859) (W (e.cursor+1859)) (OpeningRowOps.plusBit e.cursor 0 1859 1859 1859 rfl rfl)
  have h892 := OpeningLinear.read o (s892 e m) .x6 .x20 544 (wordAt e.index 17 0) (m.mem (wordAt e.index 17 0)) (by have := word_room e.index 17 0 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 17 0 544 rfl) rfl
  have h893 := OpeningLinear.read o (s893 e m) .x11 .x20 552 (wordAt e.index 17 1) (m.mem (wordAt e.index 17 1)) (by have := word_room e.index 17 1 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 17 1 552 rfl) rfl
  have h894 := OpeningLinear.read o (s894 e m) .x14 .x20 560 (wordAt e.index 17 2) (m.mem (wordAt e.index 17 2)) (by have := word_room e.index 17 2 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 17 2 560 rfl) rfl
  have h895 := OpeningLinear.read o (s895 e m) .x13 .x20 568 (wordAt e.index 17 3) (m.mem (wordAt e.index 17 3)) (by have := word_room e.index 17 3 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset e.index 17 3 568 rfl) rfl
  have h896 := OpeningLinear.register o (s896 e m) .x16 (.andi .x12 63) (W ((e.cursor+1859)%64)) (OpeningCursor.offset (e.cursor+1859))
  have h897 := OpeningLinear.register o (s897 e m) .x12 (.srli .x12 3) (v897 e m) rfl
  have h898 := OpeningLinear.register o (s898 e m) .x12 (.andi .x12 4088) (v898 e m) rfl
  have h899 := OpeningLinear.register o (s899 e m) .x28 (.add .x12 .x25) (wordAddress (cell (e.cursor+1859))) (OpeningCursor.word_address (e.cursor+1859) (by have h₀ := e.room;unfold capacity at h₀;omega))
  have h900 := OpeningLinear.register o (s900 e m) .x20 (.add .x7 .x31) (W (e.cursor+2051)) (by change W (e.cursor+0) + W 2051 = W (e.cursor+2051);rw [←BitVec.ofNat_add,Nat.add_assoc])
  have h901 := OpeningLinear.register o (s901 e m) .x29 (.addi .x7 1923) (W (e.cursor+1923)) (OpeningRowOps.plusBit e.cursor 0 1923 1923 1923 rfl rfl)
  have h902 := OpeningLinear.register o (s902 e m) .x12 (.addi .x7 1987) (W (e.cursor+1987)) (OpeningRowOps.plusBit e.cursor 0 1987 1987 1987 rfl rfl)
  have h903 := OpeningLinear.register o (s903 e m) .x17 (.lui 1) (W 4096) rfl
  have h904 := OpeningLinear.register o (s904 e m) .x17 (.sub .x8 .x17) (W 68719472240) (by change W 68719476336-W 4096=W 68719472240;decide)
  have h905 := OpeningLinear.read o (s905 e m) .x30 .x17 1816 8589934257 (W 1073741823) (by decide) (by change W 68719472240+signExtend12 1816=wordAddress 8589934257;decide) h.stack1816
  have h906 := OpeningLinear.register o (s906 e m) .x17 (.and .x13 .x30) (m.mem (wordAt e.index 17 3) &&& W 1073741823) rfl
  exact LeafModel.combine h891 (LeafModel.combine h892 (LeafModel.combine h893 (LeafModel.combine h894 (LeafModel.combine h895 (LeafModel.combine h896 (LeafModel.combine h897 (LeafModel.combine h898 (LeafModel.combine h899 (LeafModel.combine h900 (LeafModel.combine h901 (LeafModel.combine h902 (LeafModel.combine h903 (LeafModel.combine h904 (LeafModel.combine h905 (LeafModel.combine h906 (LeafModel.empty _ _))))))))))))))))

def input (e : Env) (m : Model) : OpeningRow17.I where
  root := e.cursor
  initial := s907 e m
  word := fun k => if k=3 then m.mem (wordAt e.index 17 3) &&& W 1073741823 else m.mem (wordAt e.index 17 k)
  room := by have := e.room;omega
  fits := by decide

theorem entry (e : Env) (m : Model) : OpeningRow17.entry (input e m)=s907 e m := by
  refine OpeningRowEntry.equalModel (OpeningRow17.entry (input e m)) (s907 e m) ?_ rfl
  intro r;cases r <;> rfl

def result (e : Env) (m : Model) := OpeningRow17.output (input e m)

theorem memory (e : Env) (m : Model) :
    (result e m).mem=CapWriter.lowMemory m.mem (e.cursor+1859) 17 (OpeningNodeStream.words m.mem e.index 17) := by
  exact OpeningRow17.memory (input e m)

theorem ready (e : Env) (m : Model) (stack : Stack e m.mem) : Ready16 e (result e m) := by
  constructor
  · exact (OpeningRow17.frame (input e m) .x0 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow17.frame (input e m) .x2 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow17.frame (input e m) .x8 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow17.frame (input e m) .x9 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow17.frame (input e m) .x18 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow17.frame (input e m) .x22 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow17.frame (input e m) .x25 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow17.frame (input e m) .x10 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow17.frame (input e m) .x20 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow17.frame (input e m) .x27 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow17.frame (input e m) .x15 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow17.frame (input e m) .x31 (by decide)).trans (by rw [entry];rfl)
  · exact (OpeningRow17.frame (input e m) .x30 (by decide)).trans (by rw [entry];rfl)

theorem run (o : Oracle) (e : Env) (m : Model) (h : Ready17 e m) (stack : Stack e m.mem)
    (s : MachineState) (pc : s.pc=addr 891) (fit : Fits s m) :
    ∃ t n, n≤90 ∧ CommitExact.Segment o OpeningStraight.image n s t ∧ t.pc=addr 957 ∧ Fits t (result e m) := by
  have fit' : Fits s (start e m) := (start_eq e m h).symm ▸ fit
  obtain ⟨v,rv,pv,hv⟩ := OpeningLinear.block (prepare o e m stack) (i:=891) (by decide) table s pc fit'
  obtain ⟨t,n,lim,rt,pt,ht⟩ := OpeningRow17.run o (input e m) v pv ((entry e m).symm ▸ hv)
  exact ⟨t,ops.length+n,by change 16+n≤90;omega,CommitExact.compose rv rt,pt,ht⟩

end CommitGolfCandidate.Reconstruction.OpeningRowStart17
