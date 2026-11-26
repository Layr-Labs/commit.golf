import CommitGolfCandidate.S5InputBlock
import CommitGolfCandidate.S5ParentBuffers
namespace CommitGolfCandidate.S5Machine
open CommitGolfCandidate.Chained
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def tagStore (s : MachineState) (base : Nat) (tag : Word) := s.setMem (BitVec.ofNat 64 (base+64)) tag

theorem tagged_input (s : MachineState) (base : Nat) (l r : Output) (tag : Word)
    (aligned : base%8=0) (fit : base+96≤MEMORY_BYTES)
    (left : readBuffer s base 32=l) (right : readBuffer s (base+32) 32=r) (pad : readBuffer s (base+72) 24=0) :
    readBuffer (tagStore s base tag) base 96=parentBlock l r tag := by
  change base+96≤2^36 at fit
  have al : (base+64)%8=0:=by omega
  apply read_parent_block
  · exact (read_after_store_outside s (base+64) tag base 32 al (by omega) (by omega) (by omega)).trans left
  · exact (read_after_store_outside s (base+64) tag (base+32) 32 al (by omega) (by omega) (by omega)).trans right
  · rw [read_word _ _ al];exact MachineState.getMem_setMem_eq
  · exact (read_after_store_outside s (base+64) tag (base+72) 24 al (by omega) (by omega) (by omega)).trans pad

structure ScratchPad (s : MachineState) : Prop where
  second : readBuffer s (scratchBase+32) 32=0
  last : readBuffer s (scratchBase+72) 24=0

def unchanged (s t : MachineState) (a n : Nat) := ∀ b k,b+k≤MEMORY_BYTES → Apart b k a n →
  readBuffer t b k=readBuffer s b k

theorem tag_outside (s : MachineState) (base : Nat) (tag : Word) (al : base%8=0) (fit : base+96≤MEMORY_BYTES) :
    unchanged s (tagStore s base tag) (base+64) 8 := by
  intro b k bounds sep
  change base+96≤2^36 at fit;change b+k≤2^36 at bounds
  exact read_after_store_outside _ _ _ _ _ (by omega) (by omega) (by omega) sep

theorem store_outside (s : MachineState) (base : Nat) (v : Output) (fit : base+32≤MEMORY_BYTES) :
    unchanged s (writeBits s (BitVec.ofNat 64 base) v) base 32 := by
  intro b k bounds sep
  change base+32≤2^36 at fit;change b+k≤2^36 at bounds
  exact write_bits_read_outside s v base b k (by change base+32≤2^64;omega) (by omega) sep

theorem pads_after (s t : MachineState) (pad : ScratchPad s) (a k : Nat) (frame : unchanged s t a k)
    (one : Apart (scratchBase+32) 32 a k) (two : Apart (scratchBase+72) 24 a k) : ScratchPad t :=
  ⟨(frame _ _ (by decide) one).trans pad.second,(frame _ _ (by decide) two).trans pad.last⟩

theorem first_tag_value {s h p} (vals : gaps s) (base : Nat) (src : srcAddr h p=base)
    (cut : chained h) (valid : p<count h) :
    let l:=readBuffer s base 32
    let r:=readBuffer s (base+32) 32
    readBuffer (tagStore s base (tagWord h 0)) base 96=pack (.inl (workClass h,r ++ l)) := by
  subst base
  have pad:=gap_pad valid (by unfold chained at cut;omega)
  exact (tagged_input s (srcAddr h p) _ _ (tagWord h 0) (buffers valid).2.1 (buffers valid).1 rfl rfl
    (vals h.val p 2 pad).1).trans (parentBlock_first h _ _ cut)

theorem continuation_value (s : MachineState) (h : Height) (j : Fin 15) (v : Output)
    (pad : ScratchPad s) (current : readBuffer s scratchBase 32=v) :
    readBuffer (tagStore s scratchBase (tagWord h ⟨j.val+1,by omega⟩)) scratchBase 96=encodeNext h (j.val+1) v :=
  (tagged_input s scratchBase v 0 _ (by decide) (by decide) current pad.second pad.last).trans (parentBlock_next h j v)
end CommitGolfCandidate.S5Machine
