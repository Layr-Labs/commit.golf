import CommitGolfCandidate.TwoPermutationWideLeafExec

namespace TwoPermutationPrototype.RV64.WideLeaves
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
structure LeafReady (s : MachineState) (slot : Fin 256) (start index dst salts : Nat) : Prop where
  source : s.getReg .x10 = wordAddress (start+4)
  destination : s.getReg .x20 + BitVec.ofNat 64 (32*(slot.val%64)) = wordAddress dst
  nonces : s.getReg .x22 = wordAddress salts
  tag : firstTag index = wordAddress start
  sourceBound : start + 37 ≤ 2 ^ 33
  heapBound : dst + 25 ≤ 2 ^ 33
  nonceBound : salts + 256 ≤ 2 ^ 33
  separate : start + 37 ≤ salts
  selector : s.getReg .x5 = 0
  size : s.getReg .x11 = 200
  primitive : s.getReg .x13 = 1
  front : 8 ≤ start

def preparedA (s : MachineState) (slot : Fin 256) := (firstInstructions slot).foldl execInstrBr s
def repliedA (s : MachineState) (slot : Fin 256) (start : Nat) (answer : BitVec 1600) :=
  writeBits (preparedA s slot) (wordAddress (start-8)) answer
def preparedB (s : MachineState) (slot : Fin 256) (start : Nat) (a : BitVec 1600) :=
  (secondInstructions slot).foldl execInstrBr (repliedA s slot start a)
def repliedB (s : MachineState) (slot : Fin 256) (start dst : Nat) (a b : BitVec 1600) :=
  writeBits (preparedB s slot start a) (wordAddress dst) b
def finishedLeaf (s : MachineState) (slot : Fin 256) (start dst : Nat) (a b : BitVec 1600) :=
  execInstrBr (repliedB s slot start dst a b) (.ADDI .x10 .x10 192)

theorem after_a_input_cursor (s : MachineState) (slot : Fin 256) (start index dst salts : Nat)
    (ready : LeafReady s slot start index dst salts) (a : BitVec 1600) :
    (repliedA s slot start a).getReg .x10 = wordAddress (start+4) := by
  rw [repliedA,CommitGolfCandidate.writeBits_register]
  exact (first_execution s slot).2.1.trans ready.source

theorem after_a_nonce_reg (s : MachineState) (slot : Fin 256) (start : Nat) (a : BitVec 1600) :
    (repliedA s slot start a).getReg .x22=s.getReg .x22 := by
  rw [repliedA,CommitGolfCandidate.writeBits_register]; rfl

theorem after_a_memory (s : MachineState) (slot : Fin 256) (start index dst salts w : Nat)
    (ready : LeafReady s slot start index dst salts) (a : BitVec 1600) (bound : w<2^33) :
    memoryView (repliedA s slot start a) w = Overlap.afterFirst (memoryView s) (start-8) (replyWords a) w := by
  have low := ready.front
  have top := ready.sourceBound
  let r := start-8
  have src : s.getReg .x10=wordAddress (r+12) := by
    rw [ready.source];congr 1;dsimp [r];omega
  change memoryView (writeBits (preparedA s slot) (wordAddress r) a) w=_
  rw [permutation_write_memory _ _ _ _ (by dsimp [r];omega) bound]
  rw [←Overlap.first_reply_over_zero (memoryView s) r (replyWords a) w]
  by_cases covers : r ≤ w ∧ w<r+25
  · simp only [writeWindow,dif_pos covers]
  · simp only [writeWindow,dif_neg covers]
    exact first_memory_word s slot r w src (by dsimp [r];omega) (by omega)

theorem nonce_after_a (s : MachineState) (slot : Fin 256) (start index dst salts : Nat)
    (ready : LeafReady s slot start index dst salts) (a : BitVec 1600) :
    nonceWords (repliedA s slot start a) slot = nonceWords s slot := by
  rw [at_salt _ _ salts ((after_a_nonce_reg ..).trans ready.nonces),at_salt s slot salts ready.nonces]
  funext j
  have jb := j.isLt
  have sep := ready.separate
  have top := ready.nonceBound
  let w := salts + 2*(slot.val%128)+j.val
  change memoryView (repliedA s slot start a) w = memoryView s w
  rw [after_a_memory s slot start index dst salts w ready a (by dsimp [w];omega)]
  simp only [Overlap.afterFirst,writeWindow,dif_neg (by dsimp [w];omega : ¬(start-8≤w ∧ w<start-8+25))]

theorem before_b_memory (s : MachineState) (slot : Fin 256) (start index dst salts w : Nat)
    (ready : LeafReady s slot start index dst salts) (a : BitVec 1600) (bound : w<2^33) :
    memoryView (preparedB s slot start a) w =
      Overlap.beforeSecond (memoryView s) (start-8) index (nonceWords s slot) (replyWords a) w := by
  let r := start-8
  let mid := repliedA s slot start a
  have low := ready.front
  have sep := ready.separate
  have s12 : r+12=start+4 := by dsimp [r];omega
  have s20 : r+20=start+12 := by dsimp [r];omega
  have tag : wordAddress (r+20)=secondTag index := by
    rw [s20,wordAddress_add,secondTag,ready.tag];rfl
  have mem := congrFun (second_execution mid slot).1 (wordAddress w)
  change memoryView (preparedB s slot start a) w=memoryView (secondMemory mid slot) w at mem
  rw [mem,second_memory_word mid slot r salts w
    (s12.symm ▸ after_a_input_cursor s slot start index dst salts ready a)
    ((after_a_nonce_reg ..).trans ready.nonces) (by dsimp [r];omega) ready.nonceBound (by omega)]
  have ns := nonce_after_a s slot start index dst salts ready a
  change nonceWords mid slot = _ at ns
  rw [ns,tag]
  unfold Overlap.beforeSecond
  change writeWord (writeWord (writeWord (memoryView mid) (r+20) _) (r+25) _) (r+26) _ w = _
  simp only [writeWord]
  split <;> first | rfl | skip
  split <;> first | rfl | skip
  split <;> first | rfl | skip
  exact after_a_memory s slot start index dst salts w ready a bound

theorem after_b_input (s : MachineState) (slot : Fin 256) (start index dst salts : Nat)
    (ready : LeafReady s slot start index dst salts) (a : BitVec 1600) :
    window (memoryView (preparedB s slot start a)) (start+12) =
      Overlap.secondInput index (nonceWords s slot) (replyWords a) (window (memoryView s) (start+5)) := by
  let r := start-8
  have low := ready.front
  have limit := ready.sourceBound
  rw [show start+12=r+20 by dsimp [r];omega, show start+5=r+13 by dsimp [r];omega,←Overlap.second_window]
  funext j
  exact before_b_memory s slot start index dst salts (r+20+j.val) ready a
    (by dsimp [r];have := j.isLt;omega)

theorem finished_leaf_memory (s : MachineState) (slot : Fin 256) (start index dst salts w : Nat)
    (ready : LeafReady s slot start index dst salts) (a b : BitVec 1600) (bounded : w<2^33) :
    memoryView (finishedLeaf s slot start dst a b) w =
      Overlap.resultMemory (memoryView s) (start-8) index dst (nonceWords s slot) (replyWords a) (replyWords b) w := by
  change memoryView (writeBits (preparedB s slot start a) (wordAddress dst) b) w = _
  rw [permutation_write_memory _ _ _ _ ready.heapBound bounded]
  unfold Overlap.resultMemory
  by_cases covered : dst≤w ∧ w<dst+25
  · simp only [writeWindow,dif_pos covered]
  · simp only [writeWindow,dif_neg covered]
    exact before_b_memory s slot start index dst salts w ready a bounded

end TwoPermutationPrototype.RV64.WideLeaves
