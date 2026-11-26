import CommitGolfCandidate.ReconstructedLeafLane

namespace CommitGolfCandidate.Reconstruction.LeafSource
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype (Memory Words window writeWindow writeWord)
open LeafCode LeafModel LeafMacros CommitWindows LeafSpill LeafContent LeafPrelude Generator LeafLane

/-- The byte pointer preceding the first entry of each 192-entry group of counters. -/
theorem counter_ptr (i : Index) (front : (laneOf i).val=0) (refresh : (groupOf i).val%16=0) :
    wordAddress (entryStart i-25) = BitVec.ofNat 64 (counter (tileOf i) (groupOf i)) := by
  have h := position_decomposition i
  unfold wordAddress entryStart counter
  congr 1 <;> omega

def Counter (m : Model) (i : Index) := (groupOf i).val%16 ≠ 0 →
  m.mem (generatorBase+1) = BitVec.ofNat 64 (counter (tileOf i) (groupOf i))

theorem updated_counter (m : Model) (i : Index) (e : Enter m i) (front : (laneOf i).val=0) (c : Counter m i) :
    (updateCounter m (groupOf i)).mem (generatorBase+1) = BitVec.ofNat 64 (counter (tileOf i) (groupOf i)) := by
  unfold updateCounter
  split
  · rename_i yes
    simpa [Model.store,writeWord,e.ptr] using counter_ptr i front yes
  · rename_i no; exact c no

theorem update_other (m : Model) (i : Index) (w : Nat) (ne : w ≠ generatorBase+1) :
    (updateCounter m (groupOf i)).mem w = m.mem w := by
  unfold updateCounter
  split <;> simp [Model.store,writeWord,ne]

theorem w_below (i : Index) : entryStart i+32 ≤ generatorBase-16 := by
  have h := limits i
  unfold heapBase generatorBase at *
  omega

theorem low_window (m : Model) (i : Index) :
    (window (updateCounter m (groupOf i)).mem (entryStart i) : Words 32) = window m.mem (entryStart i) := by
  funext j
  exact update_other m i _ (by have := w_below i; have := j.isLt; unfold generatorBase at *; omega)

theorem raw_mem (o : Oracle) (m : Model) (msg : Message) (i : Index)
    (entry : (window m.mem (entryStart i) : Words 32) = messageWords msg i) :
    (rawState o m (entryStart i)).mem = writeWindow m.mem (entryStart i-4) (replyWords (firstReply o msg i)) := by
  have cut : (window m.mem (entryStart i) : Words 25) = pinnedFirstInput (messageWords msg i) := by
    funext j
    exact congrFun entry ⟨j.val,by have := j.isLt; omega⟩
  change writeWindow _ _ (replyWords (o.permutation (packBuffer (window m.mem _)))) = _
  rw [cut]; rfl

theorem raw_outside (o : Oracle) (m : Model) (i : Index) (w : Nat)
    (away : w < entryStart i-4 ∨ entryStart i-4+25 ≤ w) :
    (rawState o m (entryStart i)).mem w = m.mem w := by
  change writeWindow _ _ _ w = _
  have hn : ¬(entryStart i-4≤w ∧ w<entryStart i-4+25) := by omega
  simp only [writeWindow,hn,dite_false,Model.set]

theorem counter_window (o : Oracle) (m : Model) (k : Key) (i : Index) (e : Enter m i)
    (front : (laneOf i).val=0) (header : KeyRegion m.mem k) (c : Counter m i) :
    window (rawState o (updateCounter m (groupOf i)) (entryStart i)).mem (generatorBase-marker (groupOf i)) =
      (fun j : Fin 25 => inputWord (tileOf i) (groupOf i) k j.val) := by
  rw [←generator_window]
  funext j
  let w := generatorBase-marker (groupOf i)+j.val
  have mark : marker (groupOf i) ≤ 16 := by unfold marker; omega
  have lo : generatorBase-16 ≤ w := by dsimp [w]; omega
  have hi : w < generatorBase+25 := by dsimp [w]; have := j.isLt; omega
  change (rawState o (updateCounter m (groupOf i)) _).mem w = generatorMemory (tileOf i) (groupOf i) k w
  rw [raw_outside o _ i w (Or.inr (by have := w_below i; omega))]
  by_cases atCount : w = generatorBase+1
  · rw [atCount,updated_counter m i e front c]; simp [generatorMemory]
  · rw [update_other m i w atCount,header w lo hi atCount]
    change generatorMemory 0 0 k w = generatorMemory (tileOf i) (groupOf i) k w
    simp only [generatorMemory,atCount,ite_false]

/-- The permutation in the submitted group prelude receives the physical marker,
counter and key words, even after the preceding overlapping raw permutation. -/
theorem group_mem (o : Oracle) (m : Model) (k : Key) (msg : Message) (i : Index)
    (e : Enter m i) (front : (laneOf i).val=0) (pre : Prefix o k msg i.val m.mem) (c : Counter m i) :
    (grouped o m i).mem =
      generatedFirst (updateCounter m (groupOf i)).mem i (firstReply o msg i) (tapeReply o k i) := by
  let a := updateCounter m (groupOf i)
  have raw := raw_mem o a msg i ((low_window m i).trans (pre.future i (by omega)))
  have gen := counter_window o m k i e front pre.header c
  rw [grouped,if_pos front,after_group_mem]
  change writeWindow (rawState o a (entryStart i)).mem (entryStart i-15)
    (replyWords (o.permutation (packBuffer (window (rawState o a (entryStart i)).mem
    (generatorBase-marker (groupOf i)))))) = _
  rw [gen,raw]; rfl

theorem pointed_first (o : Oracle) (m : Model) (k : Key) (msg : Message) (i : Index)
    (e : Enter m i) (front : (laneOf i).val=0) (pre : Prefix o k msg i.val m.mem) (c : Counter m i) :
    (pointed o m i).mem = generatedFirst (updateCounter m (groupOf i)).mem i (firstReply o msg i) (tapeReply o k i) := by
  simp only [pointed,front,ite_true,Model.set,staged,rebase_mem,group_mem o m k msg i e front pre c]

theorem pointed_later (o : Oracle) (m : Model) (k : Key) (msg : Message) (i : Index)
    (later : (laneOf i).val≠0) (pre : Prefix o k msg i.val m.mem) :
    (pointed o m i).mem = writeWindow m.mem (entryStart i-4) (replyWords (firstReply o msg i)) := by
  have stage : (staged o m i).mem = m.mem := by simp only [staged,rebase_mem,grouped,later,ite_false]
  have raw := raw_mem o (staged o m i) msg i (by rw [stage]; exact pre.future i (by omega))
  simp only [pointed,later,ite_false,Model.set,raw,stage]

end CommitGolfCandidate.Reconstruction.LeafSource
