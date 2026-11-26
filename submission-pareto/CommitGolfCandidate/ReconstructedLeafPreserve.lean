import CommitGolfCandidate.ReconstructedLeafDigest

namespace CommitGolfCandidate.Reconstruction.LeafPreserve
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype (Memory Words window writeWindow writeWord)
open LeafCode LeafModel LeafMacros CommitWindows LeafSpill LeafContent LeafPrelude Generator LeafLane LeafSource LeafDigest

def origin (m : Model) (i : Index) : Memory :=
  if (laneOf i).val=0 then (updateCounter m (groupOf i)).mem else m.mem

theorem frame_origin (m : Model) (i : Index) (w : Nat) (ne : w ≠ generatorBase+1) :
    origin m i w = m.mem w := by
  unfold origin; split
  · exact update_other _ _ _ ne
  · rfl

structure Ready (o : Oracle) (m : Model) (k : Key) (msg : Message) (i : Index) : Prop where
  enter : Enter m i
  pre : Prefix o k msg i.val m.mem
  counter : Counter m i
  scratch : Scratch o k m i

theorem second_frame (o : Oracle) (m : Model) (k : Key) (msg : Message) (i : Index)
    (ok : Ready o m k msg i) (w : Nat) (sep : w < entryStart i-15 ∨ entryStart i+32 ≤ w) :
    secondMem o m i w = origin m i w := by
  have lb := (limits i).1
  have nd : w ≠ p i := by unfold p; omega
  have n1 : w ≠ p i+1 := by unfold p; omega
  have n2 : w ≠ p i+2 := by unfold p; omega
  have raw : ¬(entryStart i-4 ≤ w ∧ w < entryStart i-4+25) := by omega
  have tape : ¬(entryStart i-15 ≤ w ∧ w < entryStart i-15+25) := by omega
  by_cases first : (laneOf i).val=0
  · rw [zero_mem o m k msg i ok.enter first ok.pre ok.counter]
    change writeWord (writeWord _ (p i) _) (p i+2) _ w = _
    simp only [origin,first,ite_true,writeWord,nd,n2,ite_false,generatedFirst,writeWindow,raw,tape,dite_false]
  · rw [later_mem o m k msg i first ok.pre ok.scratch]
    simp only [origin,first,ite_false,laterHeader,writeWord,nd,n1,n2,writeWindow,raw,dite_false]

theorem memory_frame (o : Oracle) (m : Model) (k : Key) (msg : Message) (i : Index)
    (ok : Ready o m k msg i) (w : Nat) (source : w < entryStart i-15 ∨ entryStart i+32 ≤ w)
    (dst : w < location i ∨ location i+25 ≤ w) :
    (result o m i).mem w = origin m i w :=
  (congrFun (finished o m k msg i ok.enter ok.pre ok.counter ok.scratch) w).trans
    ((outside _ _ _ _ dst).trans (second_frame _ _ _ _ _ ok w source))

/-- Advance the complete memory contract by exactly one leaf. Earlier hashes, unopened
entries, the reserved parent area and the permanent key region remain available. -/
theorem advance (o : Oracle) (m : Model) (k : Key) (msg : Message) (i : Index) (ok : Ready o m k msg i) :
    Prefix o k msg (i.val+1) (result o m i).mem := by
  have whole := finished o m k msg i ok.enter ok.pre ok.counter ok.scratch
  have loc (j : Index) : heapBase ≤ location j := by unfold location; omega
  have none (w : Nat) (source : w < entryStart i-15 ∨ entryStart i+32 ≤ w)
      (dst : w < location i ∨ location i+25 ≤ w) (ne : w ≠ generatorBase+1) :
      (result o m i).mem w = m.mem w :=
    (memory_frame _ _ _ _ _ ok _ source dst).trans (frame_origin m i w ne)
  have bounds := limits i
  constructor
  · intro j after
    refine Eq.trans ?_ (ok.pre.future j (by omega))
    funext w
    have J := limits j
    have N := w.isLt
    apply none
    · exact Or.inr (by unfold entryStart; omega)
    · left; have := loc i; omega
    · unfold heapBase generatorBase at *; omega
  · intro j earlier
    by_cases equal : j=i
    · subst j; rw [whole,inserted]
    · have prev : j.val < i.val := by have ne : j.val≠i.val := fun h => equal (Fin.ext h); omega
      refine Eq.trans ?_ (ok.pre.past j prev)
      funext w
      have N := w.isLt
      have J := limits j
      apply none
      · right; have := loc j; omega
      · left; unfold location; omega
      · unfold generatorBase at *; omega
  · intro w lo hi
    refine (none w (Or.inr ?_) (Or.inl ?_) ?_).trans (ok.pre.parents w lo hi)
    · have jBound : i.val < 2^24 := i.isLt
      unfold entryStart; omega
    · have := loc i; omega
    · unfold heapBase generatorBase at *; omega
  · intro w lo hi ne
    refine (none w (Or.inr ?_) (Or.inr ?_) ne).trans (ok.pre.header w lo hi ne)
    · have := w_below i; omega
    · omega

def Guard (m : Model) (i : Index) :=
  ((laneOf i).val ≠ 0 ∨ (groupOf i).val%16 ≠ 0) →
    m.mem (generatorBase+1) = BitVec.ofNat 64 (counter (tileOf i) (groupOf i))

theorem guard_counter (m : Model) (i : Index) (g : Guard m i) : Counter m i := fun h => g (.inr h)

theorem committed_counter (o : Oracle) (m : Model) (k : Key) (msg : Message) (i : Index)
    (ok : Ready o m k msg i) (g : Guard m i) :
    (result o m i).mem (generatorBase+1) = BitVec.ofNat 64 (counter (tileOf i) (groupOf i)) := by
  have h := limits i
  rw [memory_frame _ _ _ _ _ ok _ (Or.inr (by have := w_below i; omega)) (Or.inr (by omega))]
  unfold origin
  split
  · rename_i z; exact updated_counter m i ok.enter z ok.counter
  · rename_i nz; exact g (.inl nz)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
theorem next_guard (o : Oracle) (m : Model) (k : Key) (msg : Message) (i j : Index)
    (succ : j.val=i.val+1) (ok : Ready o m k msg i) (g : Guard m i) : Guard (result o m i) j := by
  intro active
  rw [committed_counter o m k msg i ok g]
  apply congrArg (BitVec.ofNat 64)
  simp only [tileOf,groupOf,laneOf,counter] at active ⊢
  rw [succ] at active ⊢
  have nz : (i.val+1)%4096 ≠ 0 := by
    intro z
    simp only [z,Nat.zero_mod,Nat.zero_div,ne_eq,not_true_eq_false,or_self] at active
  have tile : (i.val+1)/4096 = i.val/4096 := by omega
  have step : (i.val+1)%4096 = i.val%4096+1 := by omega
  rw [step] at active
  have table : ∀ x : Fin 4096, ((x.val+1)%12 ≠ 0 ∨ (x.val+1)/12%16 ≠ 0) →
      (x.val+1)/12/16 = x.val/12/16 := by decide
  rw [tile,step,table ⟨i.val%4096,by omega⟩ active]

end CommitGolfCandidate.Reconstruction.LeafPreserve
