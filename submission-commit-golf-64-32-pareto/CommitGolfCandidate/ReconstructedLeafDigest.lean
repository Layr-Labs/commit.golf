import CommitGolfCandidate.ReconstructedLeafSource
import CommitGolfCandidate.ReconstructedLeafRun

namespace CommitGolfCandidate.Reconstruction.LeafDigest
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype (Memory Words window writeWindow writeWord)
open LeafCode LeafModel LeafMacros CommitWindows LeafSpill LeafContent LeafPrelude Generator LeafLane LeafSource

def tapeWord (o : Oracle) (k : Key) (i : Index) (w : Fin 25) := replyWords (tapeReply o k i) w

/-- All later lanes read from the current block's scratch or saved registers. The final
short block only needs three pairs in scratch and never uses any saved register. -/
structure Scratch (o : Oracle) (k : Key) (m : Model) (i : Index) : Prop where
  words : (laneOf i).val ≠ 0 → ∀ j : Fin 14, m.mem (baseSalt i+j.val) = tapeWord o k i ⟨j.val,by omega⟩
  registers : (laneOf i).val ≠ 0 → (groupOf i).val < 341 → ∀ j : Fin 8,
    m.reg (saved j.val) = tapeWord o k i ⟨14+j.val,by omega⟩

def clear (m : Model) (i : Index) := m.store (p i+2) (m.mem (p i+2) &&& 0x00ffffffffffffff)

def secondMem (o : Oracle) (m : Model) (i : Index) := (clear (salted o m i) i).mem

theorem zero_mem (o : Oracle) (m : Model) (k : Key) (msg : Message) (i : Index)
    (e : Enter m i) (front : (laneOf i).val=0) (pre : Prefix o k msg i.val m.mem) (c : Counter m i) :
    secondMem o m i = firstHeader (updateCounter m (groupOf i)).mem i (firstReply o msg i) (tapeReply o k i) := by
  have raw := pointed_first o m k msg i e front pre c
  simp only [secondMem,clear,salted,front,ite_true,tagged,Model.store,raw,firstHeader,p]
  congr 1
  simp [writeWord]

theorem near_words (o : Oracle) (m : Model) (k : Key) (msg : Message) (i : Index) (pos : (laneOf i).val ≠ 0)
    (small : (laneOf i).val<8) (pre : Prefix o k msg i.val m.mem) (sc : Scratch o k m i) :
    let w := baseSalt i+2*((laneOf i).val-1)
    let a := tagged o m i
    a.mem w = tapeWord o k i (LeafNonce.firstWord (laneOf i)) ∧
    a.mem (w+1) = tapeWord o k i (LeafNonce.nextWord (laneOf i)) := by
  dsimp only
  have raw := pointed_later o m k msg i pos pre
  have lo := limits i
  let l := (laneOf i).val
  let offset := 2*(l-1)
  have mag : offset+1 < 14 := by dsimp [offset,l]; omega
  have fst : (LeafNonce.firstWord (laneOf i)).val = offset := by simp [LeafNonce.firstWord,pos,offset,l]
  have snd : (LeafNonce.nextWord (laneOf i)).val = offset+1 := by change (LeafNonce.firstWord _).val+1 = _; rw [fst]
  have below : baseSalt i+offset+1 < entryStart i-4 := by
    have coord := salt_coord i; unfold p at coord; dsimp [offset,l]; omega
  have atWord (j : Fin 25) (jh : j.val < 14) (jh' : baseSalt i+j.val < entryStart i-4) :
      (tagged o m i).mem (baseSalt i+j.val) = tapeWord o k i j := by
    have ne : baseSalt i+j.val ≠ p i := by unfold p; omega
    have away : ¬(entryStart i-4 ≤ baseSalt i+j.val ∧ baseSalt i+j.val < entryStart i-4+25) := by omega
    simp only [tagged,Model.store,raw,writeWord,ne,ite_false,writeWindow,away,dite_false]
    exact sc.words pos ⟨j.val,jh⟩
  constructor
  · have h := atWord (LeafNonce.firstWord (laneOf i)) (by omega) (by omega)
    simpa only [fst] using h
  · have h := atWord (LeafNonce.nextWord (laneOf i)) (by omega) (by omega)
    simpa only [snd,Nat.add_assoc] using h

theorem far_words (o : Oracle) (m : Model) (k : Key) (i : Index) (far : 8 ≤ (laneOf i).val)
    (sc : Scratch o k m i) :
    let a := tagged o m i
    let r := 2*((laneOf i).val-8)
    a.reg (saved r) = tapeWord o k i (LeafNonce.firstWord (laneOf i)) ∧
    a.reg (saved (r+1)) = tapeWord o k i (LeafNonce.nextWord (laneOf i)) := by
  let l := (laneOf i).val
  let r := 2*(l-8)
  have range : l < 12 := (laneOf i).isLt
  have full : (groupOf i).val < 341 := by
    change i.val%4096/12 < 341
    change 8 ≤ i.val%4096%12 at far
    omega
  have all (j : Fin 8) : (tagged o m i).reg (saved j.val) = tapeWord o k i ⟨14+j.val,by omega⟩ := by
    rw [show (tagged o m i).reg _ = _ from pointed_read o m i (saved j.val)
      ((by decide : ∀ j : Fin 8, saved j.val ≠ .x10) j) ((by decide : ∀ j : Fin 8, saved j.val ≠ .x12) j)]
    simp only [staged,rebase_other _ _ _ ((by decide : ∀ j : Fin 8, saved j.val ≠ .x19) j),
      grouped,show (laneOf i).val≠0 by omega,ite_false]
    exact sc.registers (by omega) full j
  dsimp only
  have re : r+1<8 := by dsimp [r,l] at *; omega
  have fst : (LeafNonce.firstWord (laneOf i)).val = 14+r := by
    simp only [LeafNonce.firstWord,show (laneOf i).val≠0 by omega,ite_false]; dsimp [r,l]; omega
  have snd : (LeafNonce.nextWord (laneOf i)).val = 14+(r+1) := by
    change (LeafNonce.firstWord _).val+1 = _; omega
  constructor
  · exact (all ⟨r,by omega⟩).trans (congrArg (tapeWord o k i) (Fin.ext fst.symm))
  · exact (all ⟨r+1,re⟩).trans (congrArg (tapeWord o k i) (Fin.ext snd.symm))

def laterHeader (mem : Memory) (i : Index) (raw : BitVec 1600) (low high : Word) :=
  let a := writeWindow mem (entryStart i-4) (replyWords raw)
  writeWord (writeWord (writeWord a (p i) (pinnedPositionTag i)) (p i+1) low)
    (p i+2) (high &&& 0x00ffffffffffffff)

private theorem stamp_clear (m : Model) (i : Index) (lo hi : Word) :
    (clear (stamp m (p i) lo hi) i).mem =
      writeWord (writeWord m.mem (p i+1) lo) (p i+2) (hi &&& 0x00ffffffffffffff) := by
  funext w
  by_cases last : w=p i+2 <;> simp [clear,stamp,Model.store,writeWord,last]

theorem later_mem (o : Oracle) (m : Model) (k : Key) (msg : Message) (i : Index) (pos : (laneOf i).val≠0)
    (pre : Prefix o k msg i.val m.mem) (sc : Scratch o k m i) :
    secondMem o m i = laterHeader m.mem i (firstReply o msg i)
      (tapeWord o k i (LeafNonce.firstWord (laneOf i))) (tapeWord o k i (LeafNonce.nextWord (laneOf i))) := by
  have raw := pointed_later o m k msg i pos pre
  simp only [secondMem,salted,pos,ite_false]
  split
  · rename_i sm
    obtain ⟨lo,hi⟩ := near_words o m k msg i pos sm pre sc
    simp only [nearState,stamp_clear,Model.set]
    rw [lo,hi]
    simp only [tagged,Model.store,raw,laterHeader]
  · rename_i big
    obtain ⟨lo,hi⟩ := far_words o m k i (by omega) sc
    rw [stamp_clear,lo,hi]
    simp only [tagged,Model.store,raw,laterHeader]

theorem second_input (o : Oracle) (m : Model) (k : Key) (msg : Message) (i : Index) (e : Enter m i)
    (pre : Prefix o k msg i.val m.mem) (c : Counter m i) (sc : Scratch o k m i) :
    window (secondMem o m i) (p i) =
      pinnedSecondInput i (saltWords ((LeafNonce.selected (tapeReply o k i) (laneOf i)).setWidth 128))
        (replyWords (firstReply o msg i)) (messageWords msg i) := by
  by_cases first : (laneOf i).val=0
  · rw [zero_mem o m k msg i e first pre c,show laneOf i=0 from Fin.ext first]
    refine (lane_zero_input ..).trans ?_
    exact congrArg₂ (fun nonce entry => pinnedSecondInput i nonce (replyWords (firstReply o msg i)) entry)
      (LeafNonce.zero (tapeReply o k i)) ((low_window m i).trans (pre.future i (by omega)))
  · rw [later_mem o m k msg i first pre sc]
    refine (LeafMemory.tag_window ..).trans ?_
    exact congrArg₂ (fun nonce entry => pinnedSecondInput i nonce (replyWords (firstReply o msg i)) entry)
      (LeafNonce.pair (tapeReply o k i) (laneOf i)) (pre.future i (by omega))

theorem finished (o : Oracle) (m : Model) (k : Key) (msg : Message) (i : Index) (e : Enter m i)
    (pre : Prefix o k msg i.val m.mem) (c : Counter m i) (sc : Scratch o k m i) :
    (result o m i).mem = putLeaf (secondMem o m i) i (lastReply o k msg i) := by
  have qry := second_input o m k msg i e pre c sc
  let reply := lastReply o k msg i
  have answer : o.permutation (packBuffer (window (secondMem o m i) (p i))) = reply := by rw [qry]; rfl
  let before := secondMem o m i
  let actual : BitVec 1600 := o.permutation (packBuffer (window before (p i)))
  let post (v : BitVec 1600) := writeWindow before (location i) (replyWords v)
  change writeWord (post actual) (location i+3) (post actual (location i+3) ||| 0xffff000000000000) = _
  have eq : actual = reply := answer
  rw [eq]
  have cell : post reply (location i+3) = replyWords reply 3 := by
    dsimp only [post]
    simp [writeWindow]
  rw [cell]
  rfl

end CommitGolfCandidate.Reconstruction.LeafDigest
