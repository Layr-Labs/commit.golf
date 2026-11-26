import CommitGolfCandidate.ReconstructedLeafPrelude

namespace CommitGolfCandidate.Reconstruction.LeafLane
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.RV64
open TwoPermutationPrototype.Sampling (pinnedPositionTag)
open LeafCode LeafModel LeafMacros CommitWindows LeafSpill LeafContent LeafPrelude Generator

def slot (i : Index) := i.val % 4096
abbrev shift (i : Index) := slot i ≠ 0 ∧ slot i % 63 = 0
def center (i : Index) := heapBase+4*(4096*(tileOf i).val+63*(slot i/63))
def beforeCenter (i : Index) := if shift i then center i-252 else center i
def p (i : Index) := entryStart i+7
def baseSalt (i : Index) := entryStart i-15-32*(laneOf i).val

theorem limits (i : Index) : 512 ≤ entryStart i ∧ entryStart i+32 ≤ heapBase ∧
    location i+25 < generatorBase-16 ∧ generatorBase+25 ≤ 2^33 := by
  have h : i.val < 2^24 := i.isLt
  unfold entryStart location heapBase generatorBase
  omega

theorem position_tag (i : Index) : wordAddress (p i) = pinnedPositionTag i := by
  unfold wordAddress p entryStart pinnedPositionTag
  congr 1 <;> omega

theorem target (i : Index) : center i+4*(slot i%63) = location i := by
  simp only [center,slot,location,tileOf]
  omega

theorem salt_coord (i : Index) : p i = baseSalt i+22+32*(laneOf i).val := by
  have := position_decomposition i
  unfold baseSalt p entryStart
  omega

def rebaseState (m : Model) (i : Index) := if shift i then m.set .x19 (wordAddress (center i)) else m

theorem rebase_step (o : Oracle) (m : Model) (i : Index) (reg : m.reg .x19 = wordAddress (beforeCenter i)) :
    Contract o (rebase (slot i)) m (rebaseState m i) := by
  unfold rebase rebaseState shift
  split
  · rename_i h
    apply LeafModel.addi
    have low : 252 ≤ center i := by unfold center heapBase; omega
    rw [reg,beforeCenter,if_pos h,plus (center i-252) 252 2016 rfl,Nat.sub_add_cancel low]
  · exact LeafModel.empty _ _

theorem rebase_center (m : Model) (i : Index) (reg : m.reg .x19 = wordAddress (beforeCenter i)) :
    (rebaseState m i).reg .x19 = wordAddress (center i) := by
  unfold rebaseState
  split
  · rfl
  · rename_i h; simpa [beforeCenter,h] using reg

theorem rebase_other (m : Model) (i : Index) (r : Reg) (ne : r ≠ .x19) :
    (rebaseState m i).reg r = m.reg r := by
  unfold rebaseState
  split <;> simp [Model.set,Ne.symm ne]

theorem rebase_mem (m : Model) (i : Index) : (rebaseState m i).mem = m.mem := by
  unfold rebaseState; split <;> rfl

def grouped (o : Oracle) (m : Model) (i : Index) :=
  if (laneOf i).val=0 then afterGroup o m (entryStart i) (groupOf i) else m

def staged (o : Oracle) (m : Model) (i : Index) := rebaseState (grouped o m i) i

def pointed (o : Oracle) (m : Model) (i : Index) :=
  let a := staged o m i
  if (laneOf i).val=0 then a.set .x10 (wordAddress (p i)) else
    (rawState o a (entryStart i)).set .x10 (wordAddress (p i))

def tagged (o : Oracle) (m : Model) (i : Index) := (pointed o m i).store (p i) (pinnedPositionTag i)

def salted (o : Oracle) (m : Model) (i : Index) :=
  let a := tagged o m i
  let l := (laneOf i).val
  if l=0 then a else if l<8 then nearState a (p i) (baseSalt i) l else
    stamp a (p i) (a.reg (saved (2*(l-8)))) (a.reg (saved (2*(l-8)+1)))

def result (o : Oracle) (m : Model) (i : Index) := finishState o (salted o m i) (p i) (location i)

structure Enter (m : Model) (i : Index) : Prop extends Fixed m where
  ptr : m.reg .x10 = wordAddress (entryStart i-25)
  anchor : m.reg .x19 = wordAddress (beforeCenter i)

theorem grouped_read (o : Oracle) (m : Model) (i : Index) (r : Reg) (u : ∀ j : Fin 8, saved j.val ≠ r)
    (a : r ≠ .x10) (b : r ≠ .x12) : (grouped o m i).reg r = m.reg r := by
  unfold grouped
  split
  · exact after_group_reg _ _ _ _ _ u a b
  · rfl

theorem staged_read (o : Oracle) (m : Model) (i : Index) (r : Reg) (u : ∀ j : Fin 8, saved j.val ≠ r)
    (a : r ≠ .x10) (b : r ≠ .x12) (c : r ≠ .x19) : (staged o m i).reg r = m.reg r :=
  (rebase_other _ _ _ c).trans (grouped_read _ _ _ _ u a b)

def pointingCode (i : Index) : List Instr :=
  if (laneOf i).val=0 then [.ADDI .x10 .x12 176] else rawCode ++ [.ADDI .x10 .x10 56]

theorem point (o : Oracle) (m : Model) (i : Index) (e : Enter m i) :
    Contract o (pointingCode i) (staged o m i) (pointed o m i) := by
  let a := staged o m i
  let src := entryStart i
  have lim := limits i
  have room : src+32 ≤ 2^33 := by dsimp [src]; unfold heapBase at lim; omega
  have reg (r : Reg) (u : ∀ j : Fin 8, saved j.val ≠ r) (ha : r ≠ .x10) (hb : r ≠ .x12) (hc : r ≠ .x19) :
      a.reg r = m.reg r := staged_read _ _ _ _ u ha hb hc
  unfold pointingCode pointed
  split
  · rename_i h
    have dst : a.reg .x12 = wordAddress (src-15) := by
      dsimp only [a,staged]
      rw [rebase_other _ _ _ (by decide),grouped,if_pos h,after_group_dst]
    apply LeafModel.addi
    change a.reg .x12+_ = _
    rw [dst,plus (src-15) 22 176 rfl]
    exact congrArg wordAddress (by dsimp [src,p]; omega)
  · rename_i h
    have ptr : a.reg .x10 = wordAddress (src-25) := by
      dsimp only [a,staged]
      rw [rebase_other _ _ _ (by decide),grouped,if_neg h]
      exact e.ptr
    have r := raw_call o a src (by dsimp [src]; omega) room ptr
      ((reg _ (by decide) (by decide) (by decide) (by decide)).trans e.mode)
      ((reg _ (by decide) (by decide) (by decide) (by decide)).trans e.len)
      ((reg _ (by decide) (by decide) (by decide) (by decide)).trans e.kind)
    apply LeafModel.combine r
    apply LeafModel.addi
    exact plus src 7 56 rfl

theorem pointed_ptr (o : Oracle) (m : Model) (i : Index) :
    (pointed o m i).reg .x10 = wordAddress (p i) := by unfold pointed; split <;> rfl

theorem tag (o : Oracle) (m : Model) (i : Index) :
    Contract o [.SD .x10 .x10 0] (pointed o m i) (tagged o m i) := by
  have h := limits i
  have step := LeafModel.store o (pointed o m i) .x10 .x10 0 (p i) (by unfold p; unfold heapBase at h; omega)
    (by rw [pointed_ptr]; exact BitVec.add_zero _)
  rwa [pointed_ptr,position_tag] at step

theorem nonce (o : Oracle) (m : Model) (i : Index) :
    Contract o (saltLoad (laneOf i).val) (tagged o m i) (salted o m i) := by
  let a := tagged o m i
  have lim := limits i
  have room : p i+3 ≤ 2^33 := by unfold p; unfold heapBase at lim; omega
  have ptr : a.reg .x10 = wordAddress (p i) := pointed_ptr _ _ _
  dsimp only [salted]
  split
  · rename_i h
    simpa only [saltLoad,h,ite_true] using (LeafModel.empty o a)
  · rename_i ne
    split
    · rename_i small
      exact near o a (baseSalt i) ⟨(laneOf i).val,small⟩ (show 0 < (laneOf i).val by omega) (p i) (salt_coord i) room ptr
    · rename_i big
      exact far o a (p i) (laneOf i).val (by omega) room ptr

end CommitGolfCandidate.Reconstruction.LeafLane
