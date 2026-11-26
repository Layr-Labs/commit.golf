import CommitGolfCandidate.ReconstructedOpeningCursor

namespace CommitGolfCandidate.Reconstruction.OpeningSaltLow
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningOps OpeningQuery OpeningLane
open TwoPermutationPrototype.RV64 OpeningPut OpeningCursor
open TwoPermutationPrototype (writeWord)
open CommitBlocks (addr)
set_option maxRecDepth 12000
set_option maxHeartbeats 1500000

def overflowOps (c : Nat) : List Op := [
  .ld .x14 .x13 0 (cell c),.reg .x16 (.sll .x12 .x10),.reg .x17 (.subw .x0 .x10),
  .reg .x12 (.srl .x12 .x17),.reg .x14 (.or .x14 .x16),.sd .x13 .x12 8 (cell c+1),
  .reg .x12 (.addi .x14 0)]

def storeOps (c : Nat) : List Op := [.sd .x13 .x12 0 (cell c)]
private theorem overflowTable (c : Nat) : OpeningStraight.Listed 206 ((overflowOps c).map Op.instr) :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
private theorem storeTable (c : Nat) : OpeningStraight.Listed 213 ((storeOps c).map Op.instr) := ⟨rfl,True.intro⟩

theorem room (c : Nat) (bound : c/64<capacity) : cell c+1<2^33 := by dsimp [cell,base,capacity] at *;omega

private theorem overflowChecks (m : Model) (c : Nat) (bound : c/64<capacity) (dst : m.reg .x13=wordAddress (cell c)) :
    Checked m (overflowOps c) := by
  have ok := room c bound
  simp only [overflowOps,Checked,Op.Valid,Op.apply,true_and,and_true]
  refine ⟨⟨by omega,?_⟩,⟨ok,?_⟩⟩
  · rw [dst];exact BitVec.add_zero _
  · change m.reg .x13 + signExtend12 8 = _
    rw [dst,wordAddress_add];rfl

private theorem overflowValues (m : Model) (c : Nat) (nz : c%64≠0)
    (offset : m.reg .x10=W (c%64)) (zero : m.reg .x0=0) :
    let t := after m (overflowOps c)
    t.mem=writeWord m.mem (cell c+1) (m.reg .x12 >>> (64-c%64)) ∧
    t.reg .x12=first m.mem c (m.reg .x12) ∧
    (∀ r, r≠.x12 → r≠.x14 → r≠.x16 → r≠.x17 → t.reg r=m.reg r) := by
  have ord : (W (c%64)).toNat%64=c%64 := by change ((c%64)%2^64)%64=c%64;omega
  have sh := negative_shift ⟨c%64,Nat.mod_lt _ (by decide)⟩ (Nat.pos_of_ne_zero nz)
  constructor
  · change writeWord m.mem (cell c+1) (m.reg .x12 >>> ((((m.reg .x0).truncate 32 -
        (m.reg .x10).truncate 32).signExtend 64).toNat%64)) = _
    rw [zero,offset];exact congrArg (fun n : Nat => writeWord m.mem (cell c+1) (m.reg .x12 >>> n)) sh
  constructor
  · change (m.mem (cell c) ||| (m.reg .x12 <<< ((m.reg .x10).toNat%64))) + 0 = _
    calc
      _ = m.mem (cell c) ||| (m.reg .x12 <<< ((m.reg .x10).toNat%64)) := BitVec.add_zero _
      _ = _ := by rw [offset,ord,first,ite_eq_right nz]
  · intro r a b d e
    simp [after,overflowOps,Op.apply,Model.set,Model.store,a.symm,b.symm,d.symm,e.symm]

private theorem storeChecks (m : Model) (c : Nat) (bound : c/64<capacity)
    (p : m.reg .x13=wordAddress (cell c)) : Checked m (storeOps c) := by
  have ok := room c bound
  exact ⟨⟨by omega,by rw [p];exact BitVec.add_zero _⟩,True.intro⟩

def saved (m : Model) (c : Nat) := if c%64=0 then m else after m (overflowOps c)
def finish (m : Model) (c : Nat) := after (saved (after m addressOps) c) (storeOps c)

private theorem legs (o : Oracle) (m : Model) (c : Nat) (bound : c/64<capacity)
    (s : MachineState) (pc : s.pc=addr 205) (h : Fits s m)
    (offset : m.reg .x10=W (c%64)) (dst : m.reg .x13=wordAddress (cell c)) :
    ∃ t, CommitExact.Segment o OpeningStraight.image (if c%64=0 then 1 else 8) s t ∧
      t.pc=addr 213 ∧ Fits t (saved m c) := by
  have g := zero_branch o s 205 206 213 .x10 32 pc (by decide) rfl rfl rfl (W (c%64)) ((h.registers _).trans offset)
  have ziff : W (c%64)=0 ↔ c%64=0 := by
    constructor
    · intro z;have n := congrArg BitVec.toNat z
      change (c%64)%2^64=0 at n;omega
    · intro z;rw [z];rfl
  simp only [ziff] at g
  unfold saved
  by_cases z : c%64=0
  · simp only [z,ite_true] at g ⊢
    exact ⟨_,g,rfl,h.pc _⟩
  · simp only [z,ite_false] at g ⊢
    obtain ⟨u,r,pc',f⟩ := OpeningStraight.block o m (overflowOps c) 206 (by change 206+7≤1660;decide)
      (overflowTable c) (overflowChecks m c bound dst) (s.setPC _) rfl (h.pc _)
    exact ⟨_,CommitExact.compose g r,pc',f⟩

private theorem untouched (m : Model) (c : Nat) (r : Reg)
    (a : r≠.x12) (b : r≠.x14) (d : r≠.x16) (e : r≠.x17) : (saved m c).reg r=m.reg r := by
  unfold saved;split
  · rfl
  · simp [after,overflowOps,Op.apply,Model.set,Model.store,a.symm,b.symm,d.symm,e.symm]

private theorem finalMemory (m : Model) (c : Nat) (offset : m.reg .x10=W (c%64)) (zero : m.reg .x0=0) :
    (after (saved m c) (storeOps c)).mem=put m.mem c 64 (m.reg .x12) := by
  change writeWord (saved m c).mem (cell c) ((saved m c).reg .x12) = _
  unfold saved put
  by_cases align : c%64=0
  · simp [align,first]
  · simp only [align,ite_false]
    have cross : c%64+64>64 := by omega
    rw [ite_eq_left cross,(overflowValues m c align offset zero).1,(overflowValues m c align offset zero).2.1]
    funext j
    by_cases atFirst : j=cell c
    · subst j;simp only [writeWord,show cell c≠cell c+1 by omega,ite_false,ite_true]
    · simp only [writeWord,atFirst,ite_false]

theorem exit_offset (m : Model) (c : Nat) (fit : c<2^64) (cursor : m.reg .x7=W c)
    (baseReg : m.reg .x25=wordAddress base) :
    (finish m c).reg .x10=W (c%64) :=
  (untouched (after m addressOps) c .x10 (by decide) (by decide) (by decide) (by decide)).trans
    (address_values m c fit cursor baseReg).1

/-- Actual words 201 through 213 append the 64 low salt bits at any alignment. -/
theorem run (o : Oracle) (m : Model) (c : Nat) (bound : c/64<capacity) (s : MachineState)
    (pc : s.pc=addr 201) (fits : Fits s m) (zero : m.reg .x0=0) (cursor : m.reg .x7=W c)
    (baseReg : m.reg .x25=wordAddress base) :
    ∃ u, CommitExact.Segment o OpeningStraight.image (4+(if c%64=0 then 1 else 8)+1) s u ∧ u.pc=addr 214 ∧
      Fits u (finish m c) ∧ (finish m c).mem=put m.mem c 64 (m.reg .x12) ∧
      (∀ r, r≠.x10 → r≠.x13 → r≠.x12 → r≠.x14 → r≠.x16 → r≠.x17 → (finish m c).reg r=m.reg r) := by
  let a := after m addressOps
  let b := saved a c
  have cap : c<2^64 := by unfold capacity at bound;omega
  obtain ⟨v,rv,pv,fv⟩ := address_run o m s pc fits
  obtain ⟨off,dst,am,ar⟩ := address_values m c cap cursor baseReg
  obtain ⟨w,rw,pw,fw⟩ := legs o a c bound v pv fv off dst
  have ptr : b.reg .x13=wordAddress (cell c) := (untouched a c _ (by decide) (by decide) (by decide) (by decide)).trans dst
  obtain ⟨u,ru,pu,fu⟩ := OpeningStraight.block o b (storeOps c) 213 (by change 213+1≤1660;decide)
    (storeTable c) (storeChecks b c bound ptr) w pw fw
  refine ⟨u,CommitExact.compose (CommitExact.compose rv rw) ru,pu,fu,?_,?_⟩
  · have e := finalMemory a c off ((ar _ (by decide) (by decide)).trans zero)
    exact e.trans (congrArg₂ (fun mem v => put mem c 64 v) am (ar _ (by decide) (by decide)))
  · intro r x y p q v w
    exact (untouched a c r p q v w).trans (ar _ x y)

end CommitGolfCandidate.Reconstruction.OpeningSaltLow
