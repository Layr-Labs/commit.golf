import CommitGolfCandidate.ReconstructedLeafPreserve

namespace CommitGolfCandidate.Reconstruction.LeafCarry
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype (Memory Words window writeWindow writeWord)
open LeafCode LeafModel LeafMacros CommitWindows LeafSpill LeafContent LeafPrelude Generator LeafLane LeafSource LeafDigest LeafPreserve

theorem block_next (i j : Index) (succ : j.val=i.val+1) (inside : (laneOf j).val≠0) :
    tileOf i=tileOf j ∧ groupOf i=groupOf j ∧ (laneOf j).val=(laneOf i).val+1 ∧ baseSalt i=baseSalt j := by
  change j.val%4096%12 ≠ 0 at inside
  have nz : j.val%4096 ≠ 0 := by intro h; simp [h] at inside
  have tile : i.val/4096 = j.val/4096 := by omega
  have step : j.val%4096=i.val%4096+1 := by omega
  have group : (i.val%4096)/12=(j.val%4096)/12 := by rw [step] at inside ⊢; omega
  have lane : j.val%4096%12=i.val%4096%12+1 := by omega
  refine ⟨Fin.ext tile,Fin.ext group,lane,?_⟩
  change 512+32*i.val-15-32*(i.val%4096%12)=512+32*j.val-15-32*(j.val%4096%12)
  omega

theorem continuity (i j : Index) (succ : j.val=i.val+1) :
    wordAddress (p i) = wordAddress (entryStart j-25) := by
  congr 1
  simp only [p,entryStart]
  omega

theorem anchor_next (i j : Index) (succ : j.val=i.val+1) (inside : slot i+1<4096) :
    center i = beforeCenter j := by
  have t := target i
  have u := target j
  have l : location j = location i+4 := by unfold location; omega
  have step : slot j=slot i+1 := by unfold slot at *; omega
  unfold beforeCenter
  by_cases h : LeafLane.shift j
  · rw [if_pos h]; have z := h.2; omega
  · rw [if_neg h]; have nz : slot j%63≠0 := by intro q; exact h ⟨by omega,q⟩
    omega

theorem anchor_tile (i j : Index) (succ : j.val=i.val+1) (last : slot i+1=4096) :
    center i+4 = beforeCenter j := by
  have t := target i
  have u := target j
  have l : location j = location i+4 := by unfold location; omega
  have si : slot i=4095 := by omega
  have sj : slot j=0 := by unfold slot at *; omega
  have none : ¬LeafLane.shift j := fun h => h.1 sj
  rw [beforeCenter,if_neg none]
  rw [si] at t
  rw [sj] at u
  omega

theorem next_enter (o : Oracle) (m : Model) (i j : Index) (e : Enter m i) (succ : j.val=i.val+1)
    (inside : slot i+1<4096) : Enter (result o m i) j := by
  refine ⟨result_fixed _ _ _ e.toFixed,(result_ptr ..).trans (continuity i j succ),?_⟩
  rw [result_read _ _ _ _ (by decide) (by decide) (by decide) (by decide),center_staged _ _ _ e,anchor_next _ _ succ inside]

theorem scratch_front (o : Oracle) (m : Model) (k : Key) (msg : Message) (i : Index) (ok : Ready o m k msg i)
    (front : (laneOf i).val=0) (j : Fin 14) :
    (result o m i).mem (baseSalt i+j.val) = tapeWord o k i ⟨j.val,by omega⟩ := by
  let w := baseSalt i+j.val
  have geom : baseSalt i = entryStart i-15 := by simp [baseSalt,front]
  have lim := limits i
  have J := j.isLt
  have below : w < location i := by dsimp [w]; rw [geom]; unfold location; omega
  have a : w ≠ p i := by dsimp [w]; rw [geom]; unfold p; omega
  have b : w ≠ p i+2 := by dsimp [w]; rw [geom]; unfold p; omega
  change (result o m i).mem w = _
  rw [finished _ _ _ _ _ ok.enter ok.pre ok.counter ok.scratch, outside _ _ _ _ (.inl below),
    zero_mem _ _ _ _ _ ok.enter front ok.pre ok.counter]
  change writeWord (writeWord _ (p i) _) (p i+2) _ w = _
  simp only [writeWord,b,a,ite_false]
  change generatedFirst _ _ _ _ (baseSalt i+j.val) = _
  rw [geom]
  exact tape_slot _ _ _ _ ⟨j.val,by omega⟩

theorem registers_front (o : Oracle) (m : Model) (k : Key) (msg : Message) (i : Index) (ok : Ready o m k msg i)
    (front : (laneOf i).val=0) (full : (groupOf i).val<341) (j : Fin 8) :
    (result o m i).reg (saved j.val) = tapeWord o k i ⟨14+j.val,by omega⟩ := by
  let g := groupOf i
  let s := entryStart i
  have one (r : Reg) (h : ∀ z : Fin 8, saved z.val ≠ r) := h j
  rw [result_read _ _ _ _ (one _ (by decide)) (one _ (by decide)) (one _ (by decide)) (one _ (by decide))]
  simp only [staged,rebase_other _ _ _ (one _ (by decide : ∀ z : Fin 8, saved z.val ≠ .x19)),grouped,front,ite_true,
    after_group_saved _ _ _ _ full j]
  have mem := group_mem o m k msg i ok.enter front ok.pre ok.counter
  simp only [grouped,front,ite_true,after_group_mem] at mem
  rw [mem]
  have same : entryStart i-15+14+j.val = entryStart i-15+(14+j.val) := Nat.add_assoc .. 
  rw [same]
  exact tape_slot _ _ _ _ ⟨14+j.val,by omega⟩

theorem next_scratch (o : Oracle) (m : Model) (k : Key) (msg : Message) (i j : Index) (ok : Ready o m k msg i)
    (succ : j.val=i.val+1) : Scratch o k (result o m i) j := by
  have shared (nz : (laneOf j).val≠0) (q : Fin 25) : tapeWord o k i q = tapeWord o k j q := by
    obtain ⟨t,g,_,_⟩ := block_next i j succ nz
    simp only [tapeWord,tapeReply,t,g]
  have lim := limits i
  constructor
  · intro nz q
    obtain ⟨_,_,_,same⟩ := block_next i j succ nz
    rw [←same,←shared nz]
    by_cases front : (laneOf i).val=0
    · exact scratch_front _ _ _ _ _ ok front q
    · have Q := q.isLt
      have below : baseSalt i+q.val < entryStart i-15 := by
        have geom := salt_coord i; unfold p at geom; omega
      have lower : baseSalt i+q.val < location i := by unfold location; omega
      rw [memory_frame _ _ _ _ _ ok _ (.inl below) (.inl lower),origin,if_neg front]
      exact ok.scratch.words front q
  · intro nz full q
    obtain ⟨_,grp,_,_⟩ := block_next i j succ nz
    rw [←shared nz]
    have fi : (groupOf i).val<341 := grp ▸ full
    by_cases front : (laneOf i).val=0
    · exact registers_front _ _ _ _ _ ok front fi q
    · have one (r : Reg) (h : ∀ z : Fin 8, saved z.val ≠ r) := h q
      rw [result_read _ _ _ _ (one _ (by decide)) (one _ (by decide)) (one _ (by decide)) (one _ (by decide))]
      simp only [staged,rebase_other _ _ _ (one _ (by decide : ∀ z : Fin 8, saved z.val ≠ .x19)),
        grouped,front,ite_false]
      exact ok.scratch.registers front fi q

end CommitGolfCandidate.Reconstruction.LeafCarry
