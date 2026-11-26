import CommitGolfCandidate.ReconstructedLeafLane
import CommitGolfCandidate.ReconstructedLeafCodeReceipts

namespace CommitGolfCandidate.Reconstruction.LeafLane
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.RV64
open LeafCode LeafModel LeafMacros CommitWindows LeafSpill LeafContent LeafPrelude Generator

theorem pointed_read (o : Oracle) (m : Model) (i : Index) (r : Reg) (a : r ≠ .x10) (b : r ≠ .x12) :
    (pointed o m i).reg r = (staged o m i).reg r := by
  dsimp only [pointed]
  split <;> simp [rawState,Model.set,Model.permute,Ne.symm a,Ne.symm b]

theorem salted_read (o : Oracle) (m : Model) (i : Index) (r : Reg) (a : r ≠ .x6) (b : r ≠ .x7) :
    (salted o m i).reg r = (pointed o m i).reg r := by
  dsimp only [salted]
  split
  · rfl
  split <;> simp [nearState,stamp,Model.store,Model.set,Ne.symm a,Ne.symm b,tagged]

theorem result_read (o : Oracle) (m : Model) (i : Index) (r : Reg)
    (a : r ≠ .x6) (b : r ≠ .x7) (c : r ≠ .x10) (d : r ≠ .x12) :
    (result o m i).reg r = (staged o m i).reg r := by
  change ((salted o m i).set .x12 (wordAddress (location i))).reg r = _
  simp only [Model.set,Ne.symm d,false_and,ite_false,salted_read _ _ _ _ a b,pointed_read _ _ _ _ c d]

theorem result_ptr (o : Oracle) (m : Model) (i : Index) :
    (result o m i).reg .x10 = wordAddress (p i) := by
  change (salted o m i).reg .x10 = _
  rw [salted_read _ _ _ _ (by decide) (by decide),pointed_ptr]

theorem center_staged (o : Oracle) (m : Model) (i : Index) (e : Enter m i) :
    (staged o m i).reg .x19 = wordAddress (center i) :=
  rebase_center _ _ ((grouped_read _ _ _ _ (by decide) (by decide) (by decide)).trans e.anchor)

theorem result_fixed (o : Oracle) (m : Model) (i : Index) (e : Fixed m) : Fixed (result o m i) := by
  constructor
  all_goals rw [result_read o m i _ (by decide) (by decide) (by decide) (by decide),
    staged_read o m i _ (by decide) (by decide) (by decide) (by decide)]
  exacts [e.mode,e.base,e.len,e.kind,e.ones]

/-- All instructions executed for this leaf, including the optional salt generation and
heap-pointer shift. The result is independent of the state parts absent from the model. -/
theorem body_run (o : Oracle) (m : Model) (i : Index) (e : Enter m i) :
    Contract o (body (slot i)) m (result o m i) := by
  let g := grouped o m i
  let a := staged o m i
  let b := pointed o m i
  let c := tagged o m i
  let d := salted o m i
  let k : Fin 63 := ⟨slot i%63,by omega⟩
  have lim := limits i
  have srcRoom : entryStart i+32 ≤ 2^33 := by unfold heapBase at lim; omega
  have s1 : Contract o (if (laneOf i).val=0 then groupSetup (groupOf i).val else []) m g := by
    dsimp only [g,grouped]
    split
    · exact group o m _ _ (by omega) srcRoom e.ptr e.toFixed
    · exact LeafModel.empty _ _
  have s2 : Contract o (rebase (slot i)) g a := rebase_step _ _ _
    ((grouped_read _ _ _ _ (by decide) (by decide) (by decide)).trans e.anchor)
  have ds (r : Reg) (u : ∀ j : Fin 8, saved j.val ≠ r)
      (six : r ≠ .x6) (seven : r ≠ .x7) (ten : r ≠ .x10) (twelve : r ≠ .x12) (nineteen : r ≠ .x19) :
      d.reg r = m.reg r := (salted_read o m i r six seven).trans
        ((pointed_read o m i r ten twelve).trans (staged_read o m i r u ten twelve nineteen))
  have last := LeafMacros.finish o d (p i) (center i) k (by unfold p; omega)
    (by change center i+4*(slot i%63)+25 ≤ 2^33; rw [target]; unfold generatorBase at lim; omega)
    ((salted_read o m i _ (by decide) (by decide)).trans (pointed_ptr ..))
    ((salted_read o m i _ (by decide) (by decide)).trans
      ((pointed_read o m i _ (by decide) (by decide)).trans (center_staged o m i e)))
    ((ds _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans e.mode)
    ((ds _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans e.len)
    ((ds _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans e.kind)
    ((ds _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans e.ones)
  change Contract o (finishCode k) d (finishState o d (p i) (center i+4*(slot i%63))) at last
  rw [target] at last
  have all := LeafModel.combine (LeafModel.combine (LeafModel.combine
    (LeafModel.combine (LeafModel.combine s1 s2) (point o m i e)) (tag o m i)) (nonce o m i)) last
  have eqops :
      ((if (laneOf i).val=0 then groupSetup (groupOf i).val else []) ++ rebase (slot i) ++ pointingCode i ++
        [.SD .x10 .x10 0] ++ saltLoad (laneOf i).val ++ finishCode k) = body (slot i) := by
    unfold body pointingCode
    by_cases zero : i.val%4096%12 = 0 <;>
      simp only [laneOf,groupOf,slot,zero,ite_true,ite_false,rawCode,finishCode,k,List.cons_append,List.nil_append]
  rw [←eqops]
  exact all

theorem machine_lane (o : Oracle) (m : Model) (i : Index) (e : Enter m i) (s : MachineState)
    (fits : Fits s m) (pc : s.pc = CommitBlocks.addr (start (slot i))) :
    ∃ t, CommitExact.Segment o CommitSetup.im (body (slot i)).length s t ∧
      Fits t (result o m i) ∧ t.pc = CommitBlocks.addr
      (if slot i+1=4096 then 53012 else start (slot i+1)) := by
  obtain ⟨t,run,ht⟩ := body_run o m i e s fits
  have cert := body_verified ⟨slot i,by unfold slot; omega⟩
  change goodLane (slot i) = true at cert
  simp only [goodLane,Bool.and_eq_true,decide_eq_true_eq] at cert
  exact ⟨t,run.segment _ pc cert.1,ht,(run.next_pc _ pc).trans (congrArg CommitBlocks.addr cert.2)⟩

end CommitGolfCandidate.Reconstruction.LeafLane
