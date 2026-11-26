import CommitGolfCandidate.S5TreeFrame
import CommitGolfCandidate.S5LeafMemory
namespace CommitGolfCandidate.S5Machine
open CommitGolf Chained CommitGolf.Riscv RiscvZkvm.Rv64

theorem salt_limits (i : Index) : rowBase≤saltAddress i.val ∧ saltAddress i.val+24≤scratchBase := by
  have hi:=i.isLt;change i.val<16777216 at hi
  unfold saltAddress rowBase scratchBase;split <;> omega

theorem node_tag {d i : Nat} {h : Height} {p : Nat} (hd : d≤24) (hi : i<levelCount d)
    (inside : p<count h) (cut : chained h) : Apart (nodeAddress d i) 32 (tagAddr h p) 8 := by
  have pad:=gap_pad inside (by unfold chained at cut;omega)
  have bound:=node_pad d i h.val p 2 hd hi pad
  change nodeAddress d i+32≤tagAddr h p ∨ tagAddr h p+32≤nodeAddress d i at bound
  unfold Apart;omega

private theorem keep_node {s t H h p} (eff : NodeEffect H h p s t) (inside : p<count h)
    (d i : Nat) (hd : d≤24) (hi : i<levelCount d) (apart : Apart (nodeAddress d i) 32 (nodeAddress (h.val+1) p) 32) :
    readBuffer t (nodeAddress d i) 32=readBuffer s (nodeAddress d i) 32 := by
  have bound:=parent_below_salts _ _ hi
  apply eff.outside _ _ (by change _≤2^36;unfold rowBase at bound;omega) apart
  exact fun cut=>⟨node_tag hd hi inside cut,Or.inl (bound.trans (by decide))⟩

theorem node_frame {s t H h p base salt} (old : TreeState H base salt h.val s) (eff : NodeEffect H h p s t)
    (inside : p<count h) : TreeState H base salt h.val t := by
  have ht:=h.isLt
  have hh : h.val+1≤24:=by omega
  constructor
  · intro d bound i hi
    exact (keep_node eff inside _ _ (by omega) hi
      (distinct_nodes (by omega) hh hi inside (Or.inl (by omega)))).trans (old.nodes _ bound _ hi)
  · intro i
    have b:=salt_limits i
    have dst:=parent_below_salts _ _ inside
    have tag:=gap_limit _ _ inside
    exact (eff.outside _ _ (b.2.trans (by decide)) (Or.inr (by omega))
      (fun _=>⟨Or.inr (by omega),Or.inl b.2⟩)).trans (old.salts i)
  · intro d j k pad
    obtain ⟨high,low⟩:=old.pads _ _ _ pad
    have bound:=padValid d j k pad
    have nd:=node_pad (h.val+1) p d j k hh inside pad
    have baseAligned : (unusedSlotAddr d j k)%8=0 := by unfold unusedSlotAddr;have :=rowAligned d j;omega
    have cellTag {cut : chained h} (different : h.val≠d ∨ p≠j ∨ 2≠k) :
        Apart (tagAddr h p) 32 (unusedSlotAddr d j k) 32 :=
      cell_apart ht pad.height inside pad.within (by decide : 2<3) pad.lane different
    constructor
    · apply (eff.outside _ 24 (by change _≤2^36;unfold rowBase at bound;omega) (by unfold Apart;omega) ?_).trans high
      intro cut;constructor
      · by_cases same : h.val=d ∧ p=j ∧ k=2
        · obtain ⟨rfl,rfl,rfl⟩:=same;right;change tagAddr h p+8≤tagAddr h p+8;rfl
        · have e:=cellTag (cut:=cut) (by tauto)
          unfold Apart at *;omega
      · left;unfold scratchBase rowBase at *;omega
    · intro no;apply (eff.outside _ 8 (by change _≤2^36;unfold rowBase at bound;omega) (by unfold Apart;omega) ?_).trans (low no)
      intro cut;have e:=cellTag (cut:=cut) (by unfold chained at cut;omega)
      constructor
      · unfold Apart at *;omega
      · left;unfold scratchBase rowBase at *;omega

theorem physical_child {s H h base salt} (st : TreeState H base salt h.val s) (p k : Nat) (inside : p<count h)
    (valid : k<S4.radix h.val) :
    physicalChild s h.val p k=treeNode H base h.val (S4.radix h.val*p+k) := by
  by_cases exists_ : S4.radix h.val*p+k<levelCount h.val
  · exact (congrArg (fun a=>readBuffer s a 32) (row_slot h.val p k valid).symm).trans (st.nodes _ le_rfl _ exists_)
  · have pad : Padding h.val p k := ⟨h.isLt,inside,by unfold S4.radix at valid;split at valid <;> omega,Or.inr (by omega)⟩
    obtain ⟨high,low⟩:=st.pads _ _ _ pad
    have plain : ¬(8≤h.val ∧ h.val<16 ∧ k=2) := by unfold S4.radix at valid;split at valid <;> omega
    rw [missing_node _ _ _ _ (by omega)]
    have eq:=read_join s (unusedSlotAddr h.val p k) 8 24
    change _ ++ _ = (physicalChild s h.val p k).extractLsb' 0 256 at eq
    rw [high,low plain,BitVec.extractLsb'_eq_self] at eq
    exact eq.symm

theorem grow_row {s t H h p base salt} (old : TreeState H base salt h.val s)
    (built : doneRows H base h.val p s) (effect : NodeEffect H h p s t) (inside : p<count h) :
    doneRows H base h.val (p+1) t := by
  intro j hj
  have ht:=h.isLt
  by_cases same : j=p
  · subst j;rw [effect.value,treeNode,if_pos (show p<levelCount (h.val+1) from inside)]
    have first:=physical_child old p 0 inside (by unfold S4.radix;split <;> decide)
    have second:=physical_child old p 1 inside (by unfold S4.radix;split <;> decide)
    simp only [Nat.add_zero] at first
    rw [first,second]
    by_cases bottom : h.val=0
    · have third:=physical_child old p 2 inside (by simp [S4.radix,bottom])
      rw [third]
    · simp [nodeHash,bottom]
  · have jp : j<p := by omega
    have hi : j<levelCount (h.val+1):=jp.trans inside
    exact (keep_node effect inside _ _ (by omega) hi
      (distinct_nodes (by omega) (by omega) hi inside (Or.inr same))).trans (built j jp)

theorem close_level {H h base salt s} (before : TreeState H base salt h.val s)
    (built : doneRows H base h.val (count h) s) : TreeState H base salt (h.val+1) s := by
  refine ⟨?_,before.salts,before.pads⟩
  intro k hk i hi;by_cases same : k=h.val+1
  · subst k;exact built _ hi
  · exact before.nodes _ (by omega) _ hi
end CommitGolfCandidate.S5Machine
