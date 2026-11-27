import CommitGolfCandidate.R4Layers
import CommitGolfCandidate.LateCachedTree
import CommitGolfCandidate.RungAInterface
namespace CommitGolfCandidate.RungA.Upper
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 R4 Late
set_option Elab.async false
set_option maxHeartbeats 1200000
def Levels (H : Compression) (base : Nat→Digest) (d : Nat) (s : MachineState) :=
  ∀ h,4≤h → h≤d → ∀ i<levelCount h, readBuffer s (nodeAddress h i) 32=treeNode H base h i
def Outside (s t : MachineState) :=
  ∀ a n, a+n≤2^64 → (a+n≤5301604576 ∨ 5368714368≤a) → readBuffer t a n=readBuffer s a n

theorem bounds (h i : Nat) (lo : 4≤h) (hi : h≤24) (valid : i<levelCount h) :
    5301604576≤nodeAddress h i ∧ nodeAddress h i+32≤5368714368 := by
  have start:=levelOffset_mono (a:=4) (b:=h) lo
  change 1006633152≤levelOffset h at start
  constructor
  · unfold nodeAddress;omega
  · by_cases last : h=24
    · subst h;change i<1 at valid;have e : i=0:=by omega
      subst i;decide
    · have next:=nodeEnd h i (by omega) valid
      have end_:=levelOffset_mono (a:=h+1) (b:=24) (by omega)
      change levelOffset (h+1)≤1073742912 at end_;omega

theorem outside_fill (o : Oracle) (s : MachineState) (d : Width) (lo : 4≤d.val) :
    Outside s (fillLevel (layerHash o.compression d) d (nodes d) s) := by
  intro a n fits range
  apply fill_preserves _ _ _ _ _ _ le_rfl fits
  intro j hj
  obtain ⟨b,e⟩:=bounds (d.val+1) j (by omega) (by have:=d.isLt;omega) hj
  rcases range with l|r
  · exact Or.inl (l.trans b)
  · exact Or.inr (e.trans r)

theorem currentChild (H : Compression) (base : Nat→Digest) (h p k : Nat) (s : MachineState) (ht : h<24) (hp : p<levelCount (h+1))
    (hk : k<3) (lo : 4≤h) (st : Levels H base h s) (g : Gaps s) :
    readBuffer s (unusedSlotAddr h p k) 32=if k<S4.radix h then treeNode H base h (S4.radix h*p+k) else 0 := by
  by_cases valid : k<S4.radix h
  · rw [if_pos valid]
    by_cases child : S4.radix h*p+k<levelCount h
    · exact (congrArg (fun a=>readBuffer s a 32) (row_slot h p k valid).symm).trans (st h lo le_rfl _ child)
    · rw [missing_node H base h (S4.radix h*p+k) (by omega)];exact g h p k ⟨ht,hp,hk,Or.inr (by omega)⟩
  · rw [if_neg valid];exact g h p k ⟨ht,hp,hk,Or.inl (by omega)⟩

theorem retain_fill (H : Compression) (base : Nat→Digest) (s : MachineState) (d : Nat)
    (ht : d<LOG_LENGTH) (lo : 4≤d) (st : Levels H base d s) (g : Gaps s) :
    Levels H base (d+1) (fillLevel (layerHash H d) d (levelCount (d+1)) s) := by
  intro h bottom limit i hi
  by_cases newRow : h=d+1
  · subst h
    have nodeEq : treeNode H base (d+1) i=layerHash H d (S4.row d (treeNode H base d (S4.radix d*i)) (treeNode H base d (S4.radix d*i+1)) (treeNode H base d (S4.radix d*i+2))) := if_pos hi
    rw [filled_parent _ d (levelCount (d+1)) i s ht le_rfl hi,nodeEq,readTriple s]
    apply congrArg (layerHash H d)
    have one:=currentChild H base d i 0 s ht hi (by decide) lo st g
    have two:=currentChild H base d i 1 s ht hi (by decide) lo st g
    have three:=currentChild H base d i 2 s ht hi (by decide) lo st g
    by_cases z : d=0 <;>
      simp only [unusedSlotAddr,S4.radix,S4.row,z,ite_true,ite_false,Nat.add_zero,Nat.mul_zero,↓reduceIte] at one two three ⊢ <;>
      rw [one,two,three] <;> norm_num <;> rfl
  · have prior : h≤d:=by omega
    have bound:=parent_below_salts h i hi
    exact (fill_preserves _ d _ s _ _ le_rfl (by unfold rowBase at bound;omega)
      (fun j _=>Or.inl (earlier_node d h i j prior ht hi))).trans (st h bottom prior i hi)
end CommitGolfCandidate.RungA.Upper
