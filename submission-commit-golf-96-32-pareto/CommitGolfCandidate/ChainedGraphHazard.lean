import CommitGolfCandidate.ChainedEncoding
import CommitGolfCandidate.Probability

/-! Full-width collision and backward-link targets in a good graph prefix. -/
namespace CommitGolfCandidate.Chained
open CommitGolf OracleComp

def extend {α : Type} {n : Nat} (f : Fin n → α) (value : α) (i : Fin (n+1)) : α :=
  if old : i.val < n then f ⟨i.val,old⟩ else value

theorem extend_injective {α : Type} {n : Nat} (f : Fin n → α) (value : α)
    (injective : Function.Injective f) (fresh : ∀ i, f i ≠ value) :
    Function.Injective (extend f value) := by
  intro i j same
  by_cases hi : i.val < n <;> by_cases hj : j.val < n
  · simp only [extend,dif_pos hi,dif_pos hj] at same
    have eq : (⟨i.val,hi⟩ : Fin n) = ⟨j.val,hj⟩ := injective same
    exact Fin.ext (congrArg (fun k : Fin n => k.val) eq)
  · simp only [extend,dif_pos hi,dif_neg hj] at same
    exact (fresh _ same).elim
  · simp only [extend,dif_neg hi,dif_pos hj] at same
    exact (fresh _ same.symm).elim
  · exact Fin.ext (by have := i.isLt; have := j.isLt; omega)

noncomputable def outputTargets (trace : Trace) : Finset Output :=
  Finset.univ.image trace.output

noncomputable def linkTargets (enc : Encoding) (trace : Trace) : Finset Output := by
  classical
  exact (Finset.univ.filter fun i => (enc.link (trace.input i)).isSome).image
    (fun i => (enc.link (trace.input i)).getD 0)

noncomputable def badTargets (enc : Encoding) (trace : Trace) : Finset Output := by
  classical
  exact outputTargets trace ∪ linkTargets enc trace

theorem output_mem (trace : Trace) (i : Fin trace.size) : trace.output i ∈ outputTargets trace := by
  classical
  exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩

theorem link_mem (enc : Encoding) (trace : Trace) (i : Fin trace.size) (h : Height)
    (j : Nat) (value : Output) (positive : 0 < j) (bounded : j < 16)
    (linked : trace.input i = enc.next h j value) : value ∈ linkTargets enc trace := by
  classical
  have decoded : enc.link (trace.input i) = some value := by
    rw [linked,enc.next_link _ _ _ positive bounded]
  exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp [decoded]⟩,
    by simp [decoded]⟩

theorem badTargets_card (enc : Encoding) (trace : Trace) :
    (badTargets enc trace).card ≤ 2*trace.size := by
  classical
  have outputs : (outputTargets trace).card ≤ trace.size := by
    exact (Finset.card_image_le).trans (by simp)
  have links : (linkTargets enc trace).card ≤ trace.size := by
    exact (Finset.card_image_le).trans ((Finset.card_filter_le _ _).trans (by simp))
  have union := Finset.card_union_le (outputTargets trace) (linkTargets enc trace)
  unfold badTargets
  omega

def Trace.append (trace : Trace) (input : Input) (output : Output)
    (fresh : ∀ i, trace.input i ≠ input) : Trace where
  size := trace.size+1
  input := extend trace.input input
  output := extend trace.output output
  fresh := extend_injective _ _ trace.fresh fresh

theorem good_append (enc : Encoding) (trace : Trace) (good : Good enc trace)
    (input : Input) (output : Output) (fresh : ∀ i, trace.input i ≠ input)
    (safe : output ∉ badTargets enc trace) : Good enc (trace.append input output fresh) := by
  classical
  have notOutput : ∀ i, trace.output i ≠ output := by
    intro i equal
    apply safe
    apply Finset.mem_union.mpr
    exact Or.inl (equal ▸ output_mem trace i)
  refine ⟨extend_injective _ _ good.outputs notOutput,?_⟩
  intro earlier later ordered h j value positive bounded linked
  change (if old : later.val < trace.size then trace.output ⟨later.val,old⟩ else output) ≠ value
  have laterRange : later.val < trace.size+1 := later.isLt
  have earlierOld : earlier.val < trace.size := by omega
  change extend trace.input input earlier = enc.next h j value at linked
  dsimp only [extend] at linked
  rw [dif_pos earlierOld] at linked
  by_cases laterOld : later.val < trace.size
  · rw [dif_pos laterOld]
    exact good.no_guesses ⟨earlier.val,earlierOld⟩ ⟨later.val,laterOld⟩ ordered
      h j value positive bounded linked
  · rw [dif_neg laterOld]
    intro equal
    apply safe
    apply Finset.mem_union.mpr
    apply Or.inr
    rw [equal]
    exact link_mem enc trace ⟨earlier.val,earlierOld⟩ h j value positive bounded linked

theorem fresh_target_probability (enc : Encoding) (trace : Trace) :
    Pr{let output ← $ᵗ Output}[output ∈ badTargets enc trace] ≤
      ((2*trace.size : Nat) : ENNReal)/2^256 := by
  classical
  rw [SampleableType.prEvent_uniformSample]
  have event : (Finset.univ.filter fun output => output ∈ badTargets enc trace) = badTargets enc trace := by
    ext output
    simp
  rw [event,show Fintype.card Output = 2^256 by simp, Nat.cast_pow,Nat.cast_ofNat]
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr (badTargets_card enc trace)) _

theorem good_of_append (enc : Encoding) (trace : Trace) (input : Input) (output : Output)
    (fresh : ∀ i, trace.input i ≠ input) (good : Good enc (trace.append input output fresh)) :
    Good enc trace := by
  refine ⟨?_,?_⟩
  · intro i j same
    have shared : (trace.append input output fresh).output i.castSucc =
        (trace.append input output fresh).output j.castSucc := by
      simpa only [Trace.append,extend,Fin.val_castSucc,dif_pos i.isLt,dif_pos j.isLt] using same
    have eq := good.outputs shared
    exact Fin.ext (congrArg (fun k : Fin (trace.size+1) => k.val) eq)
  · intro earlier later ordered h j value positive bounded linked
    have extended : (trace.append input output fresh).input earlier.castSucc = enc.next h j value := by
      simpa only [Trace.append,extend,Fin.val_castSucc,dif_pos earlier.isLt] using linked
    have safe := good.no_guesses earlier.castSucc later.castSucc ordered h j value positive bounded extended
    simpa only [Trace.append,extend,Fin.val_castSucc,dif_pos later.isLt] using safe

end CommitGolfCandidate.Chained
