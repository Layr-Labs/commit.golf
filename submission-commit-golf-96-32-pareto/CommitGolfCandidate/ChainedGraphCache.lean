import CommitGolfCandidate.ChainedCompletion
import CommitGolfCandidate.CompressionROM

/-! The chronological compression graph projects to the ordinary lazy cache. -/
namespace CommitGolfCandidate.Chained.Trace
open CommitGolf OracleComp OracleSpec

abbrev CacheSpec := Input →ₒ Output

noncomputable def cache (trace : Trace) : CacheSpec.QueryCache := by
  classical
  exact ⟨fun input => if found : ∃ i, trace.input i = input then
    some (trace.output (Classical.choose found)) else none⟩

theorem cache_row (trace : Trace) (row : Fin trace.size) :
    trace.cache (trace.input row) = some (trace.output row) := by
  classical
  let found : ∃ i, trace.input i = trace.input row := ⟨row,rfl⟩
  change (if found : ∃ i, trace.input i = trace.input row then
    some (trace.output (Classical.choose found)) else none) = _
  rw [dif_pos found]
  exact congrArg (some ∘ trace.output) (trace.fresh (Classical.choose_spec found))

theorem cache_none_iff (trace : Trace) (input : Input) :
    trace.cache input = none ↔ ¬ ∃ i, trace.input i = input := by
  classical
  change (if found : ∃ i, trace.input i = input then
    some (trace.output (Classical.choose found)) else none) = none ↔ _
  by_cases found : ∃ i, trace.input i = input <;> simp [found]

theorem cache_of_row (trace : Trace) (row : Fin trace.size) (input : Input) (same : trace.input row = input) :
    trace.cache input = some (trace.output row) := by
  subst input
  exact cache_row trace row

noncomputable def keys (trace : Trace) : Finset Input := by
  classical
  exact Finset.univ.image trace.input

theorem mem_keys (trace : Trace) (input : Input) : input ∈ trace.keys ↔ ∃ i, trace.input i = input := by
  classical
  simp [keys]

theorem keys_card (trace : Trace) : trace.keys.card = trace.size := by
  classical
  rw [keys,Finset.card_image_of_injective _ trace.fresh]
  simp

theorem cache_covers (trace : Trace) (input : Input) (populated : trace.cache input ≠ none) :
    input ∈ trace.keys := by
  rw [mem_keys]
  by_contra missing
  exact populated ((cache_none_iff trace input).mpr missing)

theorem cache_append (trace : Trace) (input : Input) (reply : Output) (fresh : ∀ i, trace.input i ≠ input) :
    (trace.append input reply fresh).cache = trace.cache.cacheQuery input reply := by
  classical
  apply QueryCache.ext
  intro key
  by_cases same : key=input
  · subst key
    rw [QueryCache.cacheQuery_self]
    have atInput : (trace.append input reply fresh).input (Fin.last trace.size) = input := by simp [append,extend]
    have atOutput : (trace.append input reply fresh).output (Fin.last trace.size) = reply := by simp [append,extend]
    exact ((trace.append input reply fresh).cache_of_row _ input atInput).trans (congrArg some atOutput)
  · rw [QueryCache.cacheQuery_of_ne _ _ same]
    by_cases found : ∃ i, trace.input i = key
    · obtain ⟨row,equal⟩ := found
      have old := trace.cache_of_row row key equal
      have atInput : (trace.append input reply fresh).input row.castSucc = key := by
        simpa only [append,extend,Fin.val_castSucc,dif_pos row.isLt] using equal
      have atOutput : (trace.append input reply fresh).output row.castSucc = trace.output row := by
        simp only [append,extend,Fin.val_castSucc,dif_pos row.isLt]
      have new : (trace.append input reply fresh).cache key = some (trace.output row) := by
        exact ((trace.append input reply fresh).cache_of_row _ key atInput).trans (congrArg some atOutput)
      exact new.trans old.symm
    · have missing : ¬ ∃ i, (trace.append input reply fresh).input i = key := by
        rintro ⟨row,equal⟩
        change extend trace.input input row = key at equal
        unfold extend at equal
        split at equal
        · exact found ⟨_,equal⟩
        · exact same equal.symm
      rw [(cache_none_iff _ _).mpr missing,(cache_none_iff _ _).mpr found]

theorem keys_append (trace : Trace) (input : Input) (reply : Output) (fresh : ∀ i, trace.input i ≠ input) :
    (trace.append input reply fresh).keys = insert input trace.keys := by
  classical
  ext key
  simp only [Finset.mem_insert,mem_keys]
  constructor
  · rintro ⟨row,equal⟩
    by_cases old : row.val < trace.size
    · right
      exact ⟨⟨row.val,old⟩,by simpa only [append,extend,dif_pos old] using equal⟩
    · left
      have new : input = key := by simpa only [append,extend,dif_neg old] using equal
      exact new.symm
  · rintro (rfl | ⟨row,equal⟩)
    · exact ⟨Fin.last trace.size,by simp [append,extend]⟩
    · exact ⟨row.castSucc,by simpa only [append,extend,Fin.val_castSucc,dif_pos row.isLt] using equal⟩

end CommitGolfCandidate.Chained.Trace
