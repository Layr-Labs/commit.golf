import CommitGolfCandidate.CapCheckLoadedRecords
import CommitGolfCandidate.InputOrder

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option autoImplicit false

theorem cap_check_loaded_record_for_position (input : CheckInput) (index : Index)
    (member : index ∈ input.positions) :
    ∃ record ∈ capCheckLoadedRecords input,
      record.index=index ∧ record.value=input.values ⟨index,member⟩ := by
  have inList : (⟨index,member⟩ : {i // i ∈ input.positions}) ∈
      input.positions.attach.sort (fun i j => i.val≤j.val) := by simp
  obtain ⟨ordinal,bound,same⟩ := List.mem_iff_getElem.mp inList
  have present : ordinal < input.positions.card := by simpa using bound
  refine ⟨capCheckLoadedRecord input ⟨ordinal,present⟩,?_,?_,?_⟩
  · exact List.mem_ofFn.mpr ⟨⟨ordinal,present⟩,rfl⟩
  · apply Fin.ext
    have order := sorted_value_index input.positions ordinal present
    rw [same] at order
    simpa only [capCheckLoadedRecord,openingIndex,dif_pos present] using order.symm
  · simp only [capCheckLoadedRecord,same]

end CommitGolfCandidate
