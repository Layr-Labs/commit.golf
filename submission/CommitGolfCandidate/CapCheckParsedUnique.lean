import CommitGolfCandidate.CapCheckLoadedRecords

/-! An admitted encoded record list is exactly the list read by the checker
loader. Indices and values come from the ABI; the seventeen proof slots fix
salt and siblings. The arbitrary byte suffix is preserved. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option autoImplicit false
set_option maxHeartbeats 200000

private theorem record_ext (left right : CapLowerRecord)
    (index : left.index=right.index) (value : left.value=right.value)
    (salt : left.salt=right.salt) (siblings : left.sibling=right.sibling) :
    left=right := by
  cases left
  cases right
  simp only [CapLowerRecord.mk.injEq] at *
  exact ⟨index,value,salt,siblings⟩

private theorem encoding_salt (record : CapLowerRecord) :
    (capLowerEncoding record)[0]?.getD 0=record.salt := rfl

private theorem encoding_sibling (record : CapLowerRecord) (level : Fin 16) :
    (capLowerEncoding record)[level.val+1]?.getD 0=record.sibling level := by
  simp only [capLowerEncoding,List.getElem?_cons_succ,List.getElem?_ofFn,
    level.isLt,↓reduceDIte,Option.getD_some]

theorem cap_check_parsed_records_unique (input : CheckInput)
    (records : List CapLowerRecord) (suffix : Proof)
    (parsed : CapCheckParsedRecords input records suffix) :
    capCheckLoadedRecords input=records := by
  apply List.ext_getElem
  · rw [cap_check_loaded_records_length,parsed.length]
  · intro ordinal loadedBound recordBound
    have present : ordinal < input.positions.card := by
      rw [cap_check_loaded_records_length] at loadedBound
      exact loadedBound
    have slots : ∀ slot < 17,
        (capLowerEncoding (capCheckLoadedRecords input)[ordinal])[slot]?.getD 0=
          (capLowerEncoding records[ordinal])[slot]?.getD 0 := by
      intro slot inside
      have loaded := cap_check_loaded_record_slot input ordinal slot present inside
      have encoded := cap_framed_record_slot input
        (capProgram.initialState .check input) records suffix parsed.encoded parsed.admitted
        (fun _ _ _ => rfl) ordinal slot recordBound inside
      exact loaded.symm.trans encoded
    apply record_ext
    · rw [cap_check_loaded_records_element input ordinal present]
      exact (parsed.index ordinal recordBound present).symm
    · rw [cap_check_loaded_records_element input ordinal present]
      exact (parsed.value ordinal recordBound present).symm
    · simpa only [encoding_salt] using slots 0 (by decide)
    · funext level
      simpa only [encoding_sibling] using slots (level.val+1) (by omega)

end CommitGolfCandidate
