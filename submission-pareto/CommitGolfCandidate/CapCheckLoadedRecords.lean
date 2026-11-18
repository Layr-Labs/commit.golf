import CommitGolfCandidate.CapCheckRecordsAgreement
import CommitGolfCandidate.CapOpenEncoding

/-! Read the complete lower-record prefix from the actual checker loader.
The remaining bytes are kept verbatim, including a partial trailing digest.
The construction fixes each index/value from the ABI and only salt/siblings
from proof memory (salt, three group digests, fourteen siblings); it performs no oracle calls or early tail-length rejection. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false

def capCheckLoadedRecord (input : CheckInput) (ordinal : Fin input.positions.card) :
    CapLowerRecord :=
  ⟨(input.positions.sort (· ≤ ·))[ordinal.val]'(by simpa using ordinal.isLt),
    input.values ((input.positions.attach.sort (fun i j => i.val≤j.val))[ordinal.val]'(by
      simpa using ordinal.isLt)),
    readBuffer (capProgram.initialState .check input)
      (capProgram.layout.proof+576*ordinal.val) 32,
    fun place => readBuffer (capProgram.initialState .check input)
      (capProgram.layout.proof+576*ordinal.val+32*(place.val+1)) 32,
    fun level => readBuffer (capProgram.initialState .check input)
      (capProgram.layout.proof+576*ordinal.val+32*(level.val+4)) 32⟩

def capCheckLoadedRecords (input : CheckInput) : List CapLowerRecord :=
  List.ofFn (capCheckLoadedRecord input)

theorem cap_check_loaded_records_length (input : CheckInput) :
    (capCheckLoadedRecords input).length=input.positions.card := by
  exact List.length_ofFn

theorem cap_check_loaded_records_element (input : CheckInput) (ordinal : Nat)
    (inside : ordinal < input.positions.card) :
    (capCheckLoadedRecords input)[ordinal]'(by
      rw [cap_check_loaded_records_length]; exact inside)=
      capCheckLoadedRecord input ⟨ordinal,inside⟩ := by
  exact List.getElem_ofFn _

theorem cap_check_loaded_record_slot (input : CheckInput) (ordinal slot : Nat)
    (present : ordinal < input.positions.card) (inside : slot<18) :
    readBuffer (capProgram.initialState .check input)
      (capProgram.layout.proof+576*ordinal+32*slot) 32=
      (capLowerEncoding ((capCheckLoadedRecords input)[ordinal]'(by
        rw [cap_check_loaded_records_length]; exact present)))[slot]?.getD 0 := by
  rw [cap_check_loaded_records_element input ordinal present,
    List.getElem?_eq_getElem (by rw [cap_lower_encoding_length]; exact inside),Option.getD_some]
  by_cases zero : slot=0
  · subst slot
    rw [cap_lower_encoding_salt]
    simp only [capCheckLoadedRecord,Nat.mul_zero,Nat.add_zero]
  · by_cases low : slot<4
    · have shape := cap_lower_encoding_other (capCheckLoadedRecord input ⟨ordinal,present⟩)
        ⟨slot-1,by omega⟩
      simp only [show slot-1+1=slot by omega] at shape
      rw [shape]
      simp only [capCheckLoadedRecord,show slot-1+1=slot by omega]
    · have shape := cap_lower_encoding_sibling (capCheckLoadedRecord input ⟨ordinal,present⟩)
        ⟨slot-4,by omega⟩
      simp only [show slot-4+4=slot by omega] at shape
      rw [shape]
      simp only [capCheckLoadedRecord,show slot-4+4=slot by omega]

theorem cap_check_loaded_transcript_slot (input : CheckInput) (ordinal : Nat)
    (present : ordinal<(capLowerTranscript (capCheckLoadedRecords input)).length) :
    readBuffer (capProgram.initialState .check input)
      (capProgram.layout.proof+32*ordinal) 32=
      (capLowerTranscript (capCheckLoadedRecords input))[ordinal] := by
  have row : ordinal/18 < input.positions.card := by
    rw [cap_lower_transcript_length,cap_check_loaded_records_length] at present
    omega
  have column : ordinal%18<18 := Nat.mod_lt _ (by decide)
  have recordPresent : ordinal/18<(capCheckLoadedRecords input).length := by
    rw [cap_check_loaded_records_length]; exact row
  have same : 18*(ordinal/18)+ordinal%18=ordinal := by omega
  have address : capProgram.layout.proof+576*(ordinal/18)+32*(ordinal%18)=
      capProgram.layout.proof+32*ordinal := by omega
  have slot := cap_check_loaded_record_slot input (ordinal/18) (ordinal%18) row column
  rw [address] at slot
  rw [← cap_transcript_slot _ _ _ recordPresent column,same,
    List.getElem?_eq_getElem present,Option.getD_some] at slot
  exact slot

theorem cap_check_loaded_records_prefix (input : CheckInput)
    (admitted : input.proof.length≤capProgram.sizes.proof)
    (enough : 576*input.positions.card ≤ input.proof.length) :
    input.proof.take (576*input.positions.card)=
      capDigestEncoding (capLowerTranscript (capCheckLoadedRecords input)) := by
  have encodingLength :
      (capDigestEncoding (capLowerTranscript (capCheckLoadedRecords input))).length=
        576*input.positions.card := by
    rw [cap_digest_encoding_length,cap_lower_transcript_length,
      cap_check_loaded_records_length]
    omega
  apply List.ext_getElem
  · rw [List.length_take,Nat.min_eq_left enough,encodingLength]
  · intro offset leftBound rightBound
    have inside : offset<576*input.positions.card := by
      rw [encodingLength] at rightBound; exact rightBound
    have proofPresent : offset < input.proof.length := by omega
    have bytes := cap_slots_encoding (capProgram.initialState .check input)
      capProgram.layout.proof (capLowerTranscript (capCheckLoadedRecords input))
      (cap_check_loaded_transcript_slot input) offset (by
        rw [cap_lower_transcript_length,cap_check_loaded_records_length]
        omega)
    rw [cap_check_input_proof_byte input offset admitted proofPresent,
      List.getElem?_eq_getElem proofPresent,Option.getD_some,
      List.getElem?_eq_getElem rightBound,Option.getD_some] at bytes
    simpa only [List.getElem_take] using bytes

theorem cap_check_loaded_records_parsed (input : CheckInput)
    (admitted : input.proof.length≤capProgram.sizes.proof)
    (enough : 576*input.positions.card ≤ input.proof.length) :
    CapCheckParsedRecords input (capCheckLoadedRecords input)
      (input.proof.drop (576*input.positions.card)) := by
  refine ⟨?_,admitted,cap_check_loaded_records_length input,?_,?_⟩
  · rw [← cap_check_loaded_records_prefix input admitted enough,List.take_append_drop]
  · intro ordinal inside present
    rw [cap_check_loaded_records_element input ordinal present]
    rfl
  · intro ordinal inside present
    rw [cap_check_loaded_records_element input ordinal present]
    rfl

end CommitGolfCandidate
