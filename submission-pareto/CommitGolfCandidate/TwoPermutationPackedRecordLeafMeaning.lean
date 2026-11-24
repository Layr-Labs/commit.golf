import CommitGolfCandidate.TaggedPinnedModel
import CommitGolfCandidate.TwoPermutationPackedRecordLeafBlock

namespace TwoPermutationPrototype.Packed.RecordLeaf
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Packed.Checker
open TwoPermutationPrototype.Checker (RecordInputFrame honestIndex checkSourceWord
  checker_positions_bound aligned_buffer_frame buffer_window checker_value_data record_input_value
  beginRecord record_setup_register)
open TwoPermutationPrototype.QuartetCertificate (honestCheckInput)
set_option maxRecDepth 8192
set_option maxHeartbeats 1300000

theorem staged_entry_words (input : CheckInput) (ordinal : Nat) (present : ordinal < input.positions.card)
    (before : MachineState) (fits : ProofWithin input) (cursor : RecordCursor input ordinal before)
    (framed : RecordInputFrame input ordinal before) :
    window (memoryView (staged before)) (checkSourceWord ordinal+5) =
      entryWords (input.values (honestIndex input.positions ordinal present)) := by
  let item := honestIndex input.positions ordinal present
  have card := checker_positions_bound input
  have stable := aligned_buffer_frame before (staged before) (checkSourceWord ordinal+5) 32 (by
    intro j within
    apply staged_word_frame input ordinal present before fits cursor
    · unfold checkSourceWord
      omega
    · exact Or.inr (by unfold checkSourceWord; omega))
  exact checker_value_data (fun _ => input.values item) item.val
    (stable.trans (record_input_value input ordinal present before framed))

theorem staged_honest_nonce_words (oracle : Oracle) (input : CheckInput) (ordinal : Nat)
    (present : ordinal < input.positions.card) (before : MachineState) (fits : ProofWithin input)
    (cursor : RecordCursor input ordinal before) (framed : RecordInputFrame input ordinal before)
    (message : Message) (salts : CompleteSaltTape)
    (canonical : NearHonest input (honestCheckInput oracle message input.positions salts)) :
    checkerNonce (staged before) = saltWords (salts (honestIndex input.positions ordinal present)) := by
  have stagedPtr : (staged before).getReg .x4 = wordAddress 1534 := by
    unfold staged
    rw [copy_field_register _ _ _ (by decide),record_setup_register _ _ (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact cursor.nonceScratch
  have raw := packed_record_nonce oracle message input.positions salts ordinal present before canonical framed
  have copied := (staged_nonce_read input ordinal present before fits cursor).trans raw
  rw [checker_nonce_words _ 1534 stagedPtr,buffer_window (staged before) 1534 2]
  change (fun i : Fin 2 => (readBuffer (staged before) 12272 16).extractLsb' (64*i.val) 64) = _
  rw [copied]
  rfl

theorem canonical_entry_value (oracle : Oracle) (input : CheckInput) (message : Message)
    (salts : CompleteSaltTape) (item : {index // index ∈ input.positions})
    (canonical : NearHonest input (honestCheckInput oracle message input.positions salts)) :
    input.values item = message item.val := by
  let lookup (record : CheckInput) : Entry :=
    if present : item.val ∈ record.positions then record.values ⟨item.val,present⟩ else 0
  obtain ⟨P, same, _, _⟩ := canonical
  have transported := congrArg lookup same
  have present : item.val ∈ ({ honestCheckInput oracle message input.positions salts with proof := P } :
    CheckInput).positions := item.property
  dsimp only [lookup] at transported
  rw [dif_pos item.property,dif_pos present] at transported
  exact transported

theorem honest_row_digest (oracle : Oracle) (message : Message) (salts : CompleteSaltTape) (index : Index) :
    pinnedLeafDigest oracle.permutation index (saltWords (salts index)) (entryWords (message index)) =
      pinnedFullLeafDigests (BiPermutation.equiv Block oracle.permutation) message salts index := by
  rfl

/-! ### Both leaf kinds -/

theorem raw_message_words (input : CheckInput) (ordinal : Nat) (present : ordinal < input.positions.card)
    (before : MachineState) (fits : ProofWithin input) (cursor : RecordCursor input ordinal before)
    (framed : RecordInputFrame input ordinal before) :
    rawMessage ordinal (honestIndex input.positions ordinal present).val before =
      entryWords (input.values (honestIndex input.positions ordinal present)) := by
  by_cases ahead : isAHead (honestIndex input.positions ordinal present).val = true
  · have emem := (a_entry_post before (record_entry_pc input ordinal present before cursor)
      (a_rank input ordinal present before cursor framed ahead)).2.1
    rw [show rawMessage ordinal (honestIndex input.positions ordinal present).val before =
      window (memoryView (aEntry before)) (checkSourceWord ordinal+5) from if_pos ahead]
    have stable : readBuffer (aEntry before) (8*(checkSourceWord ordinal+5)) 256 =
        readBuffer before (8*(checkSourceWord ordinal+5)) 256 := read_buffer_memory_congr _ _ emem _ _
    exact checker_value_data (fun _ => input.values (honestIndex input.positions ordinal present))
      (honestIndex input.positions ordinal present).val
      (stable.trans (record_input_value input ordinal present before framed))
  · rw [show rawMessage ordinal (honestIndex input.positions ordinal present).val before =
      window (memoryView (staged (sfPre before))) (checkSourceWord ordinal+5) from if_neg ahead]
    exact staged_entry_words input ordinal present (sfPre before) fits (sf_cursor input ordinal before cursor)
      (sf_framed input ordinal before framed)

theorem raw_nonce_honest (oracle : Oracle) (input : CheckInput) (ordinal : Nat)
    (present : ordinal < input.positions.card) (before : MachineState) (fits : ProofWithin input)
    (cursor : RecordCursor input ordinal before) (framed : RecordInputFrame input ordinal before)
    (message : Message) (salts : CompleteSaltTape)
    (canonical : NearHonest input (honestCheckInput oracle message input.positions salts)) :
    rawNonce (honestIndex input.positions ordinal present).val before =
      saltWords (salts (honestIndex input.positions ordinal present)) := by
  by_cases ahead : isAHead (honestIndex input.positions ordinal present).val = true
  · have ready := a_ready input ordinal present before fits cursor framed ahead
    have emem := (a_entry_post before (record_entry_pc input ordinal present before cursor)
      (a_rank input ordinal present before cursor framed ahead)).2.1
    rw [show rawNonce (honestIndex input.positions ordinal present).val before =
      checkerNonce (aStaged (aEntry before)) from if_pos ahead]
    have x4 : (aStaged (aEntry before)).getReg .x4 = wordAddress 1534 := by
      rw [a_staged_register .x4 (by decide) (by decide) (by decide) (by decide) (by decide), ready.scratch]; rfl
    have raw := packed_record_nonce oracle message input.positions salts ordinal present before canonical framed
    have copied := (a_staged_read ready).trans ((read_buffer_memory_congr _ _ emem _ _).trans raw)
    rw [checker_nonce_words _ 1534 x4, buffer_window (aStaged (aEntry before)) 1534 2]
    change (fun i : Fin 2 => (readBuffer (aStaged (aEntry before)) 12272 16).extractLsb' (64*i.val) 64) = _
    rw [copied]
    rfl
  · rw [show rawNonce (honestIndex input.positions ordinal present).val before =
      checkerNonce (staged (sfPre before)) from if_neg ahead]
    exact staged_honest_nonce_words oracle input ordinal present (sfPre before) fits
      (sf_cursor input ordinal before cursor) (sf_framed input ordinal before framed) message salts canonical

end TwoPermutationPrototype.Packed.RecordLeaf
