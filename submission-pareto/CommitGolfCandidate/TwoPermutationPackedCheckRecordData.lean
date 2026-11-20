import CommitGolfCandidate.TwoPermutationPackedRecordInterface

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate CommitGolfCandidate.ShortTree RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (RecordInputFrame checkSourceWord honestIndex
  record_input_value checker_positions_bound)
open TwoPermutationPrototype.QuartetCertificate (honestCheckInput)
open TwoPermutationPrototype.Sampling.Quartet (upperHeap leafAt packEight pack_eight_length)
open TwoPermutationPrototype.PackedHonest (honestHeap honestLeaves honest_input_nonce honest_input_first_sibling
  honest_input_second_sibling honest_input_mid_sibling honest_input_packed_byte honest_input_quartet_sibling
  honest_input_admitted honest_input_records_fit honest_projected_node)
set_option maxRecDepth 8192
set_option maxHeartbeats 1100000

theorem packed_record_nonce (oracle : Oracle) (message : Message) (positions : Positions) (salts : CompleteSaltTape)
    (ordinal : Nat) (present : ordinal < positions.card) (state : MachineState)
    (framed : RecordInputFrame (honestCheckInput oracle message positions salts) ordinal state) :
    readBuffer state (checkProofByte ordinal) 16 = salts (honestIndex positions ordinal present) := by
  let input := honestCheckInput oracle message positions salts
  have card := checker_positions_bound input
  have fit : checkProofByte ordinal+0+16 ≤ 2^36 := by
    change positions.card ≤ 16777216 at card
    unfold checkProofByte
    omega
  have frame := record_proof_frame input ordinal 0 16 state framed (Nat.le_of_lt present) fit
  have loaded := honest_input_nonce oracle message positions salts ordinal present
  rw [PackedChecker.initial_state] at loaded
  rw [Nat.add_zero] at frame
  exact frame.trans loaded

theorem packed_record_quartet_sibling (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (ordinal slot : Nat) (present : ordinal < positions.card) (valid : slot < 3)
    (state : MachineState)
    (framed : RecordInputFrame (honestCheckInput oracle message positions salts) ordinal state) :
    readBuffer state (checkProofByte ordinal+(16+32*slot)) 32 =
      leafAt (honestLeaves oracle message salts) ((honestIndex positions ordinal present).val.val ^^^ (slot+1)) := by
  let input := honestCheckInput oracle message positions salts
  have card := checker_positions_bound input
  have fit : checkProofByte ordinal+(16+32*slot)+32 ≤ 2^36 := by
    change positions.card ≤ 16777216 at card
    unfold checkProofByte
    omega
  have frame := record_proof_frame input ordinal (16+32*slot) 32 state framed (Nat.le_of_lt present) fit
  have loaded := honest_input_quartet_sibling oracle message positions salts ordinal slot present valid
  rw [PackedChecker.initial_state] at loaded
  have addr : PackedChecker.submission.layout.proof+(534*ordinal+16+32*slot) = checkProofByte ordinal+(16+32*slot) := by
    change 13824430176+(534*ordinal+16+32*slot) = 13824430176+534*ordinal+(16+32*slot)
    omega
  rw [addr] at loaded
  exact frame.trans loaded

theorem packed_record_first_sibling (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (ordinal : Nat) (present : ordinal < positions.card) (state : MachineState)
    (framed : RecordInputFrame (honestCheckInput oracle message positions salts) ordinal state) :
    readBuffer state (checkProofByte ordinal+112) 32 =
      honestHeap oracle message salts (Opening.lowerNode (QuartetCheck.flipIndex (honestIndex positions ordinal present).val) 2 ^^^ 1) := by
  let input := honestCheckInput oracle message positions salts
  have card := checker_positions_bound input
  have fit : checkProofByte ordinal+112+32 ≤ 2^36 := by
    change positions.card ≤ 16777216 at card
    unfold checkProofByte
    omega
  have frame := record_proof_frame input ordinal 112 32 state framed (Nat.le_of_lt present) fit
  have loaded := honest_input_first_sibling oracle message positions salts ordinal present
  rw [PackedChecker.initial_state] at loaded
  have addr : PackedChecker.submission.layout.proof+(534*ordinal+112) = checkProofByte ordinal+112 := by
    change 13824430176+(534*ordinal+112) = 13824430176+534*ordinal+112
    omega
  rw [addr] at loaded
  exact frame.trans loaded

theorem packed_record_second_sibling (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (ordinal : Nat) (present : ordinal < positions.card) (state : MachineState)
    (framed : RecordInputFrame (honestCheckInput oracle message positions salts) ordinal state) :
    readBuffer state (checkProofByte ordinal+144) 32 =
      honestHeap oracle message salts (Opening.lowerNode (QuartetCheck.flipIndex (honestIndex positions ordinal present).val) 3 ^^^ 1) := by
  let input := honestCheckInput oracle message positions salts
  have card := checker_positions_bound input
  have fit : checkProofByte ordinal+144+32 ≤ 2^36 := by
    change positions.card ≤ 16777216 at card
    unfold checkProofByte
    omega
  have frame := record_proof_frame input ordinal 144 32 state framed (Nat.le_of_lt present) fit
  have loaded := honest_input_second_sibling oracle message positions salts ordinal present
  rw [PackedChecker.initial_state] at loaded
  have addr : PackedChecker.submission.layout.proof+(534*ordinal+144) = checkProofByte ordinal+144 := by
    change 13824430176+(534*ordinal+144) = 13824430176+534*ordinal+144
    omega
  rw [addr] at loaded
  exact frame.trans loaded

/-- The 30-byte sibling of loop level `slot+2` (`slot < 4`). -/
theorem packed_record_mid_sibling (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (ordinal : Nat) (present : ordinal < positions.card) (state : MachineState)
    (framed : RecordInputFrame (honestCheckInput oracle message positions salts) ordinal state)
    (slot : Nat) (valid : slot < 4) :
    readBuffer state (checkProofByte ordinal+176+30*slot) 30 =
      (honestHeap oracle message salts (Opening.lowerNode (QuartetCheck.flipIndex (honestIndex positions ordinal present).val) (slot+4) ^^^ 1)).extractLsb' 0 240 := by
  let input := honestCheckInput oracle message positions salts
  have card := checker_positions_bound input
  have fit : checkProofByte ordinal+(176+30*slot)+30 ≤ 2^36 := by
    change positions.card ≤ 16777216 at card
    unfold checkProofByte
    omega
  have frame := record_proof_frame input ordinal (176+30*slot) 30 state framed (Nat.le_of_lt present) fit
  have loaded := honest_input_mid_sibling oracle message positions salts ordinal slot present valid
  rw [PackedChecker.initial_state] at loaded
  have addr : PackedChecker.submission.layout.proof+(534*ordinal+176+30*slot) =
      checkProofByte ordinal+(176+30*slot) := by
    change 13824430176+(534*ordinal+176+30*slot) = 13824430176+534*ordinal+(176+30*slot)
    omega
  rw [addr] at loaded
  rw [Nat.add_assoc]
  exact frame.trans loaded

/-- The packed block of loop levels `6..13`, byte by byte: GQ's `packEight` of the honest siblings. -/
theorem packed_record_block_byte (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (ordinal : Nat) (present : ordinal < positions.card) (state : MachineState)
    (framed : RecordInputFrame (honestCheckInput oracle message positions salts) ordinal state)
    (offset : Nat) (inside : offset < 238) :
    state.getByte (BitVec.ofNat 64 (checkProofByte ordinal+296+offset)) =
      (packEight ((List.range 8).map (fun k =>
        honestHeap oracle message salts (Opening.lowerNode (QuartetCheck.flipIndex (honestIndex positions ordinal present).val) (k+8) ^^^ 1))))[offset]! := by
  let input := honestCheckInput oracle message positions salts
  have card := checker_positions_bound input
  have fit : checkProofByte ordinal+296+238 ≤ 2^36 := by
    change positions.card ≤ 16777216 at card
    unfold checkProofByte
    omega
  have frame := record_proof_frame input ordinal 296 238 state framed (Nat.le_of_lt present) fit
  have after := read_buffer_byte state (checkProofByte ordinal+296) 238 offset inside
  have before := read_buffer_byte (QAssembly.submission.initialState .check input) (checkProofByte ordinal+296) 238
    offset inside
  rw [← after, frame, before]
  have enough := honest_input_records_fit oracle message positions salts
  have bounded : 534*ordinal+296+offset < input.proof.length := by
    change 534*ordinal+296+offset < (honestCheckInput oracle message positions salts).proof.length
    have more : 534*(ordinal+1) ≤ 534*positions.card := Nat.mul_le_mul_left _ present
    omega
  have byte := PackedChecker.check_input_proof_byte input (honest_input_admitted oracle message positions salts)
    (534*ordinal+296+offset) bounded
  rw [PackedChecker.initial_state] at byte
  have addr : PackedChecker.submission.layout.proof+(534*ordinal+296+offset) = checkProofByte ordinal+296+offset := by
    change 13824430176+(534*ordinal+296+offset) = 13824430176+534*ordinal+296+offset
    omega
  rw [addr] at byte
  rw [byte]
  have packed := honest_input_packed_byte oracle message positions salts ordinal offset present inside
  rw [List.getElem?_eq_getElem bounded, List.getElem?_eq_getElem (by rw [pack_eight_length]; exact inside),
    Option.some_inj] at packed
  rw [getElem!_pos _ _ (by rw [pack_eight_length]; exact inside)]
  exact packed

theorem packed_honest_heap_climb (oracle : Oracle) (message : Message) (salts : CompleteSaltTape) (node : Nat)
    (positive : 2 ≤ node) (bounded : node < 8388608) :
    let heap := honestHeap oracle message salts
    nodeKeep (node/2) (oracle.compression (pathPair node (heap node) (heap (node ^^^ 1)))) = heap (node/2) :=
  QuartetCheck.upper_heap_climb _ _ _ node positive bounded

end TwoPermutationPrototype.Packed.Checker
