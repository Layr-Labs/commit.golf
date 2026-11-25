import CommitGolfCandidate.TwoPermutationPackedRecordInterface

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate CommitGolfCandidate.ShortTree RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (RecordInputFrame checkSourceWord honestIndex
  record_input_value checker_positions_bound)
open TwoPermutationPrototype.PackedCertificate (honestCheckInput)
open TwoPermutationPrototype.PackedHonest (honestHeap honest_input_nonce honest_input_full_sibling
  honest_input_later_sibling honest_projected_node)
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

theorem packed_record_full_sibling (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (ordinal : Nat) (present : ordinal<positions.card) (state : MachineState)
    (framed : RecordInputFrame (honestCheckInput oracle message positions salts) ordinal state)
    (level : Nat) (inside : level<9) :
    readBuffer state (checkProofByte ordinal+16+32*level) 32 =
      honestHeap oracle message salts (Opening.lowerNode (honestIndex positions ordinal present) level ^^^ 1) := by
  let input := honestCheckInput oracle message positions salts
  have card := checker_positions_bound input
  have fit : checkProofByte ordinal+(16+32*level)+32 ≤ 2^36 := by
    change positions.card ≤ 16777216 at card
    unfold checkProofByte
    omega
  have frame := record_proof_frame input ordinal (16+32*level) 32 state framed (Nat.le_of_lt present) fit
  have loaded := honest_input_full_sibling oracle message positions salts ordinal level present inside
  rw [PackedChecker.initial_state] at loaded
  have addr : PackedChecker.submission.layout.proof+(514*ordinal+16+32*level)=checkProofByte ordinal+(16+32*level) := by
    change 10334769248+(514*ordinal+16+32*level)=10334769248+514*ordinal+(16+32*level)
    omega
  rw [addr] at loaded
  rw [Nat.add_assoc]
  exact frame.trans loaded

theorem packed_record_later_sibling (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (ordinal : Nat) (present : ordinal < positions.card) (state : MachineState)
    (framed : RecordInputFrame (honestCheckInput oracle message positions salts) ordinal state)
    (sibling : Nat) (later : sibling < 7) :
    readBuffer state (checkProofByte ordinal+304+30*sibling) 30 =
      (honestHeap oracle message salts (Opening.lowerNode (honestIndex positions ordinal present) (sibling+9) ^^^ 1)).extractLsb' 0 240 := by
  let input := honestCheckInput oracle message positions salts
  have card := checker_positions_bound input
  have fit : checkProofByte ordinal+(304+30*sibling)+30 ≤ 2^36 := by
    change positions.card ≤ 16777216 at card
    unfold checkProofByte
    omega
  have frame := record_proof_frame input ordinal (304+30*sibling) 30 state framed (Nat.le_of_lt present) fit
  have loaded := honest_input_later_sibling oracle message positions salts ordinal sibling present later
  rw [PackedChecker.initial_state] at loaded
  have addr : PackedChecker.submission.layout.proof+(514*ordinal+304+30*sibling) =
      checkProofByte ordinal+(304+30*sibling) := by
    change 10334769248+(514*ordinal+304+30*sibling) = 10334769248+514*ordinal+(304+30*sibling)
    omega
  rw [addr] at loaded
  rw [Nat.add_assoc]
  exact frame.trans loaded

theorem packed_honest_heap_climb (oracle : Oracle) (leaves : DigestTape) (node : Nat)
    (positive : 2 ≤ node) (bounded : node < 2*LENGTH) :
    let heap := Hybrid.heap oracle.compression leaves
    Hybrid.normalize (node/2) (oracle.compression (pathPair node (heap node) (heap (node ^^^ 1)))) = heap (node/2) := by
  let heap := Hybrid.heap oracle.compression leaves
  change Hybrid.normalize (node/2) (oracle.compression (pathPair node (heap node) (heap (node ^^^ 1)))) = heap (node/2)
  have parent := Hybrid.heap_parent oracle.compression leaves (node/2) ⟨by omega,by omega⟩
  change heap (node/2) = Hybrid.normalize (node/2) (oracle.compression (heap (2*(node/2)+1) ++ heap (2*(node/2)))) at parent
  rw [parent]
  by_cases even : node % 2 = 0
  · rw [pathPair, ite_eq_left even, Nat.xor_one_of_even (Nat.even_iff.mpr even)]
    rw [show 2*(node/2)+1 = node+1 by omega,show 2*(node/2) = node by omega]
  · have odd : Odd node := Nat.odd_iff.mpr (by omega)
    rw [pathPair, ite_eq_right even, Nat.xor_one_of_odd odd]
    rw [show 2*(node/2)+1 = node by omega,show 2*(node/2) = node-1 by omega]

end TwoPermutationPrototype.Packed.Checker
