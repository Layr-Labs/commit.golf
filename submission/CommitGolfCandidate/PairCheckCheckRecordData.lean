-- Pair-heads copy of TwoPermutationPackedCheckRecordData (stack/check/work/mkcopy.py); edits below are marked PAIR.
import CommitGolfCandidate.PairCheckRecordInterface
import CommitGolfCandidate.PairCheckModel
import CommitGolfCandidate.PairCheckNamespaces

namespace TwoPermutationPrototype.PairCk.Packed.Checker
open  TwoPermutationPrototype.Packed TwoPermutationPrototype.Packed.Checker TwoPermutationPrototype.PairCk.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate CommitGolfCandidate.ShortTree RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (RecordInputFrame checkSourceWord honestIndex
  record_input_value checker_positions_bound)
open TwoPermutationPrototype.PairCertificate (pairHonestCheckInput)
open TwoPermutationPrototype.Sampling.Quartet (upperHeap leafAt)
open TwoPermutationPrototype.PairCk.PackedHonest (honestHeap honestLeaves honest_input_nonce honest_input_first_sibling
  honest_input_later_sibling honest_input_quartet_sibling honest_projected_node)
set_option maxRecDepth 8192
set_option maxHeartbeats 1100000

theorem packed_record_nonce (oracle : Oracle) (message : Message) (positions : Positions) (salts : CompleteSaltTape)
    (ordinal : Nat) (present : ordinal < positions.card) (state : MachineState)
    (framed : RecordInputFrame (pairHonestCheckInput oracle message positions salts) ordinal state) :
    readBuffer state (checkProofByte ordinal) 16 = salts (honestIndex positions ordinal present) := by
  let input := pairHonestCheckInput oracle message positions salts
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
    (framed : RecordInputFrame (pairHonestCheckInput oracle message positions salts) ordinal state) :
    readBuffer state (checkProofByte ordinal+(16+32*slot)) 32 =
      leafAt (honestLeaves oracle message salts) ((honestIndex positions ordinal present).val.val ^^^ (slot+1)) := by
  let input := pairHonestCheckInput oracle message positions salts
  have card := checker_positions_bound input
  have fit : checkProofByte ordinal+(16+32*slot)+32 ≤ 2^36 := by
    change positions.card ≤ 16777216 at card
    unfold checkProofByte
    omega
  have frame := record_proof_frame input ordinal (16+32*slot) 32 state framed (Nat.le_of_lt present) fit
  have loaded := honest_input_quartet_sibling oracle message positions salts ordinal slot present valid
  rw [PackedChecker.initial_state] at loaded
  have addr : PackedChecker.submission.layout.proof+(534*ordinal+16+32*slot) = checkProofByte ordinal+(16+32*slot) := by
    change 11676946528+(534*ordinal+16+32*slot) = 11676946528+534*ordinal+(16+32*slot)
    omega
  rw [addr] at loaded
  exact frame.trans loaded

theorem packed_record_first_sibling (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (ordinal : Nat) (present : ordinal < positions.card) (state : MachineState)
    (framed : RecordInputFrame (pairHonestCheckInput oracle message positions salts) ordinal state) :
    readBuffer state (checkProofByte ordinal+112) 32 =
      honestHeap oracle message salts (Opening.lowerNode (honestIndex positions ordinal present).val 2 ^^^ 1) := by
  let input := pairHonestCheckInput oracle message positions salts
  have card := checker_positions_bound input
  have fit : checkProofByte ordinal+112+32 ≤ 2^36 := by
    change positions.card ≤ 16777216 at card
    unfold checkProofByte
    omega
  have frame := record_proof_frame input ordinal 112 32 state framed (Nat.le_of_lt present) fit
  have loaded := honest_input_first_sibling oracle message positions salts ordinal present
  rw [PackedChecker.initial_state] at loaded
  have addr : PackedChecker.submission.layout.proof+(534*ordinal+112) = checkProofByte ordinal+112 := by
    change 11676946528+(534*ordinal+112) = 11676946528+534*ordinal+112
    omega
  rw [addr] at loaded
  exact frame.trans loaded

theorem packed_record_later_sibling (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (ordinal : Nat) (present : ordinal < positions.card) (state : MachineState)
    (framed : RecordInputFrame (pairHonestCheckInput oracle message positions salts) ordinal state)
    (sibling : Nat) (later : sibling < 13) :
    readBuffer state (checkProofByte ordinal+144+30*sibling) 30 =
      (honestHeap oracle message salts (Opening.lowerNode (honestIndex positions ordinal present) (sibling+3) ^^^ 1)).extractLsb' 0 240 := by
  let input := pairHonestCheckInput oracle message positions salts
  have card := checker_positions_bound input
  have fit : checkProofByte ordinal+(144+30*sibling)+30 ≤ 2^36 := by
    change positions.card ≤ 16777216 at card
    unfold checkProofByte
    omega
  have frame := record_proof_frame input ordinal (144+30*sibling) 30 state framed (Nat.le_of_lt present) fit
  have loaded := honest_input_later_sibling oracle message positions salts ordinal sibling present later
  rw [PackedChecker.initial_state] at loaded
  have addr : PackedChecker.submission.layout.proof+(534*ordinal+144+30*sibling) =
      checkProofByte ordinal+(144+30*sibling) := by
    change 11676946528+(534*ordinal+144+30*sibling) = 11676946528+534*ordinal+(144+30*sibling)
    omega
  rw [addr] at loaded
  rw [Nat.add_assoc]
  exact frame.trans loaded

theorem packed_honest_heap_climb (oracle : Oracle) (message : Message) (salts : CompleteSaltTape) (node : Nat)
    (positive : 2 ≤ node) (bounded : node < 8388608) :
    let heap := honestHeap oracle message salts
    padLow (oracle.compression (pathPair node (heap node) (heap (node ^^^ 1)))) = heap (node/2) :=
  QuartetCheck.upper_heap_climb _ _ _ node positive bounded

end TwoPermutationPrototype.PairCk.Packed.Checker
