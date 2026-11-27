import CommitGolfCandidate.QuadHonestInput

/-! Honest record fields, read in a machine state that frames the remaining proof. -/
namespace TwoPermutationPrototype.Quad.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (honestIndex)
open TwoPermutationPrototype.Quad.Honest (honest_input_nonce honest_input_sibling honest_input_virt)
set_option maxRecDepth 8192
set_option maxHeartbeats 1100000

theorem quad_record_nonce (oracle : Oracle) (message : Message) (positions : Positions) (salts : CompleteSaltTape)
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
  rw [Nat.add_zero] at frame
  exact frame.trans loaded

theorem quad_record_virt (oracle : Oracle) (message : Message) (positions : Positions) (salts : CompleteSaltTape)
    (ordinal : Nat) (present : ordinal < positions.card) (state : MachineState)
    (framed : RecordInputFrame (honestCheckInput oracle message positions salts) ordinal state) :
    readBuffer state (checkProofByte ordinal+16) 8 =
      BitVec.ofNat 64 (virtIndex (honestIndex positions ordinal present).val.val) := by
  let input := honestCheckInput oracle message positions salts
  have card := checker_positions_bound input
  have fit : checkProofByte ordinal+16+8 ≤ 2^36 := by
    change positions.card ≤ 16777216 at card
    unfold checkProofByte
    omega
  have frame := record_proof_frame input ordinal 16 8 state framed (Nat.le_of_lt present) fit
  have loaded := honest_input_virt oracle message positions salts ordinal present
  have addr : loaderReference.layout.proof+(1560*ordinal+16) = checkProofByte ordinal+16 := by
    change 10804535392+(1560*ordinal+16)=10804535392+1560*ordinal+16
    omega
  rw [addr] at loaded
  exact frame.trans loaded

theorem quad_record_sibling (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (ordinal level child : Nat) (present : ordinal<positions.card)
    (deep : level<PENTA_LEVELS) (which : child<4)
    (state : MachineState) (framed : RecordInputFrame (honestCheckInput oracle message positions salts) ordinal state) :
    readBuffer state (checkProofByte ordinal+(24+128*level+32*child)) 32 =
      pentaGroup (Honest.honestPenta oracle) (Honest.honestLeaves oracle message salts) level
        ((honestIndex positions ordinal present).val.val / placeValue (level + 1))
        (pentaRot (honestIndex positions ordinal present) level child) := by
  let input := honestCheckInput oracle message positions salts
  have card := checker_positions_bound input
  have deep' : level < 12 := deep
  have fit : checkProofByte ordinal+(24+128*level+32*child)+32≤2^36 := by
    change positions.card≤16777216 at card
    unfold checkProofByte
    omega
  have frame := record_proof_frame input ordinal (24+128*level+32*child) 32 state framed (Nat.le_of_lt present) fit
  have loaded := honest_input_sibling oracle message positions salts ordinal level child present deep which
  have addr : loaderReference.layout.proof+(1560*ordinal+24+128*level+32*child)=
      checkProofByte ordinal+(24+128*level+32*child) := by
    change 10804535392+(1560*ordinal+24+128*level+32*child)=10804535392+1560*ordinal+(24+128*level+32*child)
    omega
  rw [addr] at loaded
  exact frame.trans loaded

end TwoPermutationPrototype.Quad.Checker
