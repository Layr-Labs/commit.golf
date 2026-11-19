import CommitGolfCandidate.QuadHonestInput
import CommitGolfCandidate.QuadLowerCertificate

namespace TwoPermutationPrototype.Quad.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate CommitGolfCandidate.ShortTree RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (honestIndex)
open TwoPermutationPrototype.Quad.Honest (honestHeap honest_input_nonce honest_input_first_sibling
  honest_input_later_sibling honest_projected_node)
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

theorem quad_record_first_sibling (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (ordinal : Nat) (present : ordinal < positions.card) (state : MachineState)
    (framed : RecordInputFrame (honestCheckInput oracle message positions salts) ordinal state) :
    readBuffer state (checkProofByte ordinal+208) 32 =
      honestHeap oracle message salts (((LENGTH+(honestIndex positions ordinal present).val.val)/16) ^^^ 1) := by
  let input := honestCheckInput oracle message positions salts
  have card := checker_positions_bound input
  have fit : checkProofByte ordinal+208+32 ≤ 2^36 := by
    change positions.card ≤ 16777216 at card
    unfold checkProofByte
    omega
  have frame := record_proof_frame input ordinal 208 32 state framed (Nat.le_of_lt present) fit
  have loaded := honest_input_first_sibling oracle message positions salts ordinal present
  have addr : loaderReference.layout.proof+(570*ordinal+208) = checkProofByte ordinal+208 := by
    change 11190423648+(570*ordinal+208) = 11190423648+570*ordinal+208
    omega
  rw [addr] at loaded
  exact frame.trans loaded

theorem quad_record_later_sibling (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (ordinal : Nat) (present : ordinal < positions.card) (state : MachineState)
    (framed : RecordInputFrame (honestCheckInput oracle message positions salts) ordinal state)
    (sibling : Nat) (later : sibling < 11) :
    readBuffer state (checkProofByte ordinal+240+30*sibling) 30 =
      (honestHeap oracle message salts (lowerNode (honestIndex positions ordinal present) (sibling+1) ^^^ 1)).extractLsb' 0 240 := by
  let input := honestCheckInput oracle message positions salts
  have card := checker_positions_bound input
  have fit : checkProofByte ordinal+(240+30*sibling)+30 ≤ 2^36 := by
    change positions.card ≤ 16777216 at card
    unfold checkProofByte
    omega
  have frame := record_proof_frame input ordinal (240+30*sibling) 30 state framed (Nat.le_of_lt present) fit
  have loaded := honest_input_later_sibling oracle message positions salts ordinal sibling present later
  have addr : loaderReference.layout.proof+(570*ordinal+240+30*sibling) =
      checkProofByte ordinal+(240+30*sibling) := by
    change 11190423648+(570*ordinal+240+30*sibling) = 11190423648+570*ordinal+(240+30*sibling)
    omega
  rw [addr] at loaded
  rw [Nat.add_assoc]
  exact frame.trans loaded


theorem quad_record_child (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (ordinal child : Nat) (present : ordinal<positions.card) (which : child<3)
    (state : MachineState) (framed : RecordInputFrame (honestCheckInput oracle message positions salts) ordinal state) :
    readBuffer state (checkProofByte ordinal+16+32*child) 32 =
      quadLeaf (Honest.honestLeaves oracle message salts) (honestIndex positions ordinal present)
        (quadRotSlot (honestIndex positions ordinal present) child) := by
  let input := honestCheckInput oracle message positions salts
  have card := checker_positions_bound input
  have fit : checkProofByte ordinal+(16+32*child)+32≤2^36 := by
    change positions.card≤16777216 at card
    unfold checkProofByte
    omega
  have frame := record_proof_frame input ordinal (16+32*child) 32 state framed (Nat.le_of_lt present) fit
  have loaded := Honest.honest_input_child oracle message positions salts ordinal child present which
  have addr : loaderReference.layout.proof+(570*ordinal+16+32*child)=checkProofByte ordinal+(16+32*child) := by
    change 11190423648+(570*ordinal+16+32*child)=11190423648+570*ordinal+(16+32*child)
    omega
  rw [addr] at loaded
  rw [Nat.add_assoc]
  exact frame.trans loaded

theorem quad_record_quad_child (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (ordinal child : Nat) (present : ordinal<positions.card) (which : child<3)
    (state : MachineState) (framed : RecordInputFrame (honestCheckInput oracle message positions salts) ordinal state) :
    readBuffer state (checkProofByte ordinal+112+32*child) 32 =
      quadValue (Honest.honestQuad oracle) (Honest.honestLeaves oracle message salts)
        (quad2Neighbour (honestIndex positions ordinal present) child) := by
  let input := honestCheckInput oracle message positions salts
  have card := checker_positions_bound input
  have fit : checkProofByte ordinal+(112+32*child)+32≤2^36 := by
    change positions.card≤16777216 at card
    unfold checkProofByte
    omega
  have frame := record_proof_frame input ordinal (112+32*child) 32 state framed (Nat.le_of_lt present) fit
  have loaded := Honest.honest_input_quad_child oracle message positions salts ordinal child present which
  have addr : loaderReference.layout.proof+(570*ordinal+112+32*child)=checkProofByte ordinal+(112+32*child) := by
    change 11190423648+(570*ordinal+112+32*child)=11190423648+570*ordinal+(112+32*child)
    omega
  rw [addr] at loaded
  rw [Nat.add_assoc]
  exact frame.trans loaded

private theorem later_quad_sibling_internal (index : Index) (level : Nat) (later : 0<level) (within : level<12) :
    0<lowerNode index level ^^^ 1 ∧ lowerNode index level ^^^ 1<LENGTH/16 := by
  let node := lowerNode index level
  have lo : 2≤node := (quad_lower_node_range index level within).1
  have scale : 32≤(2:Nat)^(level+4) := by
    exact (show 32=(2:Nat)^5 by decide) ▸ Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (by omega)
  have hi : node<1048576 := by
    apply (Nat.div_lt_iff_lt_mul (by positivity : 0<(2:Nat)^(level+4))).mpr
    change 16777216+index.val<1048576*2^(level+4)
    have indexBound := index.isLt
    change index.val<16777216 at indexBound
    omega
  change 0<node ^^^ 1 ∧ node ^^^ 1<1048576
  by_cases even : node%2=0
  · rw [Nat.xor_one_of_even (Nat.even_iff.mpr even)]
    omega
  · rw [Nat.xor_one_of_odd (Nat.odd_iff.mpr (by omega))]
    omega

theorem canonical_lower_wire_sibling (oracle : Oracle) (message : Message)
    (positions : Positions) (salts : CompleteSaltTape) (ordinal : Nat) (present : ordinal<positions.card)
    (state : MachineState) (framed : RecordInputFrame (honestCheckInput oracle message positions salts) ordinal state)
    (level : Nat) (within : level<12) :
    lowerWireSibling state ordinal level=
      honestHeap oracle message salts (lowerNode (honestIndex positions ordinal present) level ^^^ 1) := by
  by_cases first : level=0
  · subst level
    simpa only [lowerWireSibling,ite_true,lowerNode,Opening.lowerNode,Nat.reduceAdd,Nat.reducePow] using
      quad_record_first_sibling oracle message positions salts ordinal present state framed
  · rw [lowerWireSibling,ite_eq_right first]
    let slot := level-1
    have restored : slot+1=level := by unfold slot; omega
    have actual := quad_record_later_sibling oracle message positions salts ordinal present state framed slot (by
      unfold slot
      omega)
    rw [restored] at actual
    rw [actual]
    obtain ⟨lo,hi⟩ := later_quad_sibling_internal (honestIndex positions ordinal present) level (by omega) within
    exact Honest.honest_projected_node _ _ _ _ lo hi

end TwoPermutationPrototype.Quad.Checker
