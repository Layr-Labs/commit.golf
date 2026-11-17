import CommitGolfCandidate.CapCheckPathMemory
import CommitGolfCandidate.CapCheckPathOutcome

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] readBuffer capCheckPathBlockState capCheckPathPreparedState
  capCheckPathLoop checkEvaluation

private theorem low_bit_zero (index : Word) :
    (index &&& 1 = 0) ↔ index.getLsbD 0 = false := by
  change (index &&& 1#64 = 0#64) ↔ _
  rw [BitVec.and_one_eq_setWidth_ofBool_getLsbD]
  cases h : index.getLsbD 0 <;> simp [BitVec.ofBool]

theorem cap_check_path_loop_digest (oracle : Oracle) (state : MachineState)
    (address : Nat) (path : List (Bool × Digest))
    (scratch : state.getReg .x21 = 256)
    (pointer : state.getReg .x25 = BitVec.ofNat 64 address)
    (aligned : address % 8 = 0) (above : 320 ≤ address)
    (bounded : address + 32 * path.length < 2^64)
    (data : ∀ i (hi : i < path.length), readBuffer state (address + 32*i) 32 = (path[i]'hi).2)
    (directions : ∀ i (hi : i < path.length), (state.getReg .x20).getLsbD i = (path[i]'hi).1) :
    readBuffer (checkEvaluation oracle (capCheckPathLoop state path.length)).1 256 32 =
      climb oracle.compression (readBuffer state 256 32) path := by
  induction path generalizing state address with
  | nil => simp [capCheckPathLoop, check_evaluation_pure, climb]
  | cons pair rest ih =>
    rcases pair with ⟨right, sibling⟩
    have input := cap_check_path_input state address scratch pointer aligned above (by simp only [List.length_cons] at bounded; omega)
    have headData := data 0 (by simp)
    have headDirection := directions 0 (by simp)
    simp only [Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero] at headData headDirection
    simp only [headData, low_bit_zero, headDirection] at input
    let answer := if right then
      combine oracle.compression sibling (readBuffer state 256 32)
      else combine oracle.compression (readBuffer state 256 32) sibling
    let next := capCheckPathBlockState state answer
    have registers := cap_check_path_block_projection state answer
    have nextScratch : next.getReg .x21 = 256 := (cap_check_path_block_register state answer .x21 (by decide)).trans scratch
    have nextPointer : next.getReg .x25 = BitVec.ofNat 64 (address + 32) := by
      rw [show next.getReg .x25 = state.getReg .x25 + 32 from registers.1, pointer, BitVec.ofNat_add]
      rfl
    have nextData (i : Nat) (hi : i < rest.length) :
        readBuffer next (address + 32 + 32*i) 32 = (rest[i]'hi).2 := by
      have memory : readBuffer next (address + 32 + 32*i) 32 =
          readBuffer state (address + 32 + 32*i) 32 := by
        apply read_digest_congr _ _ _ (by omega)
        intro word hw
        apply cap_check_path_block_outside _ _ scratch _
        intro j hj equal
        have natural := congrArg BitVec.toNat equal
        simp only [BitVec.toNat_ofNat] at natural
        rw [Nat.mod_eq_of_lt (by simp only [List.length_cons] at bounded; omega : address + 32 + 32*i + 8*word < 2^64),
          Nat.mod_eq_of_lt (by omega : 256+8*j < 2^64)] at natural
        omega
      rw [memory, show address + 32 + 32*i = address + 32*(i+1) by omega]
      exact data (i+1) (by simp; omega)
    have nextDirections (i : Nat) (hi : i < rest.length) :
        (next.getReg .x20).getLsbD i = (rest[i]'hi).1 := by
      rw [show next.getReg .x20 = state.getReg .x20 >>> 1 from registers.2.1,
        BitVec.getLsbD_ushiftRight]
      rw [show 1 + i = i + 1 by omega]
      exact directions (i+1) (by simp; omega)
    have induction := ih next (address+32) nextScratch nextPointer (by omega) (by omega)
      (by simp only [List.length_cons] at bounded; omega) nextData nextDirections
    rw [List.length_cons, capCheckPathLoop]
    unfold capCheckScratchQuery
    erw [check_evaluation_public_bind]
    change readBuffer (checkEvaluation oracle (capCheckPathLoop
      (capCheckPathBlockState state (oracle.compression (readBuffer (capCheckPathPreparedState state) 256 64)))
      rest.length)).1 256 32 = _
    rw [input]
    cases right <;>
      change readBuffer (checkEvaluation oracle (capCheckPathLoop next rest.length)).1 256 32 = _
    all_goals
      rw [induction, cap_check_path_block_digest state answer scratch]
      simp only [answer, climb, List.foldl_cons, Bool.false_eq_true, ite_false, ite_true]

end CommitGolfCandidate
