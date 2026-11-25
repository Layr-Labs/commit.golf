import CommitGolfCandidate.CapCheckLeafReference

/-! The relocated cap checker executes the same ordered salted leaf fold.
This fixed-oracle theorem follows the new physical transitions and the checked
scratch-copy semantics; arbitrary-reply execution is proved separately. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] readBuffer

/-- The checker loop computes the ordered salted compression fold. -/
theorem cap_check_leaf_loop_digest (oracle : Oracle) (state : MachineState)
    (address count : Nat) (blocks : Nat → Digest)
    (scratch : state.getReg .x21 = 256)
    (pointer : state.getReg .x8 = BitVec.ofNat 64 address)
    (aligned : address % 8 = 0) (above : 320 ≤ address)
    (bounded : address + 32 * count < 2^64)
    (data : ∀ i < count, readBuffer state (address + 32*i) 32 = blocks i) :
    readBuffer (checkEvaluation oracle (capCheckLeafLoop state count)).1 256 32 =
      (List.range count).foldl
        (fun digest i => combine oracle.compression digest (blocks i)) (readBuffer state 256 32) := by
  induction count generalizing state address blocks with
  | zero => simp [capCheckLeafLoop, check_evaluation_pure]
  | succ count ih =>
    have pointerNat : (state.getReg .x8).toNat = address := by
      rw [pointer, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have separated : ∀ i < 4, ∀ j < 4,
        state.getReg .x8 + BitVec.ofNat 64 (8*i) ≠ BitVec.ofNat 64 (288+8*j) := by
      intro i hi j hj equal
      have natural := congrArg BitVec.toNat equal
      rw [pointer, ← BitVec.ofNat_add] at natural
      simp only [BitVec.toNat_ofNat] at natural
      rw [Nat.mod_eq_of_lt (by omega : address + 8*i < 2^64),
        Nat.mod_eq_of_lt (by omega : 288+8*j < 2^64)] at natural
      omega
    have input := cap_check_leaf_query_reference state scratch (by simpa [pointerNat] using aligned) separated
    rw [pointerNat, show address = address + 32*0 by omega, data 0 (by omega)] at input
    let answer := combine oracle.compression (readBuffer state 256 32) (blocks 0)
    let next := capCheckLeafBlockState state answer
    have nextScratch : next.getReg .x21 = 256 :=
      (cap_check_leaf_block_register state answer .x21 (by decide)).trans scratch
    have nextPointer : next.getReg .x8 = BitVec.ofNat 64 (address + 32) := by
      rw [show next.getReg .x8 = state.getReg .x8 + 32 from (cap_check_leaf_block_pointers state answer).1, pointer]
      rw [BitVec.ofNat_add]
      rfl
    have nextData (i : Nat) (hi : i < count) :
        readBuffer next (address + 32 + 32*i) 32 = blocks (i+1) := by
      have memory : readBuffer next (address + 32 + 32*i) 32 =
          readBuffer state (address + 32 + 32*i) 32 := by
        apply read_digest_congr _ _ _ (by omega)
        intro word hw
        apply cap_check_leaf_block_outside _ _ scratch
        intro j hj equal
        have natural := congrArg BitVec.toNat equal
        simp only [BitVec.toNat_ofNat] at natural
        rw [Nat.mod_eq_of_lt (by omega : address + 32 + 32*i + 8*word < 2^64),
          Nat.mod_eq_of_lt (by omega : 256+8*j < 2^64)] at natural
        omega
      rw [memory, show address + 32 + 32*i = address + 32*(i+1) by omega]
      exact data (i+1) (by omega)
    have induction := ih next (address+32) (fun i => blocks (i+1)) nextScratch nextPointer
      (by omega) (by omega) (by omega) nextData
    rw [capCheckLeafLoop]
    unfold capCheckScratchQuery
    erw [check_evaluation_public_bind]
    change readBuffer (checkEvaluation oracle (capCheckLeafLoop
      (capCheckLeafBlockState state (oracle.compression (readBuffer (capCheckLeafCopyState state) 256 64)))
      count)).1 256 32 = _
    rw [input]
    change readBuffer (checkEvaluation oracle (capCheckLeafLoop next count)).1 256 32 = _
    rw [induction, cap_check_leaf_block_digest state answer scratch]
    simp only [List.range_succ_eq_map, List.foldl_cons, List.foldl_map,
      Nat.succ_eq_add_one]
    rfl


/-- The checker loop preserves every memory word outside scratch. -/
theorem cap_check_leaf_loop_outside (oracle : Oracle) (state : MachineState) (count : Nat)
    (address : Word) (scratch : state.getReg .x21 = 256)
    (outside : ∀ i < 8, address ≠ BitVec.ofNat 64 (256+8*i)) :
    (checkEvaluation oracle (capCheckLeafLoop state count)).1.getMem address = state.getMem address := by
  induction count generalizing state with
  | zero => simp [capCheckLeafLoop, check_evaluation_pure]
  | succ count ih =>
    rw [capCheckLeafLoop]
    unfold capCheckScratchQuery
    erw [check_evaluation_public_bind]
    let answer := oracle.compression (readBuffer (capCheckLeafCopyState state) 256 64)
    change (checkEvaluation oracle (capCheckLeafLoop (capCheckLeafBlockState state answer) count)).1.getMem address = _
    rw [ih _ ((cap_check_leaf_block_register state answer .x21 (by decide)).trans scratch)]
    exact cap_check_leaf_block_outside state answer scratch address outside

/-- The checking leaf loop computes the salted digest in scratch. -/
theorem cap_check_leaf_digest (oracle : Oracle) (state : MachineState) (address : Nat)
    (salt : Digest) (value : Entry)
    (scratch : state.getReg .x21 = 256)
    (pointer : state.getReg .x8 = BitVec.ofNat 64 address)
    (aligned : address % 8 = 0) (above : 320 ≤ address)
    (bounded : address + 256 < 2^64)
    (initial : readBuffer state 256 32 = salt)
    (data : ∀ i < 8, readBuffer state (address + 32*i) 32 = value.extractLsb' (256*i) 256) :
    readBuffer (checkEvaluation oracle (capCheckLeafLoop state 8)).1 256 32 =
      leafDigest oracle.compression salt value := by
  rw [cap_check_leaf_loop_digest oracle state address 8 _ scratch pointer aligned above bounded data, initial]
  rfl


end CommitGolfCandidate
