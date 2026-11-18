import CommitGolfCandidate.NonceSaltMemory
import CommitGolfCandidate.Execution
import CommitGolfCandidate.S6Tree

/-! Eight decoded cap instructions write the salt field of an opening record:
two nonce words, then the tag `x20 * 256 + 4072`. The fourth word of the field
is not written. The fetched image is a premise until the concrete candidate
supplies its bytes. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def capNonceInstructions : List Instr :=
  [.LD .x6 .x23 0,.SD .x25 .x6 0,.LD .x6 .x23 8,.SD .x25 .x6 8,
   .SLLI .x6 .x20 8,.ADDI .x6 .x6 2047,.ADDI .x6 .x6 2025,.SD .x25 .x6 16]

def capNoncePrefix (state : MachineState) (count : Nat) : MachineState :=
  (capNonceInstructions.take count).foldl execInstrBr state

def capNonceEightState (state : MachineState) : MachineState := capNoncePrefix state 8

private theorem cap_nonce_getReg_setMem (state : MachineState) (address value : Word) (reg : Reg) :
    (state.setMem address value).getReg reg=state.getReg reg := by cases reg <;> rfl

private theorem cap_nonce_getMem_setMem (state : MachineState) (address value query : Word) :
    (state.setMem address value).getMem query=(if query=address then value else state.getMem query) := by
  simp [MachineState.getMem,MachineState.setMem]

theorem cap_nonce_prefix_register (state : MachineState) (count : Nat) (bounded : count≤8)
    (reg : Reg) (notTemporary : reg≠.x6) :
    (capNoncePrefix state count).getReg reg=state.getReg reg := by
  interval_cases count <;>
    simp only [capNoncePrefix,capNonceInstructions,List.take,List.foldl,execInstrBr,
      MachineState.getReg_setPC,cap_nonce_getReg_setMem,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm notTemporary)]

def CapNonceFetched (image : Image) : Prop :=
  ∀ (state : MachineState) (i : Nat),i<8 → state.pc=BitVec.ofNat 64 (4224+4*i) →
    fetch image state=some (.base ((capNonceInstructions[i]?).getD .EBREAK))

theorem cap_nonce_eight_execute (image : Image) (fetched : CapNonceFetched image)
    (state : MachineState) (pc : state.pc = 4224)
    (sourceValid : ∀ word : Fin 2,
      accessValid (state.getReg .x23 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (destinationValid : ∀ word : Fin 3,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute image (8 + fuel) state allowCoins =
      (do let result ← execute image fuel (capNonceEightState state) allowCoins
          return result.charge 8 0) := by
  change execute image (8 + fuel) state allowCoins =
    (do let result ← execute image fuel (capNoncePrefix state 8) allowCoins
        return result.charge 8 0)
  apply execute_unit_steps (states := capNoncePrefix state)
  intro i hi
  refine ⟨.base ((capNonceInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply fetched _ i hi
    interval_cases i <;>
      simp [capNoncePrefix, capNonceInstructions, execInstrBr, pc,
        MachineState.setPC]
  · have source := cap_nonce_prefix_register state i (by omega) .x23 (by decide)
    have destination := cap_nonce_prefix_register state i (by omega) .x25 (by decide)
    have s0 := sourceValid ⟨0, by decide⟩
    have s1 := sourceValid ⟨1, by decide⟩
    have d0 := destinationValid ⟨0, by decide⟩
    have d1 := destinationValid ⟨1, by decide⟩
    have d2 := destinationValid ⟨2, by decide⟩
    have valid : memoryArgumentsValid (capNoncePrefix state i)
        ((capNonceInstructions[i]?).getD .EBREAK) = true := by
      interval_cases i <;>
        simp only [capNonceInstructions, List.getElem?_cons_zero,
          List.getElem?_cons_succ, Option.getD_some, memoryArgumentsValid,
          memAccess, source, destination, signExtend12] <;>
        first | rfl | exact s0 | exact s1 | exact d0 | exact d1 | exact d2
    interval_cases i <;>
      simp only [capNonceInstructions, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some] at valid ⊢ <;>
      simp only [ordinaryStep, valid, ↓reduceIte] <;> rfl
  · interval_cases i <;> rfl

theorem cap_nonce_eight_register (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x6) :
    (capNonceEightState state).getReg reg = state.getReg reg :=
  cap_nonce_prefix_register state 8 (by decide) reg outside

theorem cap_nonce_eight_pc (state : MachineState) :
    (capNonceEightState state).pc = state.pc + 32 := by
  simp [capNonceEightState,capNoncePrefix,capNonceInstructions,execInstrBr,
    MachineState.setPC,BitVec.add_assoc]

theorem cap_nonce_eight_memory_outside (state : MachineState) (address : Word)
    (outside : ∀ word : Fin 3, address ≠ state.getReg .x25 + BitVec.ofNat 64 (8*word.val)) :
    (capNonceEightState state).getMem address = state.getMem address := by
  have a0 : address≠state.getReg .x25 := by simpa using outside ⟨0,by decide⟩
  have a1 : address≠state.getReg .x25+8#64 := outside ⟨1,by decide⟩
  have a2 : address≠state.getReg .x25+16#64 := outside ⟨2,by decide⟩
  simp [capNonceEightState,capNoncePrefix,capNonceInstructions,execInstrBr,
    MachineState.getReg_setReg_ne,MachineState.getReg_setReg_eq,cap_nonce_getReg_setMem,
    cap_nonce_getMem_setMem,signExtend12,a0,a1,a2]

/-- The tag word computed from the loaded position. -/
theorem cap_nonce_tag_word (position : Nat) (bounded : position < 2^24) :
    BitVec.ofNat 64 position <<< (8 : BitVec 6).toNat + signExtend12 2047 + signExtend12 2025 =
      BitVec.ofNat 64 (4072+256*position) := by
  have shifted : BitVec.ofNat 64 position <<< (8 : BitVec 6).toNat =
      BitVec.ofNat 64 (256*position) := by
    rw [BitVec.shiftLeft_eq_mul_twoPow, show (8 : BitVec 6).toNat = 8 by decide,
      show BitVec.twoPow 64 8 = BitVec.ofNat 64 256 by decide, ← BitVec.ofNat_mul,
      Nat.mul_comm]
  rw [shifted, show signExtend12 2047 = BitVec.ofNat 64 2047 by decide,
    show signExtend12 2025 = BitVec.ofNat 64 2025 by decide,
    ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  congr 1
  omega

theorem cap_nonce_eight_words (state : MachineState) (source destination position : Nat)
    (sourcePointer : state.getReg .x23 = BitVec.ofNat 64 source)
    (destinationPointer : state.getReg .x25 = BitVec.ofNat 64 destination)
    (index : state.getReg .x20 = BitVec.ofNat 64 position)
    (positionBound : position < 2^24)
    (sourceBound : source+16 ≤ 2^64) (destinationBound : destination+32 ≤ 2^64)
    (separate : source+16 ≤ destination ∨ destination+32 ≤ source) :
    (capNonceEightState state).getMem (BitVec.ofNat 64 destination) =
        state.getMem (BitVec.ofNat 64 source) ∧
    (capNonceEightState state).getMem (BitVec.ofNat 64 (destination+8)) =
        state.getMem (BitVec.ofNat 64 (source+8)) ∧
    (capNonceEightState state).getMem (BitVec.ofNat 64 (destination+16)) =
        BitVec.ofNat 64 (4072+256*position) ∧
    (capNonceEightState state).getMem (BitVec.ofNat 64 (destination+24)) =
        state.getMem (BitVec.ofNat 64 (destination+24)) := by
  have distinct (left right : Nat) (leftBound : left < 2^64) (rightBound : right < 2^64)
      (different : left ≠ right) : BitVec.ofNat 64 left ≠ BitVec.ofNat 64 right := by
    intro equal
    have natural := congrArg BitVec.toNat equal
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt leftBound,
      Nat.mod_eq_of_lt rightBound] at natural
    exact different natural
  have d8 : BitVec.ofNat 64 destination + 8#64 = BitVec.ofNat 64 (destination+8) := by
    rw [BitVec.ofNat_add]
  have d16 : BitVec.ofNat 64 destination + 16#64 = BitVec.ofNat 64 (destination+16) := by
    rw [BitVec.ofNat_add]
  have s8 : BitVec.ofNat 64 source + 8#64 = BitVec.ofNat 64 (source+8) := by
    rw [BitVec.ofNat_add]
  have h1 := distinct (source+8) destination (by omega) (by omega) (by omega)
  have h2 := distinct (destination+8) destination (by omega) (by omega) (by omega)
  have h3 := distinct (destination+16) destination (by omega) (by omega) (by omega)
  have h4 := distinct (destination+16) (destination+8) (by omega) (by omega) (by omega)
  have h5 := distinct (destination+24) destination (by omega) (by omega) (by omega)
  have h6 := distinct (destination+24) (destination+8) (by omega) (by omega) (by omega)
  have h7 := distinct (destination+24) (destination+16) (by omega) (by omega) (by omega)
  have tag := cap_nonce_tag_word position positionBound
  have g2 := Ne.symm h2
  have g3 := Ne.symm h3
  have g4 := Ne.symm h4
  have x6 : (capNoncePrefix state 7).getReg .x6 = BitVec.ofNat 64 (4072+256*position) := by
    simp only [capNoncePrefix, capNonceInstructions, List.take, List.foldl, execInstrBr,
      MachineState.getReg_setPC, cap_nonce_getReg_setMem, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, ne_eq, reduceCtorEq, not_false_eq_true, index]
    exact tag
  have pointer7 : (capNoncePrefix state 7).getReg .x25 = BitVec.ofNat 64 destination :=
    (cap_nonce_prefix_register state 7 (by decide) .x25 (by decide)).trans destinationPointer
  have last : capNonceEightState state =
      execInstrBr (capNoncePrefix state 7) (.SD .x25 .x6 16) := rfl
  have fourth := cap_nonce_eight_memory_outside state (BitVec.ofNat 64 (destination+24)) (by
    intro word
    rw [destinationPointer, ← BitVec.ofNat_add]
    exact distinct _ _ (by omega) (by omega) (by have := word.isLt; omega))
  refine ⟨?_, ?_, ?_, fourth⟩
  · simp [capNonceEightState, capNoncePrefix, capNonceInstructions, execInstrBr,
      MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq, cap_nonce_getReg_setMem,
      cap_nonce_getMem_setMem, signExtend12, sourcePointer, destinationPointer, d8, d16, s8,
      h1, h2, h3, h4, g2, g3, g4]
  · simp [capNonceEightState, capNoncePrefix, capNonceInstructions, execInstrBr,
      MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq, cap_nonce_getReg_setMem,
      cap_nonce_getMem_setMem, signExtend12, sourcePointer, destinationPointer, d8, d16, s8,
      h1, h2, h3, h4, g2, g3, g4]
  · rw [last]
    simp only [execInstrBr, pointer7, x6, cap_nonce_getMem_setMem, MachineState.getMem_setPC,
      show signExtend12 (16 : BitVec 12) = BitVec.ofNat 64 16 by decide, ← BitVec.ofNat_add,
      ↓reduceIte]

/-- Bytes outside the three written words are preserved. -/
theorem cap_nonce_byte_outside (state : MachineState)
    (destination address : Nat)
    (pointer : state.getReg .x25 = BitVec.ofNat 64 destination)
    (aligned : destination % 8 = 0)
    (destinationBound : destination + 32 ≤ 2^64) (addressBound : address < 2^64)
    (outside : address < destination ∨ destination + 24 ≤ address) :
    (capNonceEightState state).getByte (BitVec.ofNat 64 address) =
      state.getByte (BitVec.ofNat 64 address) := by
  have decomposition : 8 * (address / 8) + address % 8 = address := by omega
  have memory :
      (capNonceEightState state).getMem
          (BitVec.ofNat 64 (8 * (address / 8))) =
        state.getMem (BitVec.ofNat 64 (8 * (address / 8))) := by
    apply cap_nonce_eight_memory_outside
    intro word equal
    rw [pointer, ← BitVec.ofNat_add] at equal
    have numeric := congrArg BitVec.toNat equal
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 8 * (address / 8) < 2^64),
      Nat.mod_eq_of_lt (by omega : destination + 8 * word.val < 2^64)] at numeric
    omega
  conv_lhs => rw [← decomposition]
  conv_rhs => rw [← decomposition]
  rw [aligned_byte _ (address / 8) (address % 8) (by omega),
    aligned_byte _ (address / 8) (address % 8) (by omega)]
  simp only [Nat.div_eq_of_lt (by omega : address % 8 < 8), Nat.mul_zero,
    Nat.add_zero, Nat.mod_eq_of_lt (by omega : address % 8 < 8), memory]

private theorem append_value {highWidth lowWidth : Nat}
    (high : BitVec highWidth) (low : BitVec lowWidth) :
    (high ++ low).toNat = high.toNat * 2^lowWidth + low.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt low.isLt, Nat.shiftLeft_eq]

/-- A salt field built from two nonce words, the tag and a zero word is the
tagged salt of the first two words of the source digest. -/
theorem cap_nonce_salt_field (w0 w1 w2 w3 : Word) (tag : Nat) (tagBound : tag < 2^64) :
    (((0#64 ++ BitVec.ofNat 64 tag) ++ w1) ++ w0 : BitVec 256) =
      BitVec.ofNat 256 ((((w3 ++ w2) ++ w1) ++ w0 : BitVec 256).toNat % 2^128 + tag * 2^128) := by
  apply BitVec.eq_of_toNat_eq
  have b0 := w0.isLt
  have b1 := w1.isLt
  have b2 := w2.isLt
  have b3 := w3.isLt
  simp only [append_value, BitVec.toNat_ofNat]
  norm_num at b0 b1 b2 b3 tagBound ⊢
  omega

end CommitGolfCandidate
