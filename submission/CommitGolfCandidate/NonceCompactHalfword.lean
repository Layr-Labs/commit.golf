import CommitGolf.Riscv

/-! Byte effects of the interpreter's halfword load and store. A halfword store at an even
address changes exactly its two bytes; a halfword load reads the two bytes at that address. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

theorem half_offset_mod (address : Word) : byteOffset address = address.toNat % 8 := by
  unfold byteOffset
  rw [BitVec.toNat_and]
  change address.toNat &&& (2^3-1) = address.toNat % 2^3
  exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem half_address_parts (address : Word) :
    alignToDword address + BitVec.ofNat 64 (byteOffset address) = address := by
  unfold alignToDword byteOffset
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have disjoint : (address &&& ~~~7#64) &&& (address &&& 7#64) = 0 := by
    ext i
    simp only [BitVec.getElem_and, BitVec.getElem_not]
    cases h : (7#64)[i] <;> simp
  have combined : (address &&& ~~~7#64) ||| (address &&& 7#64) = address := by
    ext i
    simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not]
    cases h : (7#64)[i] <;> simp
  rw [BitVec.add_eq_or_of_and_eq_zero _ _ disjoint, combined]

theorem half_align_eq (address : Word) :
    alignToDword address = address - BitVec.ofNat 64 (byteOffset address) := by
  have parts := half_address_parts address
  calc alignToDword address =
        alignToDword address + BitVec.ofNat 64 (byteOffset address) - BitVec.ofNat 64 (byteOffset address) :=
        (BitVec.add_sub_cancel _ _).symm
    _ = address - BitVec.ofNat 64 (byteOffset address) := by rw [parts]

theorem half_next (address : Word) (even : address.toNat % 2 = 0) :
    alignToDword (address + 1) = alignToDword address ∧
      byteOffset (address + 1) = byteOffset address + 1 := by
  have small : address.toNat + 1 < 2^64 := by
    have bound := address.isLt
    omega
  have successor : (address + 1).toNat = address.toNat + 1 := by
    rw [BitVec.toNat_add]
    have one : (1 : Word).toNat = 1 := rfl
    rw [one]
    omega
  have offset : byteOffset (address + 1) = byteOffset address + 1 := by
    rw [half_offset_mod, half_offset_mod, successor]
    omega
  refine ⟨?_, offset⟩
  rw [half_align_eq (address + 1), half_align_eq address, offset]
  apply BitVec.eq_of_toNat_eq
  have offsetBound : byteOffset address ≤ address.toNat := by
    rw [half_offset_mod]
    exact Nat.mod_le _ _
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, successor]
  have lowBound : byteOffset address < 8 := by rw [half_offset_mod]; omega
  rw [Nat.mod_eq_of_lt (by omega : byteOffset address + 1 < 2^64),
    Nat.mod_eq_of_lt (by omega : byteOffset address < 2^64)]
  omega

theorem half_same_word (query address : Word)
    (aligned : alignToDword query = alignToDword address)
    (offset : byteOffset query = byteOffset address) : query = address := by
  rw [← half_address_parts query, aligned, offset, half_address_parts]

theorem half_extract_replace (word : Word) (half : BitVec 16) (place byte : Nat)
    (placeBound : place < 4) (byteBound : byte < 8) :
    extractByte (replaceHalfword word place half) byte =
      if byte = 2 * place then half.extractLsb' 0 8
      else if byte = 2 * place + 1 then half.extractLsb' 8 8
      else extractByte word byte := by
  interval_cases place <;> interval_cases byte <;>
    (apply BitVec.eq_of_getLsbD_eq
     intro bit hb
     interval_cases bit <;> simp [extractByte, replaceHalfword])

theorem half_extract_low (word : Word) (place : Nat) (placeBound : place < 4) :
    (extractHalfword word place).extractLsb' 0 8 = extractByte word (2 * place) := by
  interval_cases place <;>
    (apply BitVec.eq_of_getLsbD_eq
     intro bit hb
     interval_cases bit <;> simp [extractByte, extractHalfword])

theorem half_extract_high (word : Word) (place : Nat) (placeBound : place < 4) :
    (extractHalfword word place).extractLsb' 8 8 = extractByte word (2 * place + 1) := by
  interval_cases place <;>
    (apply BitVec.eq_of_getLsbD_eq
     intro bit hb
     interval_cases bit <;> simp [extractByte, extractHalfword])

/-- A halfword store at an even address changes exactly its two bytes. -/
theorem half_set_read (state : MachineState) (address query : Word) (half : BitVec 16)
    (even : address.toNat % 2 = 0) :
    (state.setHalfword address half).getByte query =
      if query = address then half.extractLsb' 0 8
      else if query = address + 1 then half.extractLsb' 8 8
      else state.getByte query := by
  have offsetEven : byteOffset address % 2 = 0 := by rw [half_offset_mod]; omega
  have offsetBound : byteOffset address < 8 := by rw [half_offset_mod]; omega
  have queryBound : byteOffset query < 8 := by rw [half_offset_mod]; omega
  have next := half_next address even
  by_cases aligned : alignToDword query = alignToDword address
  · simp only [MachineState.setHalfword, MachineState.getByte, aligned, MachineState.getMem_setMem_eq]
    rw [half_extract_replace _ _ _ _ (by omega) queryBound]
    have twice : 2 * (byteOffset address / 2) = byteOffset address := by omega
    rw [twice]
    by_cases first : query = address
    · subst query
      simp
    · have offsetNe : byteOffset query ≠ byteOffset address := fun same =>
        first (half_same_word query address aligned same)
      rw [if_neg offsetNe, if_neg first]
      by_cases second : query = address + 1
      · subst query
        rw [if_pos next.2, if_pos rfl]
      · have offsetNe' : byteOffset query ≠ byteOffset address + 1 := fun same =>
          second (half_same_word query (address + 1) (aligned.trans next.1.symm) (same.trans next.2.symm))
        rw [if_neg offsetNe', if_neg second]
  · have first : query ≠ address := fun same => aligned (by rw [same])
    have second : query ≠ address + 1 := fun same => aligned (by rw [same, next.1])
    simp only [MachineState.setHalfword, MachineState.getByte, MachineState.getMem_setMem_ne aligned,
      if_neg first, if_neg second]

/-- A halfword load at an even address reads its two bytes. -/
theorem half_get_low (state : MachineState) (address : Word) (even : address.toNat % 2 = 0) :
    (state.getHalfword address).extractLsb' 0 8 = state.getByte address := by
  have offsetEven : byteOffset address % 2 = 0 := by rw [half_offset_mod]; omega
  have offsetBound : byteOffset address < 8 := by rw [half_offset_mod]; omega
  simp only [MachineState.getHalfword, MachineState.getByte]
  rw [half_extract_low _ _ (by omega)]
  congr 1
  omega

theorem half_get_high (state : MachineState) (address : Word) (even : address.toNat % 2 = 0) :
    (state.getHalfword address).extractLsb' 8 8 = state.getByte (address + 1) := by
  have offsetEven : byteOffset address % 2 = 0 := by rw [half_offset_mod]; omega
  have offsetBound : byteOffset address < 8 := by rw [half_offset_mod]; omega
  have next := half_next address even
  simp only [MachineState.getHalfword, MachineState.getByte, next.1, next.2]
  rw [half_extract_high _ _ (by omega)]
  congr 1
  omega

/-- Load-then-store of one halfword, from `source` to `target` (both even). -/
theorem half_copy_read (state : MachineState) (source target query : Word)
    (sourceEven : source.toNat % 2 = 0) (targetEven : target.toNat % 2 = 0) :
    (state.setHalfword target (state.getHalfword source)).getByte query =
      if query = target then state.getByte source
      else if query = target + 1 then state.getByte (source + 1)
      else state.getByte query := by
  rw [half_set_read _ _ _ _ targetEven, half_get_low _ _ sourceEven, half_get_high _ _ sourceEven]

end CommitGolfCandidate
