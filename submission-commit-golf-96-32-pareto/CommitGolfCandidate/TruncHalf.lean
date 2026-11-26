import CommitGolfCandidate.WriteMemory
namespace CommitGolfCandidate.Trunc.Wire
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

private theorem byteOffset_bound (address : Word) : byteOffset address < 8 := by
  unfold byteOffset
  rw [BitVec.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

private theorem byte_address_parts (address : Word) :
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

private theorem byteOffset_mod (address : Word) : byteOffset address = address.toNat % 8 := by
  unfold byteOffset
  rw [BitVec.toNat_and]
  change address.toNat &&& 7 = address.toNat % 8
  rw [show (7 : Nat) = 2^3 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]

private theorem successor_slot (address : Word) (even : address.toNat % 2 = 0) :
    alignToDword (address+1) = alignToDword address ∧
      byteOffset (address+1) = byteOffset address + 1 := by
  have bounded := address.isLt
  have addValue : (address+1).toNat = address.toNat + 1 := by
    rw [BitVec.toNat_add]
    change (address.toNat+1) % 2^64 = address.toNat+1
    exact Nat.mod_eq_of_lt (by omega)
  have offsets : byteOffset (address+1) = byteOffset address + 1 := by
    rw [byteOffset_mod, byteOffset_mod, addValue]
    omega
  have split := byte_address_parts (address+1)
  rw [offsets, BitVec.ofNat_add, ← BitVec.add_assoc] at split
  have sum :
      alignToDword (address+1) + BitVec.ofNat 64 (byteOffset address) + 1 =
        alignToDword address + BitVec.ofNat 64 (byteOffset address) + 1 :=
    split.trans (congrArg (· + 1) (byte_address_parts address)).symm
  have common := congrArg (fun x : Word => x - 1 - BitVec.ofNat 64 (byteOffset address)) sum
  exact ⟨by simpa only [BitVec.add_sub_cancel] using common, offsets⟩

private theorem same_slot_addresses (destination query : Word)
    (even : destination.toNat % 2 = 0)
    (aligned : alignToDword query = alignToDword destination)
    (slot : byteOffset query / 2 = byteOffset destination / 2) :
    query = destination ∨ query = destination+1 := by
  have parity : byteOffset destination % 2 = 0 := by rw [byteOffset_mod]; omega
  have offsets : byteOffset query = byteOffset destination ∨
      byteOffset query = byteOffset destination + 1 := by omega
  have address := byte_address_parts query
  rcases offsets with same | following
  · left
    rw [aligned, same, byte_address_parts] at address
    exact address.symm
  · right
    rw [aligned, following, BitVec.ofNat_add, ← BitVec.add_assoc, byte_address_parts] at address
    exact address.symm

private theorem replace_read_byte (word : Word) (half : BitVec 16) (slot index : Nat)
    (slotBound : slot < 4) (indexBound : index < 8) :
    extractByte (replaceHalfword word slot half) index =
      if index / 2 = slot then (half >>> ((index % 2) * 8)).truncate 8
      else extractByte word index := by
  interval_cases slot <;> interval_cases index <;>
    simp (config := {decide := true}) [extractByte, replaceHalfword] <;>
    apply BitVec.eq_of_getLsbD_eq <;>
    intro bit bitBound <;> interval_cases bit <;>
    simp

/-- A halfword store changes both bytes of a single slot in one doubleword. -/
theorem store_byte (state : MachineState) (destination query : Word) (value : BitVec 16) :
    (state.setHalfword destination value).getByte query =
      if alignToDword query = alignToDword destination ∧
          byteOffset query / 2 = byteOffset destination / 2 then
        (value >>> ((byteOffset query % 2) * 8)).truncate 8
      else state.getByte query := by
  by_cases aligned : alignToDword query = alignToDword destination
  · simp only [MachineState.setHalfword, MachineState.getByte, aligned,
      MachineState.getMem_setMem_eq, true_and]
    exact replace_read_byte _ _ _ _ (by have := byteOffset_bound destination; omega)
      (byteOffset_bound query)
  · simp only [MachineState.setHalfword, MachineState.getByte,
      MachineState.getMem_setMem_ne aligned, aligned, false_and, ite_false]

/-- A halfword load recovers the original byte at either position of the slot. -/
theorem load_byte (state : MachineState) (address : Word) (query : Word)
    (aligned : alignToDword query = alignToDword address)
    (slot : byteOffset query / 2 = byteOffset address / 2) :
    ((state.getHalfword address) >>> ((byteOffset query % 2) * 8)).truncate 8 =
      state.getByte query := by
  simp only [MachineState.getHalfword, MachineState.getByte, ← slot, ← aligned]
  have indexBound := byteOffset_bound query
  generalize byteOffset query = index at indexBound ⊢
  interval_cases index <;>
    apply BitVec.eq_of_getLsbD_eq <;>
    intro bit bitBound <;> interval_cases bit <;>
    simp [extractByte, extractHalfword]

/-- All bytes outside the addressed two-byte slice retain their old contents. -/
theorem store_outside (state : MachineState) (destination query : Word) (value : BitVec 16)
    (even : destination.toNat % 2 = 0) (outside : query ≠ destination ∧ query ≠ destination+1) :
    (state.setHalfword destination value).getByte query = state.getByte query := by
  rw [store_byte, ite_eq_right]
  intro sameSlot
  exact (same_slot_addresses destination query even sameSlot.1 sameSlot.2).elim outside.1 outside.2

/-- An aligned halfword copy transports both constituent bytes in little-endian order. -/
theorem copy_bytes (state : MachineState) (source target : Word)
    (sourceEven : source.toNat % 2 = 0) (targetEven : target.toNat % 2 = 0) :
    let next := state.setHalfword target (state.getHalfword source)
    next.getByte target = state.getByte source ∧ next.getByte (target+1) = state.getByte (source+1) := by
  have sourceParity : byteOffset source % 2 = 0 := by rw [byteOffset_mod]; omega
  have targetParity : byteOffset target % 2 = 0 := by rw [byteOffset_mod]; omega
  obtain ⟨sourceAligned, sourceOffset⟩ := successor_slot source sourceEven
  obtain ⟨targetAligned, targetOffset⟩ := successor_slot target targetEven
  have sourceSlot : byteOffset (source+1) / 2 = byteOffset source / 2 := by omega
  have targetSlot : byteOffset (target+1) / 2 = byteOffset target / 2 := by omega
  constructor
  · rw [store_byte, ite_eq_left ⟨rfl,rfl⟩, targetParity, ← sourceParity]
    exact load_byte state source source rfl rfl
  · rw [store_byte, ite_eq_left ⟨targetAligned,targetSlot⟩]
    have sameParity : byteOffset (target+1) % 2 = byteOffset (source+1) % 2 := by omega
    rw [sameParity]
    exact load_byte state source (source+1) sourceAligned sourceSlot

theorem zero_bytes (s : MachineState) (target : Word) (even : target.toNat%2=0) :
    (s.setHalfword target 0).getByte target=0 ∧ (s.setHalfword target 0).getByte (target+1)=0 := by
  obtain ⟨aligned,off⟩:=successor_slot target even
  have p : byteOffset target%2=0 := by rw [byteOffset_mod];omega
  constructor
  · rw [store_byte,if_pos ⟨rfl,rfl⟩];simp
  · rw [store_byte,if_pos ⟨aligned,by omega⟩];simp
end CommitGolfCandidate.Trunc.Wire
