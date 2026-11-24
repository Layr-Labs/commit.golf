import CommitGolfCandidate.CapBFormat
import CommitGolfCandidate.K3OpenCapSpec
namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 TwoPermutationPrototype.Sampling

/-- One byte of a little-endian read. -/
theorem read_byte (state : MachineState) (address count j : Nat) (hj : j<count) :
    (readBuffer state address count).extractLsb' (8*j) 8=state.getByte (BitVec.ofNat 64 (address+j)) := by
  rw [read_buffer_slice state address count j 1 (by omega)]
  apply BitVec.eq_of_toNat_eq
  have := (state.getByte (BitVec.ofNat 64 (address+j))).isLt
  simp [readBuffer, BitVec.toNat_ofNat] <;> omega

/-- The digest bytes of a 32-byte read are the bytes read. -/
theorem digest_bytes_read (state : MachineState) (address : Nat) :
    digestBytes (readBuffer state address 32)=bytesAt state address 32 := by
  apply List.ext_getElem
  · simp [digestBytes, bytesAt]
  · intro j h1 h2
    have hj : j<32 := by simpa [digestBytes] using h1
    simp only [digestBytes, List.getElem_ofFn]
    rw [bytes_at_getElem _ _ _ _ hj]
    exact read_byte state address 32 j hj

theorem plain_read (state : MachineState) (address : Nat) :
    plain30 (readBuffer state address 32)=bytesAt state address 30 := by
  unfold plain30
  rw [digest_bytes_read]
  unfold bytesAt
  rw [← List.map_take, List.take_range]; rfl

theorem half_bytes (state : MachineState) (address : Nat) :
    (halfAt state address).extractLsb' 0 8=state.getByte (BitVec.ofNat 64 address) ∧
      (halfAt state address).extractLsb' 8 8=state.getByte (BitVec.ofNat 64 (address+1)) := by
  unfold halfAt
  constructor
  · exact BitVec.extractLsb'_append_eq_right
  · exact BitVec.extractLsb'_append_eq_left

theorem half_of_read (state : MachineState) (address : Nat) :
    halfAt state (address+28)=(readBuffer state address 32).extractLsb' 224 16 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  unfold halfAt
  rw [BitVec.getLsbD_append]
  by_cases low : i<8
  · rw [if_pos low]
    have b := congrArg (fun x : BitVec 8 => x.getLsbD i) (read_byte state address 32 28 (by decide))
    simp only [BitVec.getLsbD_extractLsb', show i<8 from low, decide_true, Bool.true_and] at b
    simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
    rw [← b]
  · rw [if_neg low]
    have b := congrArg (fun x : BitVec 8 => x.getLsbD (i-8)) (read_byte state address 32 29 (by decide))
    simp only [BitVec.getLsbD_extractLsb', show i-8<8 by omega, decide_true, Bool.true_and] at b
    simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
      show address+28+1=address+29 by omega]
    rw [← b]; congr 1; omega

end TwoPermutationPrototype.GroupedOpening
