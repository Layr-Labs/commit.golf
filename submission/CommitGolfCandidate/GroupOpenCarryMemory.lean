import CommitGolfCandidate.GroupOpenShifted32
namespace TwoPermutationPrototype.GroupedOpening.Carry
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 PackedOpening Wide Shifted30
set_option maxHeartbeats 1500000
inductive Width where | half | word | dword deriving DecidableEq
def Width.n : Width → Nat | .half => 2 | .word => 4 | .dword => 8
def write (z : Width) (m : MachineState) (T : Nat) (v : Word) := match z with
  | .half => m.setHalfword (BitVec.ofNat 64 T) (v.truncate 16)
  | .word => m.setWord32 (BitVec.ofNat 64 T) (v.truncate 32)
  | .dword => m.setMem (BitVec.ofNat 64 T) v

theorem half_write (s : MachineState) (S T : Nat) (v : Word)
    (ta : T%2=0) (tf : T+2≤2^64)
    (bytes : ∀ i, i<2 → extractByte v i=s.getByte (BitVec.ofNat 64 (S+i))) :
    ByteCopy s (s.setHalfword (BitVec.ofNat 64 T) (v.truncate 16)) S T 2 := by
  have offT := Wide.offset_nat T (by omega)
  have alignT := Wide.align_eq T (by omega)
  constructor
  · intro i hi
    have alignTi : alignToDword (BitVec.ofNat 64 (T+i)) = alignToDword (BitVec.ofNat 64 T) := by
      rw [Wide.align_eq (T+i) (by omega), alignT]
      congr 1
      omega
    rw [ProjectedHalfword.store_byte, ite_eq_left ⟨alignTi, by rw [Wide.offset_nat (T+i) (by omega), offT]; omega⟩,
      Wide.offset_nat (T+i) (by omega), show (T+i)%8%2*8 = 8*i by omega]
    simpa only [Nat.mul_zero,BitVec.ushiftRight_zero,Nat.zero_add] using (slice_byte v 0 2 i hi (by decide)).trans (by simpa only [MachineState.getByte,Nat.zero_add] using bytes i hi)
  · intro q outside
    rw [ProjectedHalfword.store_byte]
    by_cases hit : alignToDword q = alignToDword (BitVec.ofNat 64 T) ∧
        byteOffset q / 2 = byteOffset (BitVec.ofNat 64 T) / 2
    · exfalso
      rw [offT] at hit
      have back := Wide.of_align q (T-T%8) (by rw [hit.1, alignT])
      have ob := @byteOffset_lt_8 q
      apply outside (byteOffset q-T%8) (by omega)
      exact back.trans (congrArg (BitVec.ofNat 64) (by omega))
    · rw [ite_eq_right hit]

theorem word_write (s : MachineState) (S T : Nat) (v : Word)
    (ta : T%4=0) (tf : T+4≤2^64)
    (bytes : ∀ i, i<4 → extractByte v i=s.getByte (BitVec.ofNat 64 (S+i))) :
    ByteCopy s (s.setWord32 (BitVec.ofNat 64 T) (v.truncate 32)) S T 4 := by
  have offT := Wide.offset_nat T (by omega)
  have alignT := Wide.align_eq T (by omega)
  have pos : byteOffset (BitVec.ofNat 64 T) / 4 < 2 := by rw [offT]; omega
  constructor
  · intro i hi
    have alignTi : alignToDword (BitVec.ofNat 64 (T+i)) = alignToDword (BitVec.ofNat 64 T) := by
      rw [Wide.align_eq (T+i) (by omega), alignT]
      congr 1
      omega
    unfold MachineState.getByte MachineState.setWord32
    dsimp only
    rw [alignTi, MachineState.getMem_setMem_eq, Wide.offset_nat (T+i) (by omega),
      Wide.replace_word_byte _ _ _ _ pos (by omega), offT, ite_eq_left (by omega),
      show 8*((T+i)%8-4*(T%8/4)) = 8*i by omega]
    simpa only [Nat.mul_zero,BitVec.ushiftRight_zero,Nat.zero_add] using (slice_byte v 0 4 i hi (by decide)).trans (by simpa only [MachineState.getByte,Nat.zero_add] using bytes i hi)
  · intro q outside
    unfold MachineState.getByte MachineState.setWord32
    dsimp only
    by_cases same : alignToDword q = alignToDword (BitVec.ofNat 64 T)
    · rw [same, MachineState.getMem_setMem_eq, Wide.replace_word_byte _ _ _ _ pos byteOffset_lt_8]
      by_cases hit : 4*(byteOffset (BitVec.ofNat 64 T)/4) ≤ byteOffset q ∧
          byteOffset q < 4*(byteOffset (BitVec.ofNat 64 T)/4)+4
      · exfalso
        rw [offT] at hit
        have back := Wide.of_align q (T-T%8) (by rw [same, alignT])
        apply outside (byteOffset q-T%8) (by omega)
        exact back.trans (congrArg (BitVec.ofNat 64) (by omega))
      · rw [ite_eq_right hit]
    · rw [MachineState.getMem_setMem_ne same]

theorem write_copy (z : Width) (s : MachineState) (S T : Nat) (v : Word)
    (ta : T%z.n=0) (tf : T+z.n≤2^64)
    (bytes : ∀ i, i<z.n → extractByte v i=s.getByte (BitVec.ofNat 64 (S+i))) :
    ByteCopy s (write z s T v) S T z.n := by
  cases z with
  | half => exact half_write s S T v ta tf bytes
  | word => exact word_write s S T v ta tf bytes
  | dword =>
    change T%8=0 at ta
    change T+8≤2^64 at tf
    constructor
    · intro i hi
      change (s.setMem _ v).getByte _=_
      rw [Wide.byte_at _ T i ta hi tf,MachineState.getMem_setMem_eq]
      exact bytes i hi
    · intro q outside
      change (s.setMem _ v).getByte q=s.getByte q
      unfold MachineState.getByte
      apply congrArg (fun a => extractByte a _)
      apply MachineState.getMem_setMem_ne
      intro same
      exact outside (byteOffset q) byteOffset_lt_8 (Wide.of_align q T same)

theorem write_below (z : Width) (s : MachineState) (T : Nat) (v : Word) (q : Word)
    (tf : T<2^64) (low : q.toNat<T-T%8) :
    (write z s T v).getMem q=s.getMem q := by
  cases z with
  | half => exact Shifted30.half_below s T _ q tf low
  | word => exact Shifted30.word_below s T _ q tf low
  | dword =>
    apply MachineState.getMem_setMem_ne
    intro eq
    rw [eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt tf] at low
    omega

theorem write_regs (z : Width) (s : MachineState) (T : Nat) (v : Word) (r : Reg) :
    (write z s T v).getReg r=s.getReg r := by cases z <;> rfl

end TwoPermutationPrototype.GroupedOpening.Carry
