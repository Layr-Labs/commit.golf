import CommitGolfCandidate.NonceExpandBytes
import CommitGolfCandidate.NonceWordObserve

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open NonceCopyMemory
set_option maxRecDepth 8192
set_option maxHeartbeats 500000

theorem nonce_expand_loader_memory (base count words : Nat) (before after reference : MachineState)
    (aligned : base%8=0) (window : base+544*count+8*words ≤ 2^64) (effect : NonceFullExpandMemory base count words before after)
    (loaded : nonceMemoryBytes reference base (544*count+8*words)=
      NonceCodec.expand 0 count (nonceMemoryBytes before base (536*count+8*words)))
    (outside : ∀ location, location<2^64 → location%8=0 →
      (location<base ∨ base+544*count+8*words ≤ location) →
      reference.getMem (BitVec.ofNat 64 location)=before.getMem (BitVec.ofNat 64 location))
    (location : Word) (locationAligned : location.toNat%8=0) :
    reference.getMem location=after.getMem location := by
  have bytes : nonceMemoryBytes reference base (544*count+8*words)=
      nonceMemoryBytes after base (544*count+8*words) :=
    loaded.trans (nonce_expand_memory_bytes base count words before after aligned effect).symm
  have locationEq : BitVec.ofNat 64 location.toNat=location := by simp
  by_cases inBuffer : base ≤ location.toNat ∧ location.toNat<base+544*count+8*words
  · rw [←locationEq]
    apply nonce_aligned_word_eq reference after location.toNat locationAligned
    intro byte bounded
    let offset:=location.toNat-base+byte
    have inside : offset<544*count+8*words := by dsimp only [offset]; omega
    have selected:=congrArg (fun values : List Byte => values[offset]?) bytes
    simp only [nonceMemoryBytes,List.getElem?_map] at selected
    rw [List.getElem?_range inside] at selected
    simp only [Option.map_some] at selected
    have addressEq : base+offset=location.toNat+byte := by dsimp only [offset]; omega
    simpa only [addressEq] using Option.some.inj selected
  · have outer : location.toNat<base ∨ base+544*count+8*words ≤ location.toNat := by omega
    have initial:=outside location.toNat location.isLt locationAligned outer
    rw [locationEq] at initial
    rw [initial,effect.frame]
    intro index inside
    intro equal
    have numeric:=congrArg BitVec.toNat equal
    have upper : base+8*index<2^64 := by
      omega
    rw [address,BitVec.toNat_ofNat,Nat.mod_eq_of_lt upper] at numeric
    omega
end CommitGolfCandidate
