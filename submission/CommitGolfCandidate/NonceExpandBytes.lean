import CommitGolfCandidate.NonceExpandFullMemory
import CommitGolfCandidate.NonceExpandWordIndex
import CommitGolfCandidate.NonceCompactBytes

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open NonceCopyMemory
set_option maxRecDepth 8192
set_option maxHeartbeats 500000

theorem nonce_expand_full_byte (base count words : Nat) (before after : MachineState)
    (aligned : base%8=0) (effect : NonceFullExpandMemory base count words before after)
    (offset : Nat) (inside : offset<544*count+8*words) :
    after.getByte (BitVec.ofNat 64 (base+offset))=
      match NonceCodec.expandedSource count offset with
      | none => 0
      | some source => before.getByte (BitVec.ofNat 64 (base+source)) := by
  have wordBound : offset/8<68*count+words := by omega
  have copied:=effect.copied (offset/8) wordBound
  rw [nonce_expand_word_index]
  by_cases inPrefix : offset<544*count
  · rw [if_pos inPrefix]
    by_cases padding : (offset/8)%68=3
    · rw [if_pos padding]
      rw [nonce_aligned_byte after base offset aligned,copied,
        if_pos ⟨by omega,padding⟩]
      have byteBound : offset%8<8 := by omega
      interval_cases h : offset%8 <;> rfl
    · rw [if_neg padding]
      rw [if_neg (by omega : ¬(offset/8<68*count ∧ (offset/8)%68=3)),
        if_pos (by omega : offset/8<68*count)] at copied
      have bytes:=nonce_word_equal_bytes before after base (offset/8)
        (nonceExpandedSourceWord (offset/8)) (offset%8) aligned (by omega) copied
      have output : base+8*(offset/8)+offset%8=base+offset := by omega
      simpa only [output,Nat.add_assoc] using bytes
  · rw [if_neg inPrefix]
    rw [if_neg (by omega : ¬(offset/8<68*count ∧ (offset/8)%68=3)),
      if_neg (by omega : ¬offset/8<68*count)] at copied
    have bytes:=nonce_word_equal_bytes before after base (offset/8)
      (offset/8-count) (offset%8) aligned (by omega) copied
    have output : base+8*(offset/8)+offset%8=base+offset := by omega
    have source : base+8*(offset/8-count)+offset%8=base+(offset-8*count) := by omega
    simpa only [output,source] using bytes

theorem nonce_expand_byte_source_bound (count words offset source : Nat)
    (inside : offset<544*count+8*words)
    (selected : NonceCodec.expandedSource count offset=some source) :
    source<536*count+8*words := by
  rw [nonce_expand_word_index] at selected
  by_cases prefixBound : offset<544*count
  · rw [if_pos prefixBound] at selected
    split at selected
    · contradiction
    · have sourceEq:=Option.some.inj selected
      have bound:=nonce_expand_source_bound (offset/8) count (by omega)
      omega
  · rw [if_neg prefixBound] at selected
    have sourceEq:=Option.some.inj selected
    omega

theorem nonce_expand_memory_bytes (base count words : Nat) (before after : MachineState)
    (aligned : base%8=0) (effect : NonceFullExpandMemory base count words before after) :
    nonceMemoryBytes after base (544*count+8*words)=
      NonceCodec.expand 0 count (nonceMemoryBytes before base (536*count+8*words)) := by
  have lengthBefore : (nonceMemoryBytes before base (536*count+8*words)).length=536*count+8*words := by
    simp only [nonceMemoryBytes,List.length_map,List.length_range]
  have enough : 536*count ≤ (nonceMemoryBytes before base (536*count+8*words)).length := by
    rw [lengthBefore]; omega
  apply List.ext_getElem
  · rw [NonceCodec.expand_length 0 count _ enough,lengthBefore]
    simp only [nonceMemoryBytes,List.length_map,List.length_range]
    omega
  · intro offset afterBound expandedBound
    have inside : offset<544*count+8*words := by
      simpa only [nonceMemoryBytes,List.length_map,List.length_range] using afterBound
    have selected:=NonceCodec.expand_index 0 count
      (nonceMemoryBytes before base (536*count+8*words)) enough offset
    rw [List.getElem?_eq_getElem expandedBound] at selected
    have byteEq:=nonce_expand_full_byte base count words before after aligned effect offset inside
    cases choice : NonceCodec.expandedSource count offset with
    | none =>
      rw [choice] at selected byteEq
      simp only [nonceMemoryBytes,List.getElem_map,List.getElem_range]
      exact byteEq.trans (Option.some.inj selected).symm
    | some source =>
      rw [choice] at selected byteEq
      have bound:=nonce_expand_byte_source_bound count words offset source inside choice
      simp only [nonceMemoryBytes,List.getElem?_map] at selected
      rw [List.getElem?_range bound] at selected
      simp only [Option.map_some] at selected
      simp only [nonceMemoryBytes,List.getElem_map,List.getElem_range]
      exact byteEq.trans (Option.some.inj selected).symm
end CommitGolfCandidate
