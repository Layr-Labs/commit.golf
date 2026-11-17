import CommitGolfCandidate.NonceCompactFullMemory
import CommitGolfCandidate.NonceWordBytes
import CommitGolfCandidate.NonceCodecWordIndex

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open NonceCopyMemory
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

def nonceMemoryBytes (state : MachineState) (base length : Nat) : List Byte :=
  (List.range length).map (fun offset => state.getByte (BitVec.ofNat 64 (base+offset)))

theorem nonce_codec_source_bound (count words index : Nat) (inside : index<536*count+8*words) :
    NonceCodec.sourceOffset count index<544*count+8*words := by
  rw [nonce_codec_word_index]
  split
  · unfold noncePackedSourceWord
    split <;> omega
  · omega

theorem nonce_compact_full_byte (base count words : Nat) (before after : MachineState)
    (aligned : base%8=0) (effect : NonceFullCompactMemory base count words before after)
    (offset : Nat) (inside : offset<536*count+8*words) :
    after.getByte (BitVec.ofNat 64 (base+offset))=
      before.getByte (BitVec.ofNat 64 (base+NonceCodec.sourceOffset count offset)) := by
  have wordBound : offset/8<67*count+words := by omega
  have copied:=effect.copied (offset/8) wordBound
  have bytes:=nonce_word_equal_bytes before after base (offset/8)
    (if offset/8<67*count then noncePackedSourceWord (offset/8) else offset/8+count)
    (offset%8) aligned (by omega) copied
  have output : base+8*(offset/8)+offset%8=base+offset := by omega
  have source : base+8*(if offset/8<67*count then noncePackedSourceWord (offset/8) else offset/8+count)+offset%8=
      base+NonceCodec.sourceOffset count offset := by
    rw [nonce_codec_word_index]
    by_cases inPrefix : offset<536*count
    · rw [if_pos inPrefix,if_pos (by omega : offset/8<67*count)]
      omega
    · rw [if_neg inPrefix,if_neg (by omega : ¬offset/8<67*count)]
      omega
  simpa only [output,source] using bytes

theorem nonce_compact_memory_bytes (base count words : Nat) (before after : MachineState)
    (aligned : base%8=0) (effect : NonceFullCompactMemory base count words before after) :
    nonceMemoryBytes after base (536*count+8*words)=
      NonceCodec.compact count (nonceMemoryBytes before base (544*count+8*words)) := by
  have lengthBefore : (nonceMemoryBytes before base (544*count+8*words)).length=544*count+8*words := by
    simp only [nonceMemoryBytes,List.length_map,List.length_range]
  have enough : 544*count ≤ (nonceMemoryBytes before base (544*count+8*words)).length := by
    rw [lengthBefore]
    omega
  apply List.ext_getElem
  · rw [NonceCodec.compact_length count _ enough,lengthBefore]
    simp only [nonceMemoryBytes,List.length_map,List.length_range]
    omega
  · intro offset afterBound compactBound
    have inside : offset<536*count+8*words := by
      simpa only [nonceMemoryBytes,List.length_map,List.length_range] using afterBound
    have selected:=NonceCodec.compact_index count
      (nonceMemoryBytes before base (544*count+8*words)) enough offset
    have sourceBound:=nonce_codec_source_bound count words offset inside
    rw [List.getElem?_eq_getElem compactBound] at selected
    simp only [nonceMemoryBytes,List.getElem?_map] at selected
    rw [List.getElem?_range sourceBound] at selected
    simp only [Option.map_some] at selected
    have byteEq:=Option.some.inj selected
    simp only [nonceMemoryBytes,List.getElem_map,List.getElem_range]
    exact (nonce_compact_full_byte base count words before after aligned effect offset inside).trans byteEq.symm

end CommitGolfCandidate
