import CommitGolfCandidate.NonceCompactPrefixMemory
import CommitGolfCandidate.Memory

/-! Refinement of copied machine words to the interpreter's actual byte reads.
The low-byte offset is unchanged by the whole-word nonce padding removal. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open NonceCopyMemory
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

theorem nonce_aligned_byte (state : MachineState) (base offset : Nat) (aligned : base%8=0) :
    state.getByte (BitVec.ofNat 64 (base+offset))=
      extractByte (state.getMem (address base (offset/8))) (offset%8) := by
  have decomposition : base+offset=8*(base/8+offset/8)+offset%8 := by omega
  have wordBase : 8*(base/8+offset/8)=base+8*(offset/8) := by omega
  rw [decomposition, aligned_byte state (base/8+offset/8) (offset%8) (by omega)]
  rw [Nat.div_eq_of_lt (by omega : offset%8<8), Nat.mul_zero, Nat.add_zero,
    Nat.mod_mod, wordBase]
  rfl

theorem nonce_word_equal_bytes (before after : MachineState) (base output source byte : Nat)
    (aligned : base%8=0) (byteBound : byte<8)
    (copied : after.getMem (address base output)=before.getMem (address base source)) :
    after.getByte (BitVec.ofNat 64 (base+8*output+byte))=
      before.getByte (BitVec.ofNat 64 (base+8*source+byte)) := by
  have outputIndex : (8*output+byte)/8=output := by omega
  have sourceIndex : (8*source+byte)/8=source := by omega
  have outputByte : (8*output+byte)%8=byte := by omega
  have sourceByte : (8*source+byte)%8=byte := by omega
  rw [Nat.add_assoc, Nat.add_assoc base (8*source) byte,
    nonce_aligned_byte after base (8*output+byte) aligned,
    nonce_aligned_byte before base (8*source+byte) aligned,
    outputIndex, sourceIndex, outputByte, sourceByte, copied]

theorem nonce_compact_prefix_bytes (base count : Nat) (before after : MachineState)
    (aligned : base%8=0) (preserved : NonceCompactPrefixMemory base count 0 before after)
    (offset : Nat) (inside : offset<536*count) :
    after.getByte (BitVec.ofNat 64 (base+offset))=
      before.getByte (BitVec.ofNat 64
        (base+8*noncePackedSourceWord (offset/8)+offset%8)) := by
  have wordBound : offset/8<67*count := by omega
  have copied:=preserved.copied (offset/8) (by simpa using wordBound)
  have bytes:=nonce_word_equal_bytes before after base (offset/8)
    (noncePackedSourceWord (offset/8)) (offset%8) aligned (by omega) copied
  have offsetEq : base+8*(offset/8)+offset%8=base+offset := by omega
  simpa only [offsetEq] using bytes

end CommitGolfCandidate
