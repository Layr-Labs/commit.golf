import CommitGolfCandidate.LateMemory

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

/-- Joining two adjacent reads in little-endian order reconstructs the whole read. -/
theorem read_join (s : MachineState) (a low high : Nat) :
    readBuffer s (a+low) high ++ readBuffer s a low =
      (readBuffer s a (low+high)).extractLsb' 0 (8*high+8*low) := by
  have first := read_buffer_slice s a (low+high) 0 low (by omega)
  have second := read_buffer_slice s a (low+high) low high (by omega)
  simp only [Nat.add_zero, Nat.mul_zero] at first
  rw [← first, ← second]
  exact BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by omega)

private theorem write_read_digest (s : MachineState) (a : Nat) (w : Digest) :
    readBuffer (writeBits s (BitVec.ofNat 64 a) w) a 32 = w := by
  have h := read_serialized_slice (writeBits s (BitVec.ofNat 64 a) w) w a 0 32 (by
    intro j hj
    simpa only [Nat.zero_add, BitVec.ofNat_add] using
      write_bits_byte s (BitVec.ofNat 64 a) w j (by omega) (by decide))
  exact h.trans BitVec.extractLsb'_eq_self

/-- The first call overwrites bytes 64..95 of the entry. Its new read sees the
32-byte reply followed by the original 64 bytes, even with the in-place write. -/
theorem first_two_inputs (s : MachineState) (a : Nat) (v : Entry)
    (m : readBuffer s a 256 = v) (h : Compression) (bound : a + 256 ≤ 2^64) :
    let s₁ := writeBits s (BitVec.ofNat 64 (a+64)) (h (firstBlock v))
    readBuffer s a 96 = firstBlock v ∧
    readBuffer s₁ (a+64) 96 = middleBlock v (h (firstBlock v)) ∧
    readBuffer s₁ (a+160) 96 = lastBlock v := by
  subst v
  dsimp only
  constructor
  · exact (read_buffer_slice s a 256 0 96 (by decide)).symm
  let w := h (firstBlock (readBuffer s a 256))
  let t := writeBits s (BitVec.ofNat 64 (a+64)) w
  have untouched (offset count : Nat) (lower : 96 ≤ offset) (upper : offset+count ≤ 256) :
      readBuffer t (a+offset) count = readBuffer s (a+offset) count := by
    apply write_bits_read_outside
    · change a+64+32 ≤ 2^64; omega
    · omega
    · right; change a+64+32 ≤ a+offset; omega
  constructor
  · change readBuffer t (a+64) 96 = _
    have split := read_join t (a+64) 32 64
    rw [show a+64+32 = a+96 by omega, untouched 96 64 (by decide) (by decide),
      show readBuffer t (a+64) 32 = w from write_read_digest s (a+64) w] at split
    have same : (readBuffer t (a+64) 96).extractLsb' 0 768 = readBuffer t (a+64) 96 :=
      BitVec.extractLsb'_eq_self
    change _ = (readBuffer t (a+64) 96).extractLsb' 0 768 at split
    rw [same] at split
    rw [← split, ← read_buffer_slice s a 256 96 64 (by decide)]
    rfl
  · change readBuffer t (a+160) 96 = _
    rw [untouched 160 96 (by decide) (by decide), ← read_buffer_slice s a 256 160 96 (by decide)]
    rfl

/-- Decode the two final input row layouts, including all eight intervening zero bytes. -/
theorem even_row (s : MachineState) (base : Nat) (a b : Digest) (salt : Salt)
    (left : readBuffer s base 32 = a) (right : readBuffer s (base+32) 32 = b)
    (pad : readBuffer s (base+64) 8 = 0) (random : readBuffer s (base+72) 24 = salt) :
    readBuffer s base 96 = finalBlock false salt a b := by
  have j₁ := read_join s (base+64) 8 24
  have j₂ := read_join s (base+32) 32 32
  have j₃ := read_join s base 32 64
  rw [show base+64+8 = base+72 by omega, random, pad] at j₁
  rw [show base+32+32 = base+64 by omega, right] at j₂
  rw [left] at j₃
  change _ = (readBuffer s (base+64) 32).extractLsb' 0 256 at j₁
  change _ = (readBuffer s (base+32) 64).extractLsb' 0 512 at j₂
  change _ = (readBuffer s base 96).extractLsb' 0 768 at j₃
  rw [BitVec.extractLsb'_eq_self] at j₁ j₂ j₃
  rw [← j₃, ← j₂, ← j₁]
  rfl

theorem odd_row (s : MachineState) (base : Nat) (a b : Digest) (salt : Salt)
    (random : readBuffer s base 24 = salt) (pad : readBuffer s (base+24) 8 = 0)
    (left : readBuffer s (base+32) 32 = a) (right : readBuffer s (base+64) 32 = b) :
    readBuffer s base 96 = finalBlock true salt a b := by
  have j₁ := read_join s (base+32) 32 32
  rw [show base+32+32 = base+64 by omega, left, right] at j₁
  have j₂ := read_join s (base+24) 8 64
  rw [show base+24+8 = base+32 by omega, pad] at j₂
  have j₃ := read_join s base 24 72
  rw [random] at j₃
  change _ = (readBuffer s (base+32) 64).extractLsb' 0 512 at j₁
  change _ = (readBuffer s (base+24) 72).extractLsb' 0 576 at j₂
  change _ = (readBuffer s base 96).extractLsb' 0 768 at j₃
  rw [BitVec.extractLsb'_eq_self] at j₁ j₂ j₃
  rw [← j₃, ← j₂, ← j₁]
  rfl

end CommitGolfCandidate.Late
