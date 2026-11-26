import CommitGolfCandidate.MoonImage
import CommitGolfCandidate.InputMemory
import CommitGolfCandidate.WriteMemoryCore

/-! Byte-, halfword-, and doubleword-exact memory lemmas for the r=1 machine images:
- Halfword `LHU`/`SH` semantics and `sh zero, 30(a2)` -> `mask240`
- 96-byte compression buffer decompositions (Call 0, leaf chain, 3-ary, binary gap)
- ABI initial buffer contents for commit, opening, and check under our exact layout
- `DIVU`/`REMU` by 3 on valid 24-bit leaf indices and sorted-value index correspondence. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

/-! ### Byte/Halfword/Dword Memory Semantics -/

private theorem byteOffset_lt (a : Word) : byteOffset a < 8 := by
  unfold byteOffset
  rw [BitVec.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

private theorem byteOffset_eq_mod (a : Word) : byteOffset a = a.toNat % 8 := by
  unfold byteOffset
  rw [BitVec.toNat_and]
  change a.toNat &&& (2 ^ 3 - 1) = a.toNat % 2 ^ 3
  exact Nat.and_two_pow_sub_one_eq_mod _ _

private theorem alignToDword_add_byteOffset (a : Word) :
    alignToDword a + BitVec.ofNat 64 (byteOffset a) = a := by
  unfold alignToDword byteOffset
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have disj : (a &&& ~~~7#64) &&& (a &&& 7#64) = 0 := by
    ext i; simp only [BitVec.getElem_and, BitVec.getElem_not]
    cases (7#64)[i] <;> simp
  have comb : (a &&& ~~~7#64) ||| (a &&& 7#64) = a := by
    ext i; simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not]
    cases (7#64)[i] <;> simp
  rw [BitVec.add_eq_or_of_and_eq_zero _ _ disj, comb]

theorem alignToDword_ofNat_eq (base off : Nat) (hoff : off < 8) (hbase : base % 8 = 0) :
    alignToDword (BitVec.ofNat 64 (base + off)) = BitVec.ofNat 64 base := by
  have hbo : byteOffset (BitVec.ofNat 64 (base + off)) = off := by
    rw [byteOffset_eq_mod, BitVec.toNat_ofNat]
    omega
  have hp := alignToDword_add_byteOffset (BitVec.ofNat 64 (base + off))
  rw [hbo] at hp
  have hj : BitVec.ofNat 64 base + BitVec.ofNat 64 off = BitVec.ofNat 64 (base + off) :=
    (BitVec.ofNat_add _ _).symm
  have hc := congrArg (fun v : Word => v - BitVec.ofNat 64 off) (hp.trans hj.symm)
  simpa only [BitVec.add_sub_cancel] using hc

private theorem extractByte_replaceHalfword_lo (w : Word) (h : BitVec 16) (pos : Nat) (hpos : pos < 4) :
    extractByte (replaceHalfword w pos h) (2 * pos) = h.extractLsb' 0 8 := by
  interval_cases pos <;>
    apply BitVec.eq_of_getLsbD_eq <;> intro b hb <;> interval_cases b <;>
    simp [extractByte, replaceHalfword]

private theorem extractByte_replaceHalfword_hi (w : Word) (h : BitVec 16) (pos : Nat) (hpos : pos < 4) :
    extractByte (replaceHalfword w pos h) (2 * pos + 1) = h.extractLsb' 8 8 := by
  interval_cases pos <;>
    apply BitVec.eq_of_getLsbD_eq <;> intro b hb <;> interval_cases b <;>
    simp [extractByte, replaceHalfword]

private theorem extractByte_replaceHalfword_other (w : Word) (h : BitVec 16) (pos k : Nat)
    (hpos : pos < 4) (hk : k < 8) (hne0 : k ≠ 2 * pos) (hne1 : k ≠ 2 * pos + 1) :
    extractByte (replaceHalfword w pos h) k = extractByte w k := by
  interval_cases pos <;> interval_cases k <;>
    first
    | exact (hne0 rfl).elim
    | exact (hne1 rfl).elim
    | (apply BitVec.eq_of_getLsbD_eq; intro b hb; interval_cases b <;>
       simp [extractByte, replaceHalfword])

private theorem extractHalfword_bytes (w : Word) (pos : Nat) (hpos : pos < 4) :
    (extractHalfword w pos).extractLsb' 0 8 = extractByte w (2 * pos) ∧
    (extractHalfword w pos).extractLsb' 8 8 = extractByte w (2 * pos + 1) := by
  constructor <;> (
    interval_cases pos <;>
    apply BitVec.eq_of_getLsbD_eq <;> intro b hb <;> interval_cases b <;>
    simp [extractHalfword, extractByte])

/-- Writing a halfword at a 2-byte aligned address updates exactly its two bytes. -/
theorem setHalfword_getByte (state : MachineState) (addr query : Word) (h : BitVec 16)
    (halign : addr.toNat % 2 = 0) :
    (state.setHalfword addr h).getByte query =
      if query = addr then h.extractLsb' 0 8
      else if query = addr + 1#64 then h.extractLsb' 8 8
      else state.getByte query := by
  have hbo : byteOffset addr = addr.toNat % 8 := byteOffset_eq_mod addr
  have heven : byteOffset addr % 2 = 0 := by omega
  have hpos_lt : byteOffset addr / 2 < 4 := by have := byteOffset_lt addr; omega
  have hparts_a := alignToDword_add_byteOffset addr
  have hparts_q := alignToDword_add_byteOffset query
  by_cases hq0 : query = addr
  · subst query
    simp only [if_true, MachineState.setHalfword, MachineState.getByte, MachineState.getMem_setMem_eq]
    have h2 : 2 * (byteOffset addr / 2) = byteOffset addr := by omega
    simpa only [h2] using extractByte_replaceHalfword_lo (state.getMem (alignToDword addr)) h
      (byteOffset addr / 2) hpos_lt
  · rw [if_neg hq0]
    by_cases hq1 : query = addr + 1#64
    · subst query
      rw [if_pos rfl]
      have hbo1 : byteOffset (addr + 1#64) = byteOffset addr + 1 := by
        rw [byteOffset_eq_mod, BitVec.toNat_add]
        have ha : addr.toNat < 2 ^ 64 := addr.isLt
        change (addr.toNat + 1) % 2 ^ 64 % 8 = _
        have : (addr.toNat + 1) % 2 ^ 64 % 8 = (addr.toNat + 1) % 8 := by
          by_cases hwrap : addr.toNat + 1 < 2 ^ 64
          · rw [Nat.mod_eq_of_lt hwrap]
          · have : addr.toNat = 2 ^ 64 - 1 := by omega
            omega
        rw [this]; omega
      have hal1 : alignToDword (addr + 1#64) = alignToDword addr := by
        have hp1 := alignToDword_add_byteOffset (addr + 1#64)
        rw [hbo1] at hp1
        have hjoin : alignToDword addr + BitVec.ofNat 64 (byteOffset addr + 1) = addr + 1#64 := by
          rw [BitVec.ofNat_add, ← BitVec.add_assoc, hparts_a]
        have hc := congrArg (fun v : Word => v - BitVec.ofNat 64 (byteOffset addr + 1)) (hp1.trans hjoin.symm)
        simpa only [BitVec.add_sub_cancel] using hc
      simp only [MachineState.setHalfword, MachineState.getByte, hal1, MachineState.getMem_setMem_eq, hbo1]
      have h21 : 2 * (byteOffset addr / 2) + 1 = byteOffset addr + 1 := by omega
      simpa only [h21] using extractByte_replaceHalfword_hi (state.getMem (alignToDword addr)) h
        (byteOffset addr / 2) hpos_lt
    · rw [if_neg hq1]
      by_cases hdw : alignToDword query = alignToDword addr
      · have hne0 : byteOffset query ≠ 2 * (byteOffset addr / 2) := by
          intro heq
          apply hq0
          rw [← hparts_q, ← hparts_a, hdw, heq, show 2 * (byteOffset addr / 2) = byteOffset addr by omega]
        have hne1 : byteOffset query ≠ 2 * (byteOffset addr / 2) + 1 := by
          intro heq
          apply hq1
          rw [← hparts_q, ← hparts_a, hdw, heq,
            show 2 * (byteOffset addr / 2) + 1 = byteOffset addr + 1 by omega,
            BitVec.ofNat_add, ← BitVec.add_assoc]
        simp only [MachineState.setHalfword, MachineState.getByte, hdw, MachineState.getMem_setMem_eq]
        exact extractByte_replaceHalfword_other _ h _ _ hpos_lt (byteOffset_lt query) hne0 hne1
      · simp only [MachineState.setHalfword, MachineState.getByte, MachineState.getMem_setMem_ne hdw]

theorem getHalfword_bytes (state : MachineState) (addr : Word) (halign : addr.toNat % 2 = 0) :
    (state.getHalfword addr).extractLsb' 0 8 = state.getByte addr ∧
    (state.getHalfword addr).extractLsb' 8 8 = state.getByte (addr + 1#64) := by
  have hbo : byteOffset addr = addr.toNat % 8 := byteOffset_eq_mod addr
  have hpos_lt : byteOffset addr / 2 < 4 := by have := byteOffset_lt addr; omega
  have h2 : 2 * (byteOffset addr / 2) = byteOffset addr := by omega
  have hbo1 : byteOffset (addr + 1#64) = byteOffset addr + 1 := by
    rw [byteOffset_eq_mod, BitVec.toNat_add]
    have ha : addr.toNat < 2 ^ 64 := addr.isLt
    change (addr.toNat + 1) % 2 ^ 64 % 8 = _
    have hlt : addr.toNat + 1 < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt hlt]; omega
  have hal1 : alignToDword (addr + 1#64) = alignToDword addr := by
    have hp1 := alignToDword_add_byteOffset (addr + 1#64)
    have hp0 := alignToDword_add_byteOffset addr
    rw [hbo1] at hp1
    have hjoin : alignToDword addr + BitVec.ofNat 64 (byteOffset addr + 1) = addr + 1#64 := by
      rw [BitVec.ofNat_add, ← BitVec.add_assoc, hp0]
    have hc := congrArg (fun v : Word => v - BitVec.ofNat 64 (byteOffset addr + 1)) (hp1.trans hjoin.symm)
    simpa only [BitVec.add_sub_cancel] using hc
  have hb := extractHalfword_bytes (state.getMem (alignToDword addr)) (byteOffset addr / 2) hpos_lt
  constructor
  · simpa only [MachineState.getHalfword, MachineState.getByte, h2] using hb.1
  · simpa only [MachineState.getHalfword, MachineState.getByte, hal1, hbo1, h2] using hb.2

/-- One `LHU` + `SH` pair copies exactly two consecutive bytes and preserves all other bytes. -/
theorem copyHalfword_getByte (state : MachineState) (src dst query : Word)
    (hs : src.toNat % 2 = 0) (hd : dst.toNat % 2 = 0) :
    (state.setHalfword dst (state.getHalfword src)).getByte query =
      if query = dst then state.getByte src
      else if query = dst + 1#64 then state.getByte (src + 1#64)
      else state.getByte query := by
  rw [setHalfword_getByte state dst query _ hd]
  have hb := getHalfword_bytes state src hs
  rw [hb.1, hb.2]

/-- `sh zero, 30(a2)` truncates an aligned 32-byte digest at `addr` to exactly `mask240`! -/
theorem sh_zero_mask240 (state : MachineState) (addr : Nat)
    (halign : addr % 8 = 0) (hbound : addr + 32 ≤ 2 ^ 64) :
    readBuffer (state.setHalfword (BitVec.ofNat 64 (addr + 30)) 0#16) addr 32 =
      mask240 (readBuffer state addr 32) := by
  have halign30 : (BitVec.ofNat 64 (addr + 30)).toNat % 2 = 0 := by
    have hlt : addr + 30 < 2 ^ 64 := by omega
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]; omega
  have hbytes : ∀ j < 32,
      (state.setHalfword (BitVec.ofNat 64 (addr + 30)) 0#16).getByte (BitVec.ofNat 64 (addr + j)) =
        (mask240 (readBuffer state addr 32)).extractLsb' (8 * j) 8 := by
    intro j hj
    rw [setHalfword_getByte state _ _ 0#16 halign30]
    by_cases h30 : j = 30
    · subst h30
      rw [if_pos rfl, mask240_byte_ge30 _ 30 (by omega)]
      decide
    · have hne30 : BitVec.ofNat 64 (addr + j) ≠ BitVec.ofNat 64 (addr + 30) := by
        intro heq
        have hn := congrArg BitVec.toNat heq
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : addr + j < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : addr + 30 < 2 ^ 64)] at hn
        omega
      rw [if_neg hne30]
      by_cases h31 : j = 31
      · subst h31
        have heq31 : BitVec.ofNat 64 (addr + 31) = BitVec.ofNat 64 (addr + 30) + 1#64 := by
          rw [show (1#64 : Word) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
        rw [if_pos heq31, mask240_byte_ge30 _ 31 (by omega)]
        decide
      · have hne31 : BitVec.ofNat 64 (addr + j) ≠ BitVec.ofNat 64 (addr + 30) + 1#64 := by
          intro heq
          have heq' : BitVec.ofNat 64 (addr + j) = BitVec.ofNat 64 (addr + 31) := by
            simpa only [show (1#64 : Word) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add] using heq
          have hn := congrArg BitVec.toNat heq'
          simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : addr + j < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : addr + 31 < 2 ^ 64)] at hn
          omega
        rw [if_neg hne31, mask240_byte_lt30 _ j (by omega), read_buffer_byte state addr 32 j hj]
  have hr := read_serialized_slice (state.setHalfword (BitVec.ofNat 64 (addr + 30)) 0#16)
    (mask240 (readBuffer state addr 32)) addr 0 32 (by simpa only [Nat.zero_add] using hbytes)
  simpa using hr

/-- `setMem` at an 8-byte aligned address updates only bytes in `[addr, addr + 8)`. -/
theorem setMem_getByte_outside (state : MachineState) (addr query val : Word)
    (halign : addr.toNat % 8 = 0)
    (hsep : alignToDword query ≠ addr) :
    (state.setMem addr val).getByte query = state.getByte query := by
  simp only [MachineState.getByte, MachineState.getMem_setMem_ne hsep]

theorem setMem_getByte_ofNat (state : MachineState) (addr q : Nat) (val : Word)
    (halign : addr % 8 = 0) (ha : addr + 8 ≤ 2 ^ 64) (hq : q < 2 ^ 64)
    (hout : q < addr ∨ addr + 8 ≤ q) :
    (state.setMem (BitVec.ofNat 64 addr) val).getByte (BitVec.ofNat 64 q) =
      state.getByte (BitVec.ofNat 64 q) := by
  have hal : (BitVec.ofNat 64 addr).toNat % 8 = 0 := by
    have hlt : addr < 2 ^ 64 := by omega
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]; exact halign
  apply setMem_getByte_outside state _ _ val hal
  intro heq
  have hdec := alignToDword_ofNat_eq (8 * (q / 8)) (q % 8) (by omega) (by omega)
  have hqeq : 8 * (q / 8) + q % 8 = q := by omega
  rw [hqeq] at hdec
  rw [hdec] at heq
  have hn := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 8 * (q / 8) < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : addr < 2 ^ 64)] at hn
  omega

theorem setMem_getByte_inside (state : MachineState) (addr j : Nat) (val : Word)
    (halign : addr % 8 = 0) (hj : j < 8) :
    (state.setMem (BitVec.ofNat 64 addr) val).getByte (BitVec.ofNat 64 (addr + j)) =
      val.extractLsb' (8 * j) 8 := by
  have hal := alignToDword_ofNat_eq addr j hj halign
  have hbo : byteOffset (BitVec.ofNat 64 (addr + j)) = j := by
    rw [byteOffset_eq_mod, BitVec.toNat_ofNat]; omega
  simp only [MachineState.getByte, hal, hbo, MachineState.getMem_setMem_eq]
  apply BitVec.eq_of_toNat_eq
  simp only [extractByte, BitVec.truncate, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.mul_comm 8 j]

/-! ### `readBuffer` Congruences and 96-Byte Splits -/

theorem readBuffer_congr (s1 s2 : MachineState) (addr n : Nat)
    (h : ∀ j < n, s1.getByte (BitVec.ofNat 64 (addr + j)) = s2.getByte (BitVec.ofNat 64 (addr + j))) :
    readBuffer s1 addr n = readBuffer s2 addr n := by
  unfold readBuffer
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [h j (Finset.mem_range.mp hj)]

theorem readBuffer_zero_of_bytes (s : MachineState) (addr n : Nat)
    (h : ∀ j < n, s.getByte (BitVec.ofNat 64 (addr + j)) = 0) :
    readBuffer s addr n = 0 := by
  unfold readBuffer
  have hsum : ∑ j ∈ Finset.range n, (s.getByte (BitVec.ofNat 64 (addr + j))).toNat * 2 ^ (8 * j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [h j (Finset.mem_range.mp hj)]
    simp
  rw [hsum]; rfl

theorem readBuffer_word (s : MachineState) (addr : Nat) (halign : addr % 8 = 0) :
    readBuffer s addr 8 = s.getMem (BitVec.ofNat 64 addr) := by
  have sl := read_buffer_slice s addr 32 0 8 (by decide)
  have wd := read_digest_word s addr 0 halign (by decide)
  simpa only [Nat.mul_zero, Nat.add_zero] using sl.symm.trans wd

private theorem bv_append_toNat {hi lo : Nat} (a : BitVec hi) (b : BitVec lo) :
    (a ++ b).toNat = a.toNat * 2 ^ lo + b.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt b.isLt, Nat.shiftLeft_eq]

private theorem sum_range_bytes_lt (s : MachineState) (addr n : Nat) :
    (∑ i ∈ Finset.range n, (s.getByte (BitVec.ofNat 64 (addr + i))).toNat * 2 ^ (8 * i)) < 2 ^ (8 * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hb := (s.getByte (BitVec.ofNat 64 (addr + n))).isLt
    have ht := Nat.mul_le_mul_right (2 ^ (8 * n)) (show (s.getByte (BitVec.ofNat 64 (addr + n))).toNat ≤ 255 by omega)
    rw [Finset.sum_range_succ, Nat.mul_succ, Nat.pow_add]
    norm_num only [Nat.reducePow]
    omega

private theorem sum_range_bytes_add (s : MachineState) (addr a b : Nat) :
    (∑ i ∈ Finset.range (a + b), (s.getByte (BitVec.ofNat 64 (addr + i))).toNat * 2 ^ (8 * i)) =
      (∑ i ∈ Finset.range a, (s.getByte (BitVec.ofNat 64 (addr + i))).toNat * 2 ^ (8 * i)) +
      2 ^ (8 * a) * (∑ i ∈ Finset.range b, (s.getByte (BitVec.ofNat 64 (addr + a + i))).toNat * 2 ^ (8 * i)) := by
  rw [Finset.sum_range_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [Nat.mul_add, Nat.pow_add, Nat.add_assoc]
  ring

set_option exponentiation.threshold 1024 in
theorem readBuffer_call0 (s : MachineState) (addr : Nat) :
    readBuffer s addr 96 =
      ((readBuffer s (addr + 24) 72) ++ (readBuffer s (addr + 16) 8)) ++ (readBuffer s addr 16) := by
  apply BitVec.eq_of_toNat_eq
  simp only [readBuffer, bv_append_toNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (sum_range_bytes_lt s _ _)]
  have h1 := sum_range_bytes_add s addr 16 80
  have h2 := sum_range_bytes_add s (addr + 16) 8 72
  have h16_8 : addr + 16 + 8 = addr + 24 := by omega
  rw [h16_8] at h2
  rw [show (96 : Nat) = 16 + 80 from rfl, h1, show (80 : Nat) = 8 + 72 from rfl, h2]
  norm_num; ring

set_option exponentiation.threshold 1024 in
theorem readBuffer_ternary (s : MachineState) (addr : Nat) :
    readBuffer s addr 96 =
      ternaryInput (readBuffer s addr 32) (readBuffer s (addr + 32) 32) (readBuffer s (addr + 64) 32) := by
  unfold ternaryInput
  apply BitVec.eq_of_toNat_eq
  simp only [readBuffer, bv_append_toNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (sum_range_bytes_lt s _ _)]
  have h1 := sum_range_bytes_add s addr 32 64
  have h2 := sum_range_bytes_add s (addr + 32) 32 32
  have h64 : addr + 32 + 32 = addr + 64 := by omega
  rw [h64] at h2
  have h96 : (∑ i ∈ Finset.range 96, (s.getByte (BitVec.ofNat 64 (addr + i))).toNat * 2 ^ (8 * i)) =
      (∑ i ∈ Finset.range 32, (s.getByte (BitVec.ofNat 64 (addr + i))).toNat * 2 ^ (8 * i)) +
      2 ^ 256 * ((∑ i ∈ Finset.range 32, (s.getByte (BitVec.ofNat 64 (addr + 32 + i))).toNat * 2 ^ (8 * i)) +
      2 ^ 256 * (∑ i ∈ Finset.range 32, (s.getByte (BitVec.ofNat 64 (addr + 64 + i))).toNat * 2 ^ (8 * i))) := by
    change (∑ i ∈ Finset.range (32 + 64), _) = _
    rw [h1]
    have h2' : (∑ i ∈ Finset.range (32 + 32), (s.getByte (BitVec.ofNat 64 (addr + 32 + i))).toNat * 2 ^ (8 * i)) =
        (∑ i ∈ Finset.range 32, (s.getByte (BitVec.ofNat 64 (addr + 32 + i))).toNat * 2 ^ (8 * i)) +
        2 ^ (8 * 32) * (∑ i ∈ Finset.range 32, (s.getByte (BitVec.ofNat 64 (addr + 64 + i))).toNat * 2 ^ (8 * i)) := h2
    rw [show (∑ i ∈ Finset.range 64, (s.getByte (BitVec.ofNat 64 (addr + 32 + i))).toNat * 2 ^ (8 * i)) =
        (∑ i ∈ Finset.range (32 + 32), (s.getByte (BitVec.ofNat 64 (addr + 32 + i))).toNat * 2 ^ (8 * i)) from rfl, h2']
  rw [h96]; norm_num; ring

theorem readBuffer_binary_of_zero_gap (s : MachineState) (addr : Nat)
    (hgap : readBuffer s (addr + 64) 32 = 0) :
    readBuffer s addr 96 = binaryInput (readBuffer s addr 32) (readBuffer s (addr + 32) 32) := by
  rw [readBuffer_ternary, hgap]; rfl

theorem readBuffer_salt16 (s : MachineState) (addr : Nat) (halign : addr % 8 = 0) :
    readBuffer s addr 16 =
      s.getMem (BitVec.ofNat 64 (addr + 8)) ++ s.getMem (BitVec.ofNat 64 addr) := by
  apply BitVec.eq_of_toNat_eq
  rw [bv_append_toNat, ← readBuffer_word s addr halign, ← readBuffer_word s (addr + 8) (by omega)]
  simp only [readBuffer, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (sum_range_bytes_lt s _ _)]
  rw [show (16 : Nat) = 8 + 8 from rfl, sum_range_bytes_add s addr 8 8]
  norm_num; ring

theorem readBuffer_30_mask240 (s : MachineState) (addr : Nat)
    (htop : s.getByte (BitVec.ofNat 64 (addr + 30)) = 0 ∧ s.getByte (BitVec.ofNat 64 (addr + 31)) = 0)
    (d : Digest)
    (hlo : ∀ j < 30, s.getByte (BitVec.ofNat 64 (addr + j)) = d.extractLsb' (8 * j) 8) :
    readBuffer s addr 32 = mask240 d := by
  have hb : ∀ j < 32, s.getByte (BitVec.ofNat 64 (addr + j)) = (mask240 d).extractLsb' (8 * j) 8 := by
    intro j hj
    by_cases h30 : j < 30
    · rw [hlo j h30, mask240_byte_lt30 d j h30]
    · rw [mask240_byte_ge30 d j (by omega)]
      have hcases : j = 30 ∨ j = 31 := by omega
      rcases hcases with rfl | rfl
      · exact htop.1
      · exact htop.2
  have hr := read_serialized_slice s (mask240 d) addr 0 32 (by simpa only [Nat.zero_add] using hb)
  simpa using hr

theorem writeBits_readBuffer_slice {bits : Nat} (state : MachineState) (address offset count : Nat)
    (answer : BitVec bits) (inside : offset + count ≤ (bits + 7) / 8)
    (bounded : (bits + 7) / 8 ≤ 2 ^ 64) :
    readBuffer (writeBits state (BitVec.ofNat 64 address) answer) (address + offset) count =
      answer.extractLsb' (8 * offset) (8 * count) := by
  apply read_serialized_slice
  intro j hj
  have w := write_bits_byte state (BitVec.ofNat 64 address) answer (offset + j) (by omega) bounded
  simpa only [BitVec.ofNat_add, Nat.add_assoc, BitVec.add_assoc] using w

theorem writeBits_readBuffer_digest (state : MachineState) (address : Nat) (answer : Digest) :
    readBuffer (writeBits state (BitVec.ofNat 64 address) answer) address 32 = answer := by
  have h := writeBits_readBuffer_slice state address 0 32 answer (by decide) (by decide)
  simpa using h

/-! ### `DIVU` / `REMU` by 3 on 24-bit Indices -/

theorem rv64_divu_three (x : Word) :
    rv64_divu x 3#64 = BitVec.ofNat 64 (x.toNat / 3) := by
  unfold rv64_divu
  have hne : (3#64 == 0#64) = false := by decide
  rw [hne]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_udiv, BitVec.toNat_ofNat]
  have hlt : x.toNat / 3 < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt
  rw [Nat.mod_eq_of_lt hlt]
  rfl

theorem rv64_remu_three (x : Word) :
    rv64_remu x 3#64 = BitVec.ofNat 64 (x.toNat % 3) := by
  unfold rv64_remu
  have hne : (3#64 == 0#64) = false := by decide
  rw [hne]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_umod, BitVec.toNat_ofNat]
  have hlt : x.toNat % 3 < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hlt]
  rfl

/-! ### Sorted Position / Value Correspondence -/

def openingIndex (positions : Positions) (ordinal : Nat) : Nat :=
  if h : ordinal < positions.card then
    ((positions.sort (· ≤ ·))[ordinal]'(by simpa using h)).val
  else 0

theorem openingIndex_lt (positions : Positions) (ordinal : Nat) :
    openingIndex positions ordinal < LENGTH := by
  unfold openingIndex
  split
  · exact ((positions.sort (· ≤ ·))[ordinal]'(by simpa)).isLt
  · unfold LENGTH LOG_LENGTH; omega

theorem sorted_value_indices (positions : Positions) :
    (positions.attach.sort (fun i j => i.val ≤ j.val)).map Subtype.val =
      positions.sort (· ≤ ·) := by
  have mapped := Finset.map_sort (r := fun i j : {i // i ∈ positions} => i.val ≤ j.val)
    (r' := fun i j : Index => i ≤ j) (f := Function.Embedding.subtype (· ∈ positions))
    (s := positions.attach) (by intro a _ b _; rfl)
  simpa only [Finset.attach_map_val, Function.Embedding.coe_subtype] using mapped

theorem sorted_value_index (positions : Positions) (ordinal : Nat)
    (present : ordinal < positions.card) :
    (((positions.attach.sort (fun i j => i.val ≤ j.val))[ordinal]'(by simpa using present)).val).val =
      openingIndex positions ordinal := by
  have attachedBound : ordinal < (positions.attach.sort (fun i j => i.val ≤ j.val)).length := by
    simpa using present
  have positionBound : ordinal < (positions.sort (· ≤ ·)).length := by simpa using present
  have same := congrArg (fun list : List Index => list[ordinal]?) (sorted_value_indices positions)
  simp only [List.getElem?_map, List.getElem?_eq_getElem attachedBound,
    List.getElem?_eq_getElem positionBound, Option.map_some, Option.some.injEq] at same
  rw [same]
  simp only [openingIndex, dif_pos present]

/-! ### ABI Initial State Contents for Our Exact Layout -/

private theorem positions_card_le_length (positions : Positions) : positions.card ≤ 16777216 := by
  have h := Finset.card_le_univ positions
  rw [Fintype.card_fin] at h
  exact h

private theorem commit_image_data :
    (submission.image .commit).data = ArtifactEncoding.decode 8 MoonArtifact.commitData := by
  simp only [submission, MoonArtifact.submission]

private theorem opening_image_data :
    (submission.image .opening).data = ArtifactEncoding.decode 8 MoonArtifact.openingData := by
  simp only [submission, MoonArtifact.submission]

private theorem check_image_data :
    (submission.image .check).data = ArtifactEncoding.decode 8 MoonArtifact.openingData := by
  simp only [submission, MoonArtifact.submission]
  exact congrArg (ArtifactEncoding.decode 8) checkData_eq_openingData

theorem commit_initial_msg_byte (message : Message) (index : Index) (offset : Nat)
    (inside : offset < 256) :
    (submission.initialState .commit message).getByte
      (BitVec.ofNat 64 (4096 + 256 * index.val + offset)) =
        (message index).extractLsb' (8 * offset) 8 := by
  have hi : index.val < 16777216 := index.isLt
  rw [initial_input_byte submission .commit message _ (by omega)]
  have hsel : submission.layout.message ≤ 4096 + 256 * index.val + offset ∧
      4096 + 256 * index.val + offset < submission.layout.message + LENGTH * (LEAF_SIZE / 8) := by
    change 4096 ≤ _ ∧ _ < 4096 + 16777216 * 256; omega
  simp only [inputByte, Submission.inputBuffers, List.find?_cons, messageBuffer, hsel, and_self, decide_true]
  have hq : (4096 + 256 * index.val + offset - submission.layout.message) / (LEAF_SIZE / 8) = index.val := by
    change (4096 + 256 * index.val + offset - 4096) / 256 = _; omega
  have hr : (4096 + 256 * index.val + offset - submission.layout.message) % (LEAF_SIZE / 8) = offset := by
    change (4096 + 256 * index.val + offset - 4096) % 256 = _; omega
  simp only [hq, hr, index.isLt, dite_true]

theorem commit_initial_msg_slice (message : Message) (index : Index) (off count : Nat)
    (hbound : off + count ≤ 256) :
    readBuffer (submission.initialState .commit message) (4096 + 256 * index.val + off) count =
      (message index).extractLsb' (8 * off) (8 * count) := by
  apply read_serialized_slice
  intro j hj
  simpa only [Nat.add_assoc] using commit_initial_msg_byte message index (off + j) (by omega)

theorem commit_initial_zero_byte (message : Message) (addr : Nat)
    (hout : addr < 4096 ∨ (4096 + 2 ^ 32 ≤ addr ∧ addr < 68719476032)) :
    (submission.initialState .commit message).getByte (BitVec.ofNat 64 addr) = 0 := by
  rw [initial_input_byte submission .commit message _ (by omega)]
  have hnsel : ¬ (submission.layout.message ≤ addr ∧
      addr < submission.layout.message + LENGTH * (LEAF_SIZE / 8)) := by
    change ¬ (4096 ≤ addr ∧ addr < 4096 + 16777216 * 256); omega
  simp only [inputByte, Submission.inputBuffers, List.find?_cons, messageBuffer, hnsel,
    decide_false, List.find?_nil, commit_dataBase]
  rw [if_neg (by omega)]

theorem commit_initial_data_dword (message : Message) (off : Nat) (hoff : off + 8 ≤ 704) :
    (submission.initialState .commit message).getMem (BitVec.ofNat 64 (68719476032 + off)) =
      packedDword MoonArtifact.commitData off hoff := by
  rw [initial_input_word submission .commit message _ (by omega)]
  unfold packedDword
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt : j < 8 := Finset.mem_range.mp hj
  have hnsel : ¬ (submission.layout.message ≤ 68719476032 + off + j ∧
      68719476032 + off + j < submission.layout.message + LENGTH * (LEAF_SIZE / 8)) := by
    change ¬ (4096 ≤ _ ∧ _ < 4096 + 16777216 * 256); omega
  simp only [inputByte, Submission.inputBuffers, List.find?_cons, messageBuffer, hnsel,
    decide_false, List.find?_nil, commit_dataBase, show 68719476032 ≤ 68719476032 + off + j by omega,
    ite_true, show 68719476032 + off + j - 68719476032 = off + j by omega]
  rw [commit_image_data, getElem?_decode 8 MoonArtifact.commitData (off + j) (by omega), Option.getD_some,
    dif_pos (by omega)]

theorem opening_initial_trapdoor_byte (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (off : Nat) (hoff : off < 1342178336) :
    (submission.initialState .opening (trapdoor, positions)).getByte
      (BitVec.ofNat 64 (4294971424 + off)) = trapdoor.extractLsb' (8 * off) 8 := by
  rw [initial_input_byte submission .opening (trapdoor, positions) _ (by omega)]
  have hsel : submission.layout.trapdoor ≤ 4294971424 + off ∧
      4294971424 + off < submission.layout.trapdoor + (8 * submission.sizes.trapdoor + 7) / 8 := by
    change 4294971424 ≤ _ ∧ _ < 4294971424 + (8 * 1342178336 + 7) / 8; omega
  simp only [inputByte, Submission.inputBuffers, List.find?_cons, fixedBuffer, hsel, and_self,
    decide_true, show 4294971424 + off - submission.layout.trapdoor = off by
      change 4294971424 + off - 4294971424 = off; omega]

theorem opening_initial_trapdoor_slice (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (off count : Nat) (hbound : off + count ≤ 1342178336) :
    readBuffer (submission.initialState .opening (trapdoor, positions)) (4294971424 + off) count =
      trapdoor.extractLsb' (8 * off) (8 * count) := by
  apply read_serialized_slice
  intro j hj
  simpa only [Nat.add_assoc] using opening_initial_trapdoor_byte trapdoor positions (off + j) (by omega)

theorem opening_initial_index (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (ordinal : Nat) (hord : ordinal < positions.card) :
    (submission.initialState .opening (trapdoor, positions)).getMem
      (BitVec.ofNat 64 (5637149760 + 8 * ordinal)) =
        BitVec.ofNat 64 (openingIndex positions ordinal) := by
  have hcard := positions_card_le_length positions
  let idx := (positions.sort (· ≤ ·))[ordinal]'(by simpa using hord)
  have hidx : idx.val < 16777216 := idx.isLt
  have hbytes : ∀ j < 8,
      (submission.initialState .opening (trapdoor, positions)).getByte
        (BitVec.ofNat 64 (5637149760 + 8 * ordinal + j)) =
          (BitVec.ofNat 64 idx.val).extractLsb' (8 * j) 8 := by
    intro j hj
    rw [initial_input_byte submission .opening (trapdoor, positions) _ (by omega)]
    have hnot_td : ¬ (submission.layout.trapdoor ≤ 5637149760 + 8 * ordinal + j ∧
        5637149760 + 8 * ordinal + j < submission.layout.trapdoor + (8 * submission.sizes.trapdoor + 7) / 8) := by
      change ¬ (4294971424 ≤ _ ∧ _ < 4294971424 + (8 * 1342178336 + 7) / 8); omega
    have hsel : submission.layout.indices ≤ 5637149760 + 8 * ordinal + j ∧
        5637149760 + 8 * ordinal + j < submission.layout.indices + 8 * (positions.sort (· ≤ ·)).length := by
      rw [Finset.length_sort]; change 5637149760 ≤ _ ∧ _ < 5637149760 + 8 * positions.card; omega
    simp only [inputByte, Submission.inputBuffers, List.find?_cons, fixedBuffer, positionsBuffer,
      hnot_td, decide_false, hsel, and_self, decide_true]
    have hq : (5637149760 + 8 * ordinal + j - submission.layout.indices) / 8 = ordinal := by
      change (5637149760 + 8 * ordinal + j - 5637149760) / 8 = _; omega
    have hr : (5637149760 + 8 * ordinal + j - submission.layout.indices) % 8 = j := by
      change (5637149760 + 8 * ordinal + j - 5637149760) % 8 = _; omega
    rw [hq, hr, List.getElem?_eq_getElem (by simpa using hord)]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.extractLsb', Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (by omega : idx.val < 2 ^ 64)]
    rfl
  have hd := read_serialized_slice (submission.initialState .opening (trapdoor, positions))
    (BitVec.ofNat 64 idx.val) (5637149760 + 8 * ordinal) 0 8 (by simpa only [Nat.zero_add] using hbytes)
  rw [readBuffer_word _ _ (by omega)] at hd
  simpa only [Nat.mul_zero, Nat.mul_one, BitVec.extractLsb'_eq_self, openingIndex, dif_pos hord] using hd

theorem opening_initial_zero_low (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (addr : Nat) (haddr : addr < 4294971424) :
    (submission.initialState .opening (trapdoor, positions)).getByte (BitVec.ofNat 64 addr) = 0 := by
  have hcard := positions_card_le_length positions
  rw [initial_input_byte submission .opening (trapdoor, positions) _ (by omega)]
  have h1 : ¬ (submission.layout.trapdoor ≤ addr ∧
      addr < submission.layout.trapdoor + (8 * submission.sizes.trapdoor + 7) / 8) := by
    change ¬ (4294971424 ≤ addr ∧ _); omega
  have h2 : ¬ (submission.layout.indices ≤ addr ∧
      addr < submission.layout.indices + 8 * (positions.sort (· ≤ ·)).length) := by
    change ¬ (5637149760 ≤ addr ∧ _); omega
  simp only [inputByte, Submission.inputBuffers, List.find?_cons, fixedBuffer, positionsBuffer,
    h1, h2, decide_false, List.find?_nil, opening_dataBase]
  rw [if_neg (by omega)]

theorem opening_initial_data_dword (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (off : Nat) (hoff : off + 8 ≤ 800) :
    (submission.initialState .opening (trapdoor, positions)).getMem (BitVec.ofNat 64 (68719475936 + off)) =
      packedDword MoonArtifact.openingData off hoff := by
  have hcard := positions_card_le_length positions
  rw [initial_input_word submission .opening (trapdoor, positions) _ (by omega)]
  unfold packedDword
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt : j < 8 := Finset.mem_range.mp hj
  have h1 : ¬ (submission.layout.trapdoor ≤ 68719475936 + off + j ∧
      68719475936 + off + j < submission.layout.trapdoor + (8 * submission.sizes.trapdoor + 7) / 8) := by
    change ¬ (4294971424 ≤ _ ∧ _ < 4294971424 + (8 * 1342178336 + 7) / 8); omega
  have h2 : ¬ (submission.layout.indices ≤ 68719475936 + off + j ∧
      68719475936 + off + j < submission.layout.indices + 8 * (positions.sort (· ≤ ·)).length) := by
    rw [Finset.length_sort]; change ¬ (5637149760 ≤ _ ∧ _ < 5637149760 + 8 * positions.card); omega
  simp only [inputByte, Submission.inputBuffers, List.find?_cons, fixedBuffer, positionsBuffer,
    h1, h2, decide_false, List.find?_nil, opening_dataBase,
    show 68719475936 ≤ 68719475936 + off + j by omega, ite_true,
    show 68719475936 + off + j - 68719475936 = off + j by omega]
  rw [opening_image_data, getElem?_decode 8 MoonArtifact.openingData (off + j) (by omega), Option.getD_some,
    dif_pos (by omega)]

theorem check_initial_commitment (input : CheckInput) :
    readBuffer (submission.initialState .check input) 4294971392 32 = input.commitment := by
  have hd := read_serialized_slice (submission.initialState .check input) input.commitment 4294971392 0 32 (by
    intro j hj
    rw [initial_input_byte submission .check input _ (by omega)]
    have hsel : submission.layout.commitment ≤ 4294971392 + j ∧
        4294971392 + j < submission.layout.commitment + (DIGEST_BITS + 7) / 8 := by
      change 4294971392 ≤ _ ∧ _ < 4294971392 + 32; omega
    simp only [inputByte, Submission.inputBuffers, List.find?_cons, fixedBuffer, hsel, and_self,
      decide_true, Nat.zero_add, show 4294971392 + j - submission.layout.commitment = j by
        change 4294971392 + j - 4294971392 = j; omega])
  exact hd.trans BitVec.extractLsb'_eq_self

theorem check_initial_index (input : CheckInput) (ordinal : Nat) (hord : ordinal < input.positions.card) :
    (submission.initialState .check input).getMem (BitVec.ofNat 64 (5637149760 + 8 * ordinal)) =
      BitVec.ofNat 64 (openingIndex input.positions ordinal) := by
  have hcard := positions_card_le_length input.positions
  let idx := (input.positions.sort (· ≤ ·))[ordinal]'(by simpa using hord)
  have hidx : idx.val < 16777216 := idx.isLt
  have hbytes : ∀ j < 8,
      (submission.initialState .check input).getByte (BitVec.ofNat 64 (5637149760 + 8 * ordinal + j)) =
        (BitVec.ofNat 64 idx.val).extractLsb' (8 * j) 8 := by
    intro j hj
    rw [initial_input_byte submission .check input _ (by omega)]
    have h1 : ¬ (submission.layout.commitment ≤ 5637149760 + 8 * ordinal + j ∧
        5637149760 + 8 * ordinal + j < submission.layout.commitment + (DIGEST_BITS + 7) / 8) := by
      change ¬ (4294971392 ≤ _ ∧ _ < 4294971392 + 32); omega
    have hsel : submission.layout.indices ≤ 5637149760 + 8 * ordinal + j ∧
        5637149760 + 8 * ordinal + j < submission.layout.indices + 8 * (input.positions.sort (· ≤ ·)).length := by
      rw [Finset.length_sort]; change 5637149760 ≤ _ ∧ _ < 5637149760 + 8 * input.positions.card; omega
    simp only [inputByte, Submission.inputBuffers, List.find?_cons, fixedBuffer, positionsBuffer,
      h1, decide_false, hsel, and_self, decide_true]
    have hq : (5637149760 + 8 * ordinal + j - submission.layout.indices) / 8 = ordinal := by
      change (5637149760 + 8 * ordinal + j - 5637149760) / 8 = _; omega
    have hr : (5637149760 + 8 * ordinal + j - submission.layout.indices) % 8 = j := by
      change (5637149760 + 8 * ordinal + j - 5637149760) % 8 = _; omega
    rw [hq, hr, List.getElem?_eq_getElem (by simpa using hord)]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.extractLsb', Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (by omega : idx.val < 2 ^ 64)]
    rfl
  have hd := read_serialized_slice (submission.initialState .check input)
    (BitVec.ofNat 64 idx.val) (5637149760 + 8 * ordinal) 0 8 (by simpa only [Nat.zero_add] using hbytes)
  rw [readBuffer_word _ _ (by omega)] at hd
  simpa only [Nat.mul_zero, Nat.mul_one, BitVec.extractLsb'_eq_self, openingIndex, dif_pos hord] using hd

theorem check_initial_value_byte (input : CheckInput) (ordinal offset : Nat)
    (hord : ordinal < input.positions.card) (hoff : offset < 256) :
    (submission.initialState .check input).getByte
      (BitVec.ofNat 64 (5771367488 + 256 * ordinal + offset)) =
      (input.values ((input.positions.attach.sort (fun i j => i.val ≤ j.val))[ordinal]'(by
        simpa using hord))).extractLsb' (8 * offset) 8 := by
  have hcard := positions_card_le_length input.positions
  rw [initial_input_byte submission .check input _ (by omega)]
  have h1 : ¬ (submission.layout.commitment ≤ 5771367488 + 256 * ordinal + offset ∧
      5771367488 + 256 * ordinal + offset < submission.layout.commitment + (DIGEST_BITS + 7) / 8) := by
    change ¬ (4294971392 ≤ _ ∧ _ < 4294971392 + 32); omega
  have h2 : ¬ (submission.layout.indices ≤ 5771367488 + 256 * ordinal + offset ∧
      5771367488 + 256 * ordinal + offset < submission.layout.indices + 8 * (input.positions.sort (· ≤ ·)).length) := by
    rw [Finset.length_sort]; change ¬ (5637149760 ≤ _ ∧ _ < 5637149760 + 8 * input.positions.card); omega
  have hsel : submission.layout.values ≤ 5771367488 + 256 * ordinal + offset ∧
      5771367488 + 256 * ordinal + offset < submission.layout.values + (LEAF_SIZE / 8) * (input.positions.attach.sort (fun i j => i.val ≤ j.val)).length := by
    rw [Finset.length_sort, Finset.card_attach]
    change 5771367488 ≤ _ ∧ _ < 5771367488 + 256 * input.positions.card; omega
  simp only [inputByte, Submission.inputBuffers, List.find?_cons, fixedBuffer, positionsBuffer,
    valuesBuffer, h1, h2, decide_false, hsel, and_self, decide_true]
  have hq : (5771367488 + 256 * ordinal + offset - submission.layout.values) / (LEAF_SIZE / 8) = ordinal := by
    change (5771367488 + 256 * ordinal + offset - 5771367488) / 256 = _; omega
  have hr : (5771367488 + 256 * ordinal + offset - submission.layout.values) % (LEAF_SIZE / 8) = offset := by
    change (5771367488 + 256 * ordinal + offset - 5771367488) % 256 = _; omega
  rw [hq, hr, List.getElem?_eq_getElem (by simpa using hord)]

theorem check_initial_value_slice (input : CheckInput) (ordinal off count : Nat)
    (hord : ordinal < input.positions.card) (hbound : off + count ≤ 256) :
    readBuffer (submission.initialState .check input) (5771367488 + 256 * ordinal + off) count =
      (input.values ((input.positions.attach.sort (fun i j => i.val ≤ j.val))[ordinal]'(by
        simpa using hord))).extractLsb' (8 * off) (8 * count) := by
  apply read_serialized_slice
  intro j hj
  simpa only [Nat.add_assoc] using check_initial_value_byte input ordinal (off + j) hord (by omega)

theorem check_initial_proof_byte (input : CheckInput)
    (hvalid : input.proof.length ≤ submission.sizes.proof) (off : Nat)
    (hoff : off < input.proof.length) :
    (submission.initialState .check input).getByte (BitVec.ofNat 64 (10066334784 + off)) =
      input.proof[off] := by
  have hcard := positions_card_le_length input.positions
  change input.proof.length ≤ 8422172696 at hvalid
  rw [initial_input_byte submission .check input _ (by omega)]
  have h1 : ¬ (submission.layout.commitment ≤ 10066334784 + off ∧
      10066334784 + off < submission.layout.commitment + (DIGEST_BITS + 7) / 8) := by
    change ¬ (4294971392 ≤ _ ∧ _ < 4294971392 + 32); omega
  have h2 : ¬ (submission.layout.indices ≤ 10066334784 + off ∧
      10066334784 + off < submission.layout.indices + 8 * (input.positions.sort (· ≤ ·)).length) := by
    rw [Finset.length_sort]; change ¬ (5637149760 ≤ _ ∧ _ < 5637149760 + 8 * input.positions.card); omega
  have h3 : ¬ (submission.layout.values ≤ 10066334784 + off ∧
      10066334784 + off < submission.layout.values + (LEAF_SIZE / 8) * (input.positions.attach.sort (fun i j => i.val ≤ j.val)).length) := by
    rw [Finset.length_sort, Finset.card_attach]
    change ¬ (5771367488 ≤ _ ∧ _ < 5771367488 + 256 * input.positions.card); omega
  have hsel : submission.layout.proof ≤ 10066334784 + off ∧
      10066334784 + off < submission.layout.proof + input.proof.length := by
    change 10066334784 ≤ _ ∧ _ < 10066334784 + input.proof.length; omega
  simp only [inputByte, Submission.inputBuffers, List.find?_cons, fixedBuffer, positionsBuffer,
    valuesBuffer, h1, h2, h3, decide_false, hsel, and_self, decide_true,
    show 10066334784 + off - submission.layout.proof = off by
      change 10066334784 + off - 10066334784 = off; omega,
    List.getElem?_eq_getElem hoff, Option.getD_some]

theorem check_initial_zero_low (input : CheckInput) (addr : Nat) (haddr : addr < 4294971392) :
    (submission.initialState .check input).getByte (BitVec.ofNat 64 addr) = 0 := by
  have hcard := positions_card_le_length input.positions
  rw [initial_input_byte submission .check input _ (by omega)]
  have h1 : ¬ (submission.layout.commitment ≤ addr ∧
      addr < submission.layout.commitment + (DIGEST_BITS + 7) / 8) := by
    change ¬ (4294971392 ≤ addr ∧ _); omega
  have h2 : ¬ (submission.layout.indices ≤ addr ∧
      addr < submission.layout.indices + 8 * (input.positions.sort (· ≤ ·)).length) := by
    change ¬ (5637149760 ≤ addr ∧ _); omega
  have h3 : ¬ (submission.layout.values ≤ addr ∧
      addr < submission.layout.values + (LEAF_SIZE / 8) * (input.positions.attach.sort (fun i j => i.val ≤ j.val)).length) := by
    change ¬ (5771367488 ≤ addr ∧ _); omega
  have h4 : ¬ (submission.layout.proof ≤ addr ∧ addr < submission.layout.proof + input.proof.length) := by
    change ¬ (10066334784 ≤ addr ∧ _); omega
  simp only [inputByte, Submission.inputBuffers, List.find?_cons, fixedBuffer, positionsBuffer,
    valuesBuffer, h1, h2, h3, h4, decide_false, List.find?_nil, check_dataBase]
  rw [if_neg (by omega)]

theorem check_initial_data_dword (input : CheckInput)
    (hvalid : input.proof.length ≤ submission.sizes.proof) (off : Nat) (hoff : off + 8 ≤ 800) :
    (submission.initialState .check input).getMem (BitVec.ofNat 64 (68719475936 + off)) =
      packedDword MoonArtifact.openingData off hoff := by
  have hcard := positions_card_le_length input.positions
  change input.proof.length ≤ 8422172696 at hvalid
  rw [initial_input_word submission .check input _ (by omega)]
  unfold packedDword
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt : j < 8 := Finset.mem_range.mp hj
  have h1 : ¬ (submission.layout.commitment ≤ 68719475936 + off + j ∧
      68719475936 + off + j < submission.layout.commitment + (DIGEST_BITS + 7) / 8) := by
    change ¬ (4294971392 ≤ _ ∧ _ < 4294971392 + 32); omega
  have h2 : ¬ (submission.layout.indices ≤ 68719475936 + off + j ∧
      68719475936 + off + j < submission.layout.indices + 8 * (input.positions.sort (· ≤ ·)).length) := by
    rw [Finset.length_sort]; change ¬ (5637149760 ≤ _ ∧ _ < 5637149760 + 8 * input.positions.card); omega
  have h3 : ¬ (submission.layout.values ≤ 68719475936 + off + j ∧
      68719475936 + off + j < submission.layout.values + (LEAF_SIZE / 8) * (input.positions.attach.sort (fun i j => i.val ≤ j.val)).length) := by
    rw [Finset.length_sort, Finset.card_attach]
    change ¬ (5771367488 ≤ _ ∧ _ < 5771367488 + 256 * input.positions.card); omega
  have h4 : ¬ (submission.layout.proof ≤ 68719475936 + off + j ∧
      68719475936 + off + j < submission.layout.proof + input.proof.length) := by
    change ¬ (10066334784 ≤ _ ∧ _ < 10066334784 + input.proof.length); omega
  simp only [inputByte, Submission.inputBuffers, List.find?_cons, fixedBuffer, positionsBuffer,
    valuesBuffer, h1, h2, h3, h4, decide_false, List.find?_nil, check_dataBase,
    show 68719475936 ≤ 68719475936 + off + j by omega, ite_true,
    show 68719475936 + off + j - 68719475936 = off + j by omega]
  rw [check_image_data, getElem?_decode 8 MoonArtifact.openingData (off + j) (by omega),
    Option.getD_some, dif_pos (by omega)]

/-! ### Layer 3 Shared Contract: Honest Committed Trapdoor Contents -/

def CommittedTrapdoor (h768 : COMPRESSION_INPUT_LENGTH = 768) (c : Compression)
    (msg : Message) (salts : Index → Salt128)
    (trapdoor : BitVec (8 * submission.sizes.trapdoor)) : Prop :=
  let c96 : Comp96 := fun x => c (x.cast h768.symm)
  (∀ l ≤ 24, ∀ idx < levelSize l,
    trapdoor.extractLsb' (8 * (levelBase l + nodeOffset l idx)) 256 =
      nodeVal c96 msg salts l idx) ∧
  (∀ l, 1 ≤ l → l < 24 → ∀ q < (levelSize l + 1) / 2,
    trapdoor.extractLsb' (8 * (levelBase l + 96 * q + 64)) 256 = 0) ∧
  (∀ i : Index,
    trapdoor.extractLsb' (8 * (saltsOff + 16 * i.val)) 128 = salts i)

end CommitGolfCandidate
