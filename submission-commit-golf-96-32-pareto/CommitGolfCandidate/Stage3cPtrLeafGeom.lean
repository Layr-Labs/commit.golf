import CommitGolfCandidate.Stage3cLeafAccount
import CommitGolfCandidate.Stage3cLeafTile
import CommitGolfCandidate.Stage3cRow

namespace CommitGolfCandidate.Chained.BinaryMachine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

set_option maxRecDepth 20000
set_option maxHeartbeats 16000000
set_option Elab.async false

/-- Message cursor at the first instruction of leaf `k`, including the 2048 bias. -/
def msgCursor (k : Nat) : Nat :=
  6144 + (k / 128) * 32768 + (k % 128) / 16 * 4096

/-- Row cursor at the first instruction of leaf `k`, including the 2048 bias. -/
def rowCursor (k : Nat) : Nat :=
  rowBase + 2048 + (k / 128) * 11776 + (k % 128) / 32 * 2944

/-- Node cursor at the first instruction of leaf `k`, including the 2048 bias. -/
def nodeCursor (k : Nat) : Nat :=
  4294975488 + 2048 + (k / 128) * 6144 + (k % 128) / 32 * 1536

/-- Remaining tile trips, held in `x20`. -/
def tileCounter (k : Nat) : Nat := 131072 - k / 128

def localIndex (j : Nat) : Nat :=
  (j / 32) * 388 + if j % 32 < 16 then 12 * (j % 32) else 193 + 12 * (j % 32 - 16)

theorem cursors_initial :
    msgCursor 0 = 6144 ∧ rowCursor 0 = 5905590272 ∧
    nodeCursor 0 = 4294977536 ∧ tileCounter 0 = 131072 := by
  decide

private theorem scale_bump (n unit : Nat) :
    (if n = 0 then 1 else 0) * unit = if n = 0 then unit else 0 := by
  by_cases h : n = 0
  · rw [ite_eq_left h, ite_eq_left h, Nat.one_mul]
  · rw [ite_eq_right h, ite_eq_right h, Nat.zero_mul]

private theorem msg_local (t : Nat) (ht : t < 127) :
    (t + 1) / 16 = t / 16 + (if (t + 1) % 16 = 0 then 1 else 0) := by
  have closed : ∀ u : Fin 127,
      (u.val + 1) / 16 = u.val / 16 + (if (u.val + 1) % 16 = 0 then 1 else 0) := by
    decide
  exact closed ⟨t, ht⟩

private theorem row_local (t : Nat) (ht : t < 127) :
    (t + 1) / 32 = t / 32 + (if (t + 1) % 32 = 0 then 1 else 0) := by
  have closed : ∀ u : Fin 127,
      (u.val + 1) / 32 = u.val / 32 + (if (u.val + 1) % 32 = 0 then 1 else 0) := by
    decide
  exact closed ⟨t, ht⟩

theorem msg_succ (k : Nat) (hk : k < LENGTH) :
    msgCursor (k + 1) = msgCursor k + if (k + 1) % 16 = 0 then 4096 else 0 := by
  have hk' : k < 16777216 := by simpa [LENGTH, LOG_LENGTH] using hk
  by_cases boundary : k % 128 = 127
  · have mod0 : (k + 1) % 128 = 0 := by omega
    have div1 : (k + 1) / 128 = k / 128 + 1 := by omega
    have mod16 : (k + 1) % 16 = 0 := by omega
    have q : (k % 128) / 16 = 7 := by rw [boundary]
    simp only [msgCursor, mod0, div1, q, if_pos mod16]
    omega
  · have lt : k % 128 < 127 := by omega
    have mod1 : (k + 1) % 128 = k % 128 + 1 := by omega
    have div0 : (k + 1) / 128 = k / 128 := by omega
    have mod16 : (k + 1) % 16 = (k % 128 + 1) % 16 := by omega
    have step := msg_local (k % 128) lt
    simp only [msgCursor, mod1, div0]
    rw [step, mod16, Nat.add_mul, ← Nat.add_assoc,
      scale_bump ((k % 128 + 1) % 16) 4096]

theorem row_succ (k : Nat) (hk : k < LENGTH) :
    rowCursor (k + 1) = rowCursor k + if (k + 1) % 32 = 0 then 2944 else 0 := by
  have hk' : k < 16777216 := by simpa [LENGTH, LOG_LENGTH] using hk
  by_cases boundary : k % 128 = 127
  · have mod0 : (k + 1) % 128 = 0 := by omega
    have div1 : (k + 1) / 128 = k / 128 + 1 := by omega
    have mod32 : (k + 1) % 32 = 0 := by omega
    have q : (k % 128) / 32 = 3 := by rw [boundary]
    simp only [rowCursor, mod0, div1, q, if_pos mod32]
    omega
  · have lt : k % 128 < 127 := by omega
    have mod1 : (k + 1) % 128 = k % 128 + 1 := by omega
    have div0 : (k + 1) / 128 = k / 128 := by omega
    have mod32 : (k + 1) % 32 = (k % 128 + 1) % 32 := by omega
    have step := row_local (k % 128) lt
    simp only [rowCursor, mod1, div0]
    rw [step, mod32, Nat.add_mul, ← Nat.add_assoc,
      scale_bump ((k % 128 + 1) % 32) 2944]

theorem node_succ (k : Nat) (hk : k < LENGTH) :
    nodeCursor (k + 1) = nodeCursor k + if (k + 1) % 32 = 0 then 1536 else 0 := by
  have hk' : k < 16777216 := by simpa [LENGTH, LOG_LENGTH] using hk
  by_cases boundary : k % 128 = 127
  · have mod0 : (k + 1) % 128 = 0 := by omega
    have div1 : (k + 1) / 128 = k / 128 + 1 := by omega
    have mod32 : (k + 1) % 32 = 0 := by omega
    have q : (k % 128) / 32 = 3 := by rw [boundary]
    simp only [nodeCursor, mod0, div1, q, if_pos mod32]
    omega
  · have lt : k % 128 < 127 := by omega
    have mod1 : (k + 1) % 128 = k % 128 + 1 := by omega
    have div0 : (k + 1) / 128 = k / 128 := by omega
    have mod32 : (k + 1) % 32 = (k % 128 + 1) % 32 := by omega
    have step := row_local (k % 128) lt
    simp only [nodeCursor, mod1, div0]
    rw [step, mod32, Nat.add_mul, ← Nat.add_assoc,
      scale_bump ((k % 128 + 1) % 32) 1536]

theorem counter_succ (k : Nat) (hk : k < LENGTH) :
    tileCounter (k + 1) = tileCounter k - if (k + 1) % 128 = 0 then 1 else 0 := by
  have hk' : k < 16777216 := by simpa [LENGTH, LOG_LENGTH] using hk
  by_cases boundary : k % 128 = 127
  · have mod0 : (k + 1) % 128 = 0 := by omega
    have div1 : (k + 1) / 128 = k / 128 + 1 := by omega
    have room : k / 128 ≤ 131071 := by omega
    simp only [tileCounter, mod0, div1, if_pos]
    omega
  · have mod1 : (k + 1) % 128 = k % 128 + 1 := by omega
    have div0 : (k + 1) / 128 = k / 128 := by omega
    have nz : (k + 1) % 128 ≠ 0 := by omega
    simp only [tileCounter, div0, if_neg nz, Nat.sub_zero]

theorem leaf_pc_local (k : Nat) : leafPC k = 4123 + localIndex (k % 128) := by
  have lt : k % 128 < 128 := Nat.mod_lt k (by decide)
  have eq := origins_agree ⟨k % 128, lt⟩
  simp only [leafPC, localIndex] at eq ⊢
  rw [← Nat.add_assoc]
  exact eq

theorem local_fits : ∀ j : Fin 128, localIndex j.val + 18 ≤ 1555 := by
  decide

theorem offset_align : ∀ j : Fin 128, ∀ c : Fin 4,
    srcOff j.val c.val % 8 = 0 ∧ srcOff j.val c.val ≤ 4000 ∧
    dstOff j.val c.val % 8 = 0 ∧ dstOff j.val c.val ≤ 4000 := by
  decide

private theorem mod8_mul (a b : Nat) (hb : b % 8 = 0) : (a * b) % 8 = 0 := by
  rw [Nat.mul_mod, hb, Nat.mul_zero, Nat.zero_mod]

private theorem mod8_add (a b : Nat) (ha : a % 8 = 0) (hb : b % 8 = 0) :
    (a + b) % 8 = 0 := by
  rw [Nat.add_mod, ha, hb, Nat.zero_add, Nat.zero_mod]

private theorem mod8_sub (a b : Nat) (ha : a % 8 = 0) (hb : b % 8 = 0) :
    (a - b) % 8 = 0 := by
  rw [← Nat.mod_add_div a 8, ← Nat.mod_add_div b 8, ha, hb, Nat.zero_add, Nat.zero_add,
    ← Nat.mul_sub_left_distrib, Nat.mul_mod_right]

private theorem msg_mod (k : Nat) : msgCursor k % 8 = 0 := by
  exact mod8_add _ _
    (mod8_add _ _ (by decide) (mod8_mul _ _ (by decide)))
    (mod8_mul _ _ (by decide))

private theorem row_mod (k : Nat) : rowCursor k % 8 = 0 := by
  have hb : rowBase % 8 = 0 := by simp only [rowBase]
  exact mod8_add _ _
    (mod8_add _ _ (mod8_add _ _ hb (by decide)) (mod8_mul _ _ (by decide)))
    (mod8_mul _ _ (by decide))

private theorem node_mod (k : Nat) : nodeCursor k % 8 = 0 := by
  exact mod8_add _ _
    (mod8_add _ _ (mod8_add _ _ (by decide) (by decide)) (mod8_mul _ _ (by decide)))
    (mod8_mul _ _ (by decide))

private def msgCap : Nat := 6144 + 131071 * 32768 + 7 * 4096
private def rowCap : Nat := rowBase + 2048 + 131071 * 11776 + 3 * 2944
private def nodeCap : Nat := 4294975488 + 2048 + 131071 * 6144 + 3 * 1536

private theorem msg_ge (k : Nat) : 2048 ≤ msgCursor k := by
  simp only [msgCursor]; omega

private theorem row_ge (k : Nat) : 2048 ≤ rowCursor k := by
  simp only [rowCursor, rowBase]; omega

private theorem node_ge (k : Nat) : 2048 ≤ nodeCursor k := by
  simp only [nodeCursor]; omega

private theorem msg_le (k : Nat) (hk : k < 16777216) : msgCursor k ≤ msgCap := by
  have t : k / 128 ≤ 131071 := by omega
  have g : (k % 128) / 16 ≤ 7 := by omega
  have := Nat.mul_le_mul_right 32768 t
  have := Nat.mul_le_mul_right 4096 g
  simp only [msgCursor, msgCap]
  omega

private theorem row_le (k : Nat) (hk : k < 16777216) : rowCursor k ≤ rowCap := by
  have t : k / 128 ≤ 131071 := by omega
  have g : (k % 128) / 32 ≤ 3 := by omega
  unfold rowCursor rowCap
  exact Nat.add_le_add
    (Nat.add_le_add_left (Nat.mul_le_mul_right 11776 t) (rowBase + 2048))
    (Nat.mul_le_mul_right 2944 g)

private theorem node_le (k : Nat) (hk : k < 16777216) : nodeCursor k ≤ nodeCap := by
  have t : k / 128 ≤ 131071 := by omega
  have g : (k % 128) / 32 ≤ 3 := by omega
  have := Nat.mul_le_mul_right 6144 t
  have := Nat.mul_le_mul_right 1536 g
  simp only [nodeCursor, nodeCap]
  omega

private theorem msg_room (extra : Nat) (he : extra ≤ 96) :
    msgCap - 2048 + 4000 + extra ≤ 2 ^ 36 := by
  have base : msgCap - 2048 + 4000 + 96 ≤ 2 ^ 36 := by simp only [msgCap]; decide
  exact Nat.le_trans (Nat.add_le_add_left he (msgCap - 2048 + 4000)) base

private theorem row_room (extra : Nat) (he : extra ≤ 96) :
    rowCap - 2048 + 4000 + extra ≤ 2 ^ 36 := by
  have id : rowCap = 7449091200 := by unfold rowCap rowBase; rfl
  rw [id]
  have base : 7449091200 - 2048 + 4000 + 96 ≤ 2 ^ 36 := by decide
  exact Nat.le_trans (Nat.add_le_add_left he (7449091200 - 2048 + 4000)) base

private theorem node_room (extra : Nat) (he : extra ≤ 96) :
    nodeCap - 2048 + 4000 + extra ≤ 2 ^ 36 := by
  have base : nodeCap - 2048 + 4000 + 96 ≤ 2 ^ 36 := by simp only [nodeCap]; decide
  exact Nat.le_trans (Nat.add_le_add_left he (nodeCap - 2048 + 4000)) base

private theorem eight : 2048 % 8 = 0 := by decide

private theorem slot (base off extra cap : Nat) (hbase : base % 8 = 0) (hoff : off % 8 = 0)
    (_hge : 2048 ≤ base) (hle : base ≤ cap) (ho : off ≤ 4000)
    (hcap : cap - 2048 + 4000 + extra ≤ 2 ^ 36) :
    (base - 2048 + off) % 8 = 0 ∧ base - 2048 + off + extra ≤ 2 ^ 36 := by
  refine ⟨mod8_add _ _ (mod8_sub base 2048 hbase eight) hoff, ?_⟩
  exact Nat.le_trans
    (Nat.add_le_add_right (Nat.add_le_add (Nat.sub_le_sub_right hle 2048) ho) extra) hcap

def absSrc (k c : Nat) : Nat :=
  (if c = 3 then rowCursor k else msgCursor k) - 2048 + srcOff (k % 128) c

def absDst (k c : Nat) : Nat :=
  (if c = 0 then msgCursor k else if c = 3 then nodeCursor k else rowCursor k) - 2048 +
    dstOff (k % 128) c

theorem leaf_range (k : Nat) (hk : k < LENGTH) (c : Fin 4) :
    absSrc k c.val % 8 = 0 ∧ absSrc k c.val + 96 ≤ 2 ^ 36 ∧
    absDst k c.val % 8 = 0 ∧ absDst k c.val + 32 ≤ 2 ^ 36 := by
  have hk' : k < 16777216 := by simpa [LENGTH, LOG_LENGTH] using hk
  have fits := offset_align ⟨k % 128, Nat.mod_lt k (by decide)⟩ c
  obtain ⟨so, soLe, doff, doLe⟩ := fits
  have mm := msg_mod k
  have rm := row_mod k
  have nm := node_mod k
  have mge := msg_ge k
  have rge := row_ge k
  have nge := node_ge k
  have mle := msg_le k hk'
  have rle := row_le k hk'
  have nle := node_le k hk'
  have small : 32 ≤ 96 := by decide
  fin_cases c
  · simp only [absSrc, absDst, show (0 = 3) = False by decide, ite_false, ite_true]
    obtain ⟨sMod, sBound⟩ := slot (msgCursor k) (srcOff (k % 128) 0) 96 msgCap mm so mge mle soLe
      (msg_room 96 (Nat.le_refl _))
    obtain ⟨dMod, dBound⟩ := slot (msgCursor k) (dstOff (k % 128) 0) 32 msgCap mm doff mge mle doLe
      (msg_room 32 small)
    exact ⟨sMod, sBound, dMod, dBound⟩
  · simp only [absSrc, absDst, show (1 = 3) = False by decide, show (1 = 0) = False by decide,
      ite_false]
    obtain ⟨sMod, sBound⟩ := slot (msgCursor k) (srcOff (k % 128) 1) 96 msgCap mm so mge mle soLe
      (msg_room 96 (Nat.le_refl _))
    obtain ⟨dMod, dBound⟩ := slot (rowCursor k) (dstOff (k % 128) 1) 32 rowCap rm doff rge rle doLe
      (row_room 32 small)
    exact ⟨sMod, sBound, dMod, dBound⟩
  · simp only [absSrc, absDst, show (2 = 3) = False by decide, show (2 = 0) = False by decide,
      ite_false]
    obtain ⟨sMod, sBound⟩ := slot (msgCursor k) (srcOff (k % 128) 2) 96 msgCap mm so mge mle soLe
      (msg_room 96 (Nat.le_refl _))
    obtain ⟨dMod, dBound⟩ := slot (rowCursor k) (dstOff (k % 128) 2) 32 rowCap rm doff rge rle doLe
      (row_room 32 small)
    exact ⟨sMod, sBound, dMod, dBound⟩
  · simp only [absSrc, absDst, show (3 = 0) = False by decide, ite_false, ite_true]
    obtain ⟨sMod, sBound⟩ := slot (rowCursor k) (srcOff (k % 128) 3) 96 rowCap rm so rge rle soLe
      (row_room 96 (Nat.le_refl _))
    obtain ⟨dMod, dBound⟩ := slot (nodeCursor k) (dstOff (k % 128) 3) 32 nodeCap nm doff nge nle doLe
      (node_room 32 small)
    exact ⟨sMod, sBound, dMod, dBound⟩

/-- Sign-extending the stored immediate recovers the logical byte offset. -/
theorem sext_offset : ∀ j : Fin 128, ∀ c : Fin 4,
    BitVec.ofNat 64 2048 + signExtend12 (BitVec.ofNat 12 (immRaw (srcOff j.val c.val))) =
      BitVec.ofNat 64 (srcOff j.val c.val) ∧
    BitVec.ofNat 64 2048 + signExtend12 (BitVec.ofNat 12 (immRaw (dstOff j.val c.val))) =
      BitVec.ofNat 64 (dstOff j.val c.val) := by
  decide +kernel

end CommitGolfCandidate.Chained.BinaryMachine
