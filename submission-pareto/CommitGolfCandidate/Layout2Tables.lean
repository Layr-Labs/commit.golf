import CommitGolfCandidate.Layout2Codec

/-! # Layout 2 V1 Tables and Opener-Facing Record Layout

Closed-form V1 bit-permutation tables (`decTables` for new → old, `encTables` for old → new),
structural proofs of `WellFormed` and `RightInverse` in both directions, and the explicit
field-by-field / phase-by-phase description of `convert encTables k` on today's proof format,
together with the 3-branch RV64 Band-B carry-register recurrence (`streamCarry`) for M3. -/

namespace CommitGolfCandidate.Layout2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

private theorem ite_pos {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by
  split
  · rfl
  · contradiction

private theorem ite_neg {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) :
    (if c then a else b) = b := by
  split
  · contradiction
  · rfl

private theorem dite_pos {α : Sort _} {c : Prop} [Decidable c] {a : c → α} {b : ¬ c → α} (h : c) :
    (if hc : c then a hc else b hc) = a h := by
  split
  · rfl
  · contradiction

private theorem dite_neg {α : Sort _} {c : Prop} [Decidable c] {a : c → α} {b : ¬ c → α} (h : ¬ c) :
    (if hc : c then a hc else b hc) = b h := by
  split
  · contradiction
  · rfl

/-! ### 1. Closed-Form V1 Tables (`decTables` and `encTables`) -/

/-- Starting byte offset of phase `p ∈ {0, 1, 2, 3}` inside a 2,136-byte superblock. -/
def phaseBase (p : Nat) : Nat :=
  if p = 0 then 0 else if p = 1 then 528 else if p = 2 then 1064 else 1600

@[simp] theorem phaseBase_0 : phaseBase 0 = 0 := rfl
@[simp] theorem phaseBase_1 : phaseBase 1 = 528 := rfl
@[simp] theorem phaseBase_2 : phaseBase 2 = 1064 := rfl
@[simp] theorem phaseBase_3 : phaseBase 3 = 1600 := rfl

/-- Number of full 64-bit Band-B tail stream dwords written at the end of phase `p`. -/
def phaseStreamCount (p : Nat) : Nat :=
  if p = 0 then 5 else 6

@[simp] theorem phaseStreamCount_0 : phaseStreamCount 0 = 5 := rfl
@[simp] theorem phaseStreamCount_1 : phaseStreamCount 1 = 6 := rfl
@[simp] theorem phaseStreamCount_2 : phaseStreamCount 2 = 6 := rfl
@[simp] theorem phaseStreamCount_3 : phaseStreamCount 3 = 6 := rfl

/-- Index of the first full 64-bit Band-B stream dword emitted in phase `p`. -/
def phaseStreamStart (p : Nat) : Nat :=
  if p = 0 then 0 else if p = 1 then 5 else if p = 2 then 11 else 17

@[simp] theorem phaseStreamStart_0 : phaseStreamStart 0 = 0 := rfl
@[simp] theorem phaseStreamStart_1 : phaseStreamStart 1 = 5 := rfl
@[simp] theorem phaseStreamStart_2 : phaseStreamStart 2 = 11 := rfl
@[simp] theorem phaseStreamStart_3 : phaseStreamStart 3 = 17 := rfl

/-- Map a Band-B tail stream bit `sbit < 368 * r` to its bit index in the new `534 * r`-byte block.
Because the partial-block carry flush (`6 / 4 / 2` bytes at `528 / 1064 / 1600`) sits immediately
after phase `r - 1`'s full stream dwords, the map consists of four contiguous linear intervals. -/
def streamBitToNewBit (r sbit : Nat) : Nat :=
  if r = 1 then 3904 + sbit
  else if sbit < 320 then 3904 + sbit
  else if r = 2 then 8128 + (sbit - 320)
  else if sbit < 704 then 8128 + (sbit - 320)
  else if r = 3 then 12416 + (sbit - 704)
  else if sbit < 1088 then 12416 + (sbit - 704)
  else 16704 + (sbit - 1088)

/-- Closed-form decoder table (`new → old`): given multiplicity `r ∈ {1..4}` and output bit `i`
in today's `534 * r`-byte record block, returns the source bit index in the new V1 block. -/
def decTables : Tables := fun r i =>
  let p := i / 4272
  let off := i % 4272
  let nb := 8 * phaseBase p
  if off < 1408 then
    nb + off
  else if off < 2368 then
    let a := (off - 1408) / 240
    let u := (off - 1408) % 240
    if u < 192 then nb + 1408 + 192 * a + u
    else nb + 2176 + 48 * a + (u - 192)
  else if off < 4048 then
    let j := (off - 2368) / 240
    let u := (off - 2368) % 240
    if u < 192 then nb + 2368 + 192 * j + u
    else if u < 238 then streamBitToNewBit r (368 * p + 46 * j + (u - 192))
    else streamBitToNewBit r (368 * p + 354 + 2 * j + (u - 238))
  else
    let u := off - 4048
    if u < 192 then nb + 3712 + u
    else streamBitToNewBit r (368 * p + 322 + (u - 192))

/-- Map a Band-B stream bit `sbit` back to its source bit index in today's `534 * r`-byte block. -/
def streamBitToOldBit (sbit : Nat) : Nat :=
  let p := sbit / 368
  let s := sbit % 368
  let ob := 4272 * p
  if s < 322 then
    let j := s / 46
    let t := s % 46
    ob + 2560 + 240 * j + t
  else if s < 354 then
    ob + 4240 + (s - 322)
  else
    let j := (s - 354) / 2
    let u := (s - 354) % 2
    ob + 2606 + 240 * j + u

/-- Map a non-stream bit `off < 3904` inside phase `p` back to its source bit index in today's block. -/
def nonStreamToOldBit (p off : Nat) : Nat :=
  let ob := 4272 * p
  if off < 1408 then ob + off
  else if off < 2176 then
    let a := (off - 1408) / 192
    let u := (off - 1408) % 192
    ob + 1408 + 240 * a + u
  else if off < 2368 then
    let a := (off - 2176) / 48
    let u := (off - 2176) % 48
    ob + 1600 + 240 * a + u
  else if off < 3712 then
    let j := (off - 2368) / 192
    let u := (off - 2368) % 192
    ob + 2368 + 240 * j + u
  else
    ob + 4048 + (off - 3712)

/-- Closed-form encoder table (`old → new`): given multiplicity `r ∈ {1..4}` and output bit `j`
in the new V1 `534 * r`-byte block, returns the source bit index in today's block. -/
def encTables : Tables := fun r j =>
  if j < 3904 then nonStreamToOldBit 0 j
  else if r = 1 then streamBitToOldBit (j - 3904)
  else if j < 4224 then streamBitToOldBit (j - 3904)
  else if j < 8128 then nonStreamToOldBit 1 (j - 4224)
  else if r = 2 then streamBitToOldBit (320 + (j - 8128))
  else if j < 8512 then streamBitToOldBit (320 + (j - 8128))
  else if j < 12416 then nonStreamToOldBit 2 (j - 8512)
  else if r = 3 then streamBitToOldBit (704 + (j - 12416))
  else if j < 12800 then streamBitToOldBit (704 + (j - 12416))
  else if j < 16704 then nonStreamToOldBit 3 (j - 12800)
  else streamBitToOldBit (1088 + (j - 16704))

/-! ### 2. Structural Well-Formedness and Two-Sided Inverse Proofs -/

private theorem streamBitToNewBit_lt (r sbit : Nat) (lo : 1 ≤ r) (hi : r ≤ 4)
    (bound : sbit < 368 * r) : streamBitToNewBit r sbit < 4272 * r := by
  unfold streamBitToNewBit
  split_ifs <;> omega

private theorem enc_on_streamBitToNewBit (r sbit : Nat) (lo : 1 ≤ r) (hi : r ≤ 4)
    (bound : sbit < 368 * r) :
    encTables r (streamBitToNewBit r sbit) = streamBitToOldBit sbit := by
  have hr : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by omega
  rcases hr with rfl | rfl | rfl | rfl
  · unfold streamBitToNewBit
    rw [ite_pos rfl]
    unfold encTables
    rw [ite_neg (by omega), ite_pos rfl]
    exact congrArg streamBitToOldBit (by omega)
  · unfold streamBitToNewBit
    simp only [show ¬ (2 = 1) by decide, ite_false, ite_true]
    by_cases h1 : sbit < 320
    · rw [ite_pos h1]; unfold encTables
      rw [ite_neg (by omega), ite_neg (by decide), ite_pos (by omega)]
      exact congrArg streamBitToOldBit (by omega)
    · rw [ite_neg h1]; unfold encTables
      rw [ite_neg (by omega), ite_neg (by decide), ite_neg (by omega), ite_neg (by omega), ite_pos rfl]
      exact congrArg streamBitToOldBit (by omega)
  · unfold streamBitToNewBit
    simp only [show ¬ (3 = 1) by decide, show ¬ (3 = 2) by decide, ite_false, ite_true]
    by_cases h1 : sbit < 320
    · rw [ite_pos h1]; unfold encTables
      rw [ite_neg (by omega), ite_neg (by decide), ite_pos (by omega)]
      exact congrArg streamBitToOldBit (by omega)
    · rw [ite_neg h1]
      by_cases h2 : sbit < 704
      · rw [ite_pos h2]; unfold encTables
        rw [ite_neg (by omega), ite_neg (by decide), ite_neg (by omega), ite_neg (by omega),
          ite_neg (by decide), ite_pos (by omega)]
        exact congrArg streamBitToOldBit (by omega)
      · rw [ite_neg h2]; unfold encTables
        rw [ite_neg (by omega), ite_neg (by decide), ite_neg (by omega), ite_neg (by omega),
          ite_neg (by decide), ite_neg (by omega), ite_neg (by omega), ite_pos rfl]
        exact congrArg streamBitToOldBit (by omega)
  · unfold streamBitToNewBit
    simp only [show ¬ (4 = 1) by decide, show ¬ (4 = 2) by decide, show ¬ (4 = 3) by decide, ite_false]
    by_cases h1 : sbit < 320
    · rw [ite_pos h1]; unfold encTables
      rw [ite_neg (by omega), ite_neg (by decide), ite_pos (by omega)]
      exact congrArg streamBitToOldBit (by omega)
    · rw [ite_neg h1]
      by_cases h2 : sbit < 704
      · rw [ite_pos h2]; unfold encTables
        rw [ite_neg (by omega), ite_neg (by decide), ite_neg (by omega), ite_neg (by omega),
          ite_neg (by decide), ite_pos (by omega)]
        exact congrArg streamBitToOldBit (by omega)
      · rw [ite_neg h2]
        by_cases h3 : sbit < 1088
        · rw [ite_pos h3]; unfold encTables
          rw [ite_neg (by omega), ite_neg (by decide), ite_neg (by omega), ite_neg (by omega),
            ite_neg (by decide), ite_neg (by omega), ite_neg (by omega), ite_neg (by decide),
            ite_pos (by omega)]
          exact congrArg streamBitToOldBit (by omega)
        · rw [ite_neg h3]; unfold encTables
          rw [ite_neg (by omega), ite_neg (by decide), ite_neg (by omega), ite_neg (by omega),
            ite_neg (by decide), ite_neg (by omega), ite_neg (by omega), ite_neg (by decide),
            ite_neg (by omega), ite_neg (by omega)]
          exact congrArg streamBitToOldBit (by omega)

private theorem enc_on_nonStream (r p off : Nat) (lo : 1 ≤ r) (hi : r ≤ 4)
    (hp : p < r) (hoff : off < 3904) :
    encTables r (8 * phaseBase p + off) = nonStreamToOldBit p off := by
  have hp4 : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 := by omega
  rcases hp4 with rfl | rfl | rfl | rfl
  · rw [phaseBase_0]; unfold encTables; rw [ite_pos (by omega)]
    exact congrArg (nonStreamToOldBit 0) (by omega)
  · rw [phaseBase_1]; unfold encTables
    rw [ite_neg (by omega), ite_neg (by omega), ite_neg (by omega), ite_pos (by omega)]
    exact congrArg (nonStreamToOldBit 1) (by omega)
  · rw [phaseBase_2]; unfold encTables
    rw [ite_neg (by omega), ite_neg (by omega), ite_neg (by omega), ite_neg (by omega),
      ite_neg (by omega), ite_neg (by omega), ite_pos (by omega)]
    exact congrArg (nonStreamToOldBit 2) (by omega)
  · rw [phaseBase_3]; unfold encTables
    rw [ite_neg (by omega), ite_neg (by omega), ite_neg (by omega), ite_neg (by omega),
      ite_neg (by omega), ite_neg (by omega), ite_neg (by omega), ite_neg (by omega),
      ite_neg (by omega), ite_pos (by omega)]
    exact congrArg (nonStreamToOldBit 3) (by omega)

private theorem streamBitToOldBit_lt (r sbit : Nat) (bound : sbit < 368 * r) :
    streamBitToOldBit sbit < 4272 * r := by
  unfold streamBitToOldBit
  dsimp only
  split_ifs <;> omega

private theorem nonStreamToOldBit_lt (r p off : Nat) (hp : p < r) (hoff : off < 3904) :
    nonStreamToOldBit p off < 4272 * r := by
  unfold nonStreamToOldBit
  dsimp only
  split_ifs <;> omega

private theorem dec_on_streamBitToOldBit (r sbit : Nat) (lo : 1 ≤ r) (hi : r ≤ 4)
    (bound : sbit < 368 * r) :
    decTables r (streamBitToOldBit sbit) = streamBitToNewBit r sbit := by
  unfold streamBitToOldBit
  dsimp only
  set p := sbit / 368
  set s := sbit % 368
  have hps : 368 * p + s = sbit := by dsimp [p, s]; omega
  have hs : s < 368 := Nat.mod_lt _ (by decide)
  by_cases h1 : s < 322
  · rw [ite_pos h1]
    set j := s / 46
    set t := s % 46
    have hj : j < 7 := by dsimp [j]; omega
    have ht : t < 46 := Nat.mod_lt _ (by decide)
    have hjt : 46 * j + t = s := by dsimp [j, t]; omega
    unfold decTables
    have hdiv : (4272 * p + 2560 + 240 * j + t) / 4272 = p := by omega
    have hmod : (4272 * p + 2560 + 240 * j + t) % 4272 = 2560 + 240 * j + t := by omega
    have hd240 : (2560 + 240 * j + t - 2368) / 240 = j := by omega
    have hm240 : (2560 + 240 * j + t - 2368) % 240 = 192 + t := by omega
    simp only [hdiv, hmod, show ¬ (2560 + 240 * j + t < 1408) by omega,
      show ¬ (2560 + 240 * j + t < 2368) by omega, show 2560 + 240 * j + t < 4048 by omega,
      ite_false, ite_true, hd240, hm240, show ¬ (192 + t < 192) by omega, show 192 + t < 238 by omega]
    exact congrArg (streamBitToNewBit r) (by omega)
  · rw [ite_neg h1]
    by_cases h2 : s < 354
    · rw [ite_pos h2]
      unfold decTables
      have hdiv : (4272 * p + 4240 + (s - 322)) / 4272 = p := by omega
      have hmod : (4272 * p + 4240 + (s - 322)) % 4272 = 4240 + (s - 322) := by omega
      simp only [hdiv, hmod, show ¬ (4240 + (s - 322) < 1408) by omega,
        show ¬ (4240 + (s - 322) < 2368) by omega, show ¬ (4240 + (s - 322) < 4048) by omega,
        show ¬ (4240 + (s - 322) - 4048 < 192) by omega, ite_false]
      exact congrArg (streamBitToNewBit r) (by omega)
    · rw [ite_neg h2]
      set j := (s - 354) / 2
      set u := (s - 354) % 2
      have hj : j < 7 := by dsimp [j]; omega
      have hu : u < 2 := Nat.mod_lt _ (by decide)
      have hju : 2 * j + u = s - 354 := by dsimp [j, u]; omega
      unfold decTables
      have hdiv : (4272 * p + 2606 + 240 * j + u) / 4272 = p := by omega
      have hmod : (4272 * p + 2606 + 240 * j + u) % 4272 = 2606 + 240 * j + u := by omega
      have hd240 : (2606 + 240 * j + u - 2368) / 240 = j := by omega
      have hm240 : (2606 + 240 * j + u - 2368) % 240 = 238 + u := by omega
      simp only [hdiv, hmod, show ¬ (2606 + 240 * j + u < 1408) by omega,
        show ¬ (2606 + 240 * j + u < 2368) by omega, show 2606 + 240 * j + u < 4048 by omega,
        ite_false, ite_true, hd240, hm240, show ¬ (238 + u < 192) by omega, show ¬ (238 + u < 238) by omega]
      exact congrArg (streamBitToNewBit r) (by omega)

private theorem dec_on_nonStreamToOldBit (r p off : Nat) (hoff : off < 3904) :
    decTables r (nonStreamToOldBit p off) = 8 * phaseBase p + off := by
  unfold nonStreamToOldBit
  dsimp only
  by_cases h1 : off < 1408
  · rw [ite_pos h1]
    unfold decTables
    have hdiv : (4272 * p + off) / 4272 = p := by omega
    have hmod : (4272 * p + off) % 4272 = off := by omega
    simp only [hdiv, hmod, h1, ite_true]
  · rw [ite_neg h1]
    by_cases h2 : off < 2176
    · rw [ite_pos h2]
      set a := (off - 1408) / 192
      set u := (off - 1408) % 192
      have ha : a < 4 := by dsimp [a]; omega
      have hu : u < 192 := Nat.mod_lt _ (by decide)
      have hau : 192 * a + u = off - 1408 := by dsimp [a, u]; omega
      unfold decTables
      have hdiv : (4272 * p + 1408 + 240 * a + u) / 4272 = p := by omega
      have hmod : (4272 * p + 1408 + 240 * a + u) % 4272 = 1408 + 240 * a + u := by omega
      simp only [hdiv, hmod]
      split_ifs <;> omega
    · rw [ite_neg h2]
      by_cases h3 : off < 2368
      · rw [ite_pos h3]
        set a := (off - 2176) / 48
        set u := (off - 2176) % 48
        have ha : a < 4 := by dsimp [a]; omega
        have hu : u < 48 := Nat.mod_lt _ (by decide)
        have hau : 48 * a + u = off - 2176 := by dsimp [a, u]; omega
        unfold decTables
        have hdiv : (4272 * p + 1600 + 240 * a + u) / 4272 = p := by omega
        have hmod : (4272 * p + 1600 + 240 * a + u) % 4272 = 1600 + 240 * a + u := by omega
        simp only [hdiv, hmod]
        split_ifs <;> omega
      · rw [ite_neg h3]
        by_cases h4 : off < 3712
        · rw [ite_pos h4]
          set j := (off - 2368) / 192
          set u := (off - 2368) % 192
          have hj : j < 7 := by dsimp [j]; omega
          have hu : u < 192 := Nat.mod_lt _ (by decide)
          have hju : 192 * j + u = off - 2368 := by dsimp [j, u]; omega
          unfold decTables
          have hdiv : (4272 * p + 2368 + 240 * j + u) / 4272 = p := by omega
          have hmod : (4272 * p + 2368 + 240 * j + u) % 4272 = 2368 + 240 * j + u := by omega
          simp only [hdiv, hmod]
          split_ifs <;> omega
        · rw [ite_neg h4]
          unfold decTables
          have hdiv : (4272 * p + 4048 + (off - 3712)) / 4272 = p := by omega
          have hmod : (4272 * p + 4048 + (off - 3712)) % 4272 = 4048 + (off - 3712) := by omega
          simp only [hdiv, hmod]
          split_ifs <;> omega

theorem dec_wellFormed : WellFormed decTables := by
  intro r lo hi i bound
  unfold decTables
  set p := i / 4272
  set off := i % 4272
  have hp : p < r := by dsimp [p]; omega
  have hoff : off < 4272 := Nat.mod_lt _ (by decide)
  dsimp only
  split_ifs
  · unfold phaseBase; split_ifs <;> omega
  · unfold phaseBase; split_ifs <;> omega
  · unfold phaseBase; split_ifs <;> omega
  · unfold phaseBase; split_ifs <;> omega
  · exact streamBitToNewBit_lt r _ lo hi (by omega)
  · exact streamBitToNewBit_lt r _ lo hi (by omega)
  · unfold phaseBase; split_ifs <;> omega
  · exact streamBitToNewBit_lt r _ lo hi (by omega)

theorem enc_wellFormed : WellFormed encTables := by
  intro r lo hi j bound
  unfold encTables
  split_ifs
  · exact nonStreamToOldBit_lt r 0 j (by omega) (by omega)
  · exact streamBitToOldBit_lt r (j - 3904) (by omega)
  · exact streamBitToOldBit_lt r (j - 3904) (by omega)
  · exact nonStreamToOldBit_lt r 1 (j - 4224) (by omega) (by omega)
  · exact streamBitToOldBit_lt r (320 + (j - 8128)) (by omega)
  · exact streamBitToOldBit_lt r (320 + (j - 8128)) (by omega)
  · exact nonStreamToOldBit_lt r 2 (j - 8512) (by omega) (by omega)
  · exact streamBitToOldBit_lt r (704 + (j - 12416)) (by omega)
  · exact streamBitToOldBit_lt r (704 + (j - 12416)) (by omega)
  · exact nonStreamToOldBit_lt r 3 (j - 12800) (by omega) (by omega)
  · exact streamBitToOldBit_lt r (1088 + (j - 16704)) (by omega)

theorem dec_enc_rightInverse : RightInverse decTables encTables := by
  intro r lo hi i bound
  set p := i / 4272
  set off := i % 4272
  have hp : p < r := by dsimp [p]; omega
  have hoff : off < 4272 := Nat.mod_lt _ (by decide)
  have hip : 4272 * p + off = i := by dsimp [p, off]; omega
  unfold decTables
  simp only [show i / 4272 = p from rfl, show i % 4272 = off from rfl]
  by_cases h1 : off < 1408
  · rw [ite_pos h1, enc_on_nonStream r p off lo hi hp (by omega)]
    unfold nonStreamToOldBit; rw [ite_pos h1]; omega
  · rw [ite_neg h1]
    by_cases h2 : off < 2368
    · rw [ite_pos h2]
      set a := (off - 1408) / 240
      set u := (off - 1408) % 240
      have ha : a < 4 := by dsimp [a]; omega
      have hu : u < 240 := Nat.mod_lt _ (by decide)
      have hau : 240 * a + u = off - 1408 := by dsimp [a, u]; omega
      by_cases hu192 : u < 192
      · rw [ite_pos hu192]
        have hrew : 8 * phaseBase p + 1408 + 192 * a + u = 8 * phaseBase p + (1408 + 192 * a + u) := by omega
        rw [hrew, enc_on_nonStream r p _ lo hi hp (by omega)]
        unfold nonStreamToOldBit
        rw [ite_neg (by omega), ite_pos (by omega)]
        have hd : (1408 + 192 * a + u - 1408) / 192 = a := by omega
        have hm : (1408 + 192 * a + u - 1408) % 192 = u := by omega
        simp only [hd, hm]; omega
      · rw [ite_neg hu192]
        have hrew : 8 * phaseBase p + 2176 + 48 * a + (u - 192) = 8 * phaseBase p + (2176 + 48 * a + (u - 192)) := by omega
        rw [hrew, enc_on_nonStream r p _ lo hi hp (by omega)]
        unfold nonStreamToOldBit
        rw [ite_neg (by omega), ite_neg (by omega), ite_pos (by omega)]
        have hd : (2176 + 48 * a + (u - 192) - 2176) / 48 = a := by omega
        have hm : (2176 + 48 * a + (u - 192) - 2176) % 48 = u - 192 := by omega
        simp only [hd, hm]; omega
    · rw [ite_neg h2]
      by_cases h3 : off < 4048
      · rw [ite_pos h3]
        set j := (off - 2368) / 240
        set u := (off - 2368) % 240
        have hj : j < 7 := by dsimp [j]; omega
        have hu : u < 240 := Nat.mod_lt _ (by decide)
        have hju : 240 * j + u = off - 2368 := by dsimp [j, u]; omega
        by_cases hu1 : u < 192
        · rw [ite_pos hu1]
          have hrew : 8 * phaseBase p + 2368 + 192 * j + u = 8 * phaseBase p + (2368 + 192 * j + u) := by omega
          rw [hrew, enc_on_nonStream r p _ lo hi hp (by omega)]
          unfold nonStreamToOldBit
          rw [ite_neg (by omega), ite_neg (by omega), ite_neg (by omega), ite_pos (by omega)]
          have hd : (2368 + 192 * j + u - 2368) / 192 = j := by omega
          have hm : (2368 + 192 * j + u - 2368) % 192 = u := by omega
          simp only [hd, hm]; omega
        · rw [ite_neg hu1]
          by_cases hu2 : u < 238
          · rw [ite_pos hu2, enc_on_streamBitToNewBit r _ lo hi (by omega)]
            unfold streamBitToOldBit
            have hdiv : (368 * p + 46 * j + (u - 192)) / 368 = p := by omega
            have hmod : (368 * p + 46 * j + (u - 192)) % 368 = 46 * j + (u - 192) := by omega
            have hd46 : (46 * j + (u - 192)) / 46 = j := by omega
            have hm46 : (46 * j + (u - 192)) % 46 = u - 192 := by omega
            simp only [hdiv, hmod, show 46 * j + (u - 192) < 322 by omega, ite_true, hd46, hm46]
            omega
          · rw [ite_neg hu2, enc_on_streamBitToNewBit r _ lo hi (by omega)]
            unfold streamBitToOldBit
            have hdiv : (368 * p + 354 + 2 * j + (u - 238)) / 368 = p := by omega
            have hmod : (368 * p + 354 + 2 * j + (u - 238)) % 368 = 354 + 2 * j + (u - 238) := by omega
            have hd2 : (354 + 2 * j + (u - 238) - 354) / 2 = j := by omega
            have hm2 : (354 + 2 * j + (u - 238) - 354) % 2 = u - 238 := by omega
            simp only [hdiv, hmod, show ¬ (354 + 2 * j + (u - 238) < 322) by omega,
              show ¬ (354 + 2 * j + (u - 238) < 354) by omega, ite_false, hd2, hm2]
            omega
      · rw [ite_neg h3]
        set u := off - 4048
        have hu_lt : u < 224 := by dsimp [u]; omega
        by_cases hu : u < 192
        · rw [ite_pos hu]
          have hrew : 8 * phaseBase p + 3712 + u = 8 * phaseBase p + (3712 + u) := by omega
          rw [hrew, enc_on_nonStream r p _ lo hi hp (by omega)]
          unfold nonStreamToOldBit
          rw [ite_neg (by omega), ite_neg (by omega), ite_neg (by omega), ite_neg (by omega)]
          omega
        · rw [ite_neg hu, enc_on_streamBitToNewBit r _ lo hi (by omega)]
          unfold streamBitToOldBit
          have hdiv : (368 * p + 322 + (u - 192)) / 368 = p := by omega
          have hmod : (368 * p + 322 + (u - 192)) % 368 = 322 + (u - 192) := by omega
          simp only [hdiv, hmod, show ¬ (322 + (u - 192) < 322) by omega,
            show 322 + (u - 192) < 354 by omega, ite_false, ite_true]
          omega

theorem enc_dec_rightInverse : RightInverse encTables decTables := by
  intro r lo hi j bound
  unfold encTables
  split_ifs
  · rw [dec_on_nonStreamToOldBit r 0 j (by omega), phaseBase_0]; omega
  · rw [dec_on_streamBitToOldBit r (j - 3904) lo hi (by omega)]; unfold streamBitToNewBit; rw [ite_pos (by omega)]; omega
  · rw [dec_on_streamBitToOldBit r (j - 3904) lo hi (by omega)]; unfold streamBitToNewBit; split_ifs <;> omega
  · rw [dec_on_nonStreamToOldBit r 1 (j - 4224) (by omega), phaseBase_1]; omega
  · rw [dec_on_streamBitToOldBit r (320 + (j - 8128)) lo hi (by omega)]; unfold streamBitToNewBit; split_ifs <;> omega
  · rw [dec_on_streamBitToOldBit r (320 + (j - 8128)) lo hi (by omega)]; unfold streamBitToNewBit; split_ifs <;> omega
  · rw [dec_on_nonStreamToOldBit r 2 (j - 8512) (by omega), phaseBase_2]; omega
  · rw [dec_on_streamBitToOldBit r (704 + (j - 12416)) lo hi (by omega)]; unfold streamBitToNewBit; split_ifs <;> omega
  · rw [dec_on_streamBitToOldBit r (704 + (j - 12416)) lo hi (by omega)]; unfold streamBitToNewBit; split_ifs <;> omega
  · rw [dec_on_nonStreamToOldBit r 3 (j - 12800) (by omega), phaseBase_3]; omega
  · rw [dec_on_streamBitToOldBit r (1088 + (j - 16704)) lo hi (by omega)]; unfold streamBitToNewBit; split_ifs <;> omega

/-- Checker round-trip: `convert decTables k (convert encTables k p) = p` for every complete proof. -/
theorem convert_dec_enc (k : Nat) (p : Proof) (complete : 534 * k ≤ p.length) :
    convert decTables k (convert encTables k p) = p :=
  convert_roundtrip dec_wellFormed dec_enc_rightInverse k p complete

/-- Reverse round-trip: `convert encTables k (convert decTables k p) = p` for every complete proof. -/
theorem convert_enc_dec (k : Nat) (p : Proof) (complete : 534 * k ≤ p.length) :
    convert encTables k (convert decTables k p) = p :=
  convert_roundtrip enc_wellFormed enc_dec_rightInverse k p complete

/-! ### 3. Opener-Facing Layout Description (Field by Field, Phase by Phase) -/

/-- Logical fields of one opening record, matching `GroupedOpening.physicalRecord`. -/
structure RecordFields where
  salt  : BitVec 128
  mate  : Fin 3 → BitVec 256
  sib0  : BitVec 256          -- level 0 (L22 sibling, full 32B)
  sib1  : BitVec 256          -- level 1 (L21 sibling, full 32B)
  bandA : Fin 4 → BitVec 256  -- levels 2..5 (240-bit: 24B body + 48b tail)
  bandB : Fin 8 → BitVec 256  -- levels 6..13 (238-bit: 24B body + 46b tail)

/-- Bits `238..255` of `bandB 0..6` are zero (holds for every honest heap node of depth `0..16`,
see `GroupedOpening.upper_heap_high`). -/
def BandBClean (f : RecordFields) : Prop :=
  ∀ j : Fin 7, (f.bandB ⟨j.val, by omega⟩).extractLsb' 238 18 = 0

/-- Little-endian byte serialization of a `8 * n`-bit vector. -/
def leBytes {n : Nat} (v : BitVec (8 * n)) : Proof :=
  List.ofFn fun i : Fin n => v.extractLsb' (8 * i.val) 8

@[simp] theorem leBytes_length {n : Nat} (v : BitVec (8 * n)) : (leBytes v).length = n := by
  simp [leBytes]

/-- Little-endian 8-byte serialization of a 64-bit word. -/
def wordBytes (w : Word) : Proof := leBytes (n := 8) w

@[simp] theorem wordBytes_length (w : Word) : (wordBytes w).length = 8 :=
  leBytes_length (n := 8) w

/-- Construct a 64-bit word from a bit predicate `f : Nat → Bool` (bits `0..63`). -/
private def bitsToNat (f : Nat → Bool) (off : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (if f off then 1 else 0) + 2 * bitsToNat f (off + 1) n

private theorem bitsToNat_testBit (f : Nat → Bool) :
    ∀ n off i, (bitsToNat f off n).testBit i = (decide (i < n) && f (off + i))
  | 0, _, _ => by simp [bitsToNat]
  | n + 1, off, 0 => by
    simp only [bitsToNat, Nat.testBit_zero, Nat.add_zero, Nat.zero_lt_succ, decide_true, Bool.true_and]
    cases f off <;> simp
  | n + 1, off, i + 1 => by
    rw [bitsToNat, Nat.testBit_succ]
    have hdiv : ((if f off then 1 else 0) + 2 * bitsToNat f (off + 1) n) / 2 = bitsToNat f (off + 1) n := by
      cases f off <;> simp only [Bool.false_eq_true, ite_true, ite_false, reduceIte] <;> omega
    rw [hdiv, bitsToNat_testBit f n (off + 1) i]
    simp only [Nat.add_lt_add_iff_right, show off + 1 + i = off + (i + 1) by omega]

def wordOfBits (f : Nat → Bool) : Word :=
  BitVec.ofNat 64 (bitsToNat f 0 64)

theorem wordOfBits_getLsbD (f : Nat → Bool) (i : Nat) (hi : i < 64) :
    (wordOfBits f).getLsbD i = f i := by
  rw [wordOfBits, BitVec.getLsbD_ofNat, bitsToNat_testBit]
  simp [hi]

/-- Halfword 14 of Band-B slot `k < 7` in today's layout (exact match to `GroupedOpening.foldHalf`). -/
def v1FoldHalf (s top : BitVec 256) (k : Nat) : BitVec 16 :=
  s.extractLsb' 224 16 ||| ((top.extractLsb' 224 16 >>> (2 * k)) <<< 14)

/-- Byte `b < 534` of today's 534-byte record layout for `f`. -/
def oldRecordByte (f : RecordFields) (b : Nat) : Byte :=
  if b < 16 then f.salt.extractLsb' (8 * b) 8
  else if b < 48 then (f.mate 0).extractLsb' (8 * (b - 16)) 8
  else if b < 80 then (f.mate 1).extractLsb' (8 * (b - 48)) 8
  else if b < 112 then (f.mate 2).extractLsb' (8 * (b - 80)) 8
  else if b < 144 then f.sib0.extractLsb' (8 * (b - 112)) 8
  else if b < 176 then f.sib1.extractLsb' (8 * (b - 144)) 8
  else if hA : b < 296 then
    let a := (b - 176) / 30
    let u := (b - 176) % 30
    (f.bandA ⟨a, by omega⟩).extractLsb' (8 * u) 8
  else if hB : b < 506 then
    let j := (b - 296) / 30
    let u := (b - 296) % 30
    let sj := f.bandB ⟨j, by omega⟩
    if u < 28 then sj.extractLsb' (8 * u) 8
    else (v1FoldHalf sj (f.bandB 7) j).extractLsb' (8 * (u - 28)) 8
  else
    (f.bandB 7).extractLsb' (8 * (b - 506)) 8

/-- Today's 534-byte record for `f`. -/
def oldRecordBytes (f : RecordFields) : Proof :=
  List.ofFn fun b : Fin 534 => oldRecordByte f b.val

@[simp] theorem oldRecordBytes_length (f : RecordFields) : (oldRecordBytes f).length = 534 := by
  rw [oldRecordBytes, List.length_ofFn]

/-- Today's `534 * r`-byte block for `r` consecutive records `block 0 .. block (r - 1)`. -/
def oldBlockBytes (r : Nat) (block : Nat → RecordFields) : Proof :=
  (List.range r).flatMap fun p => oldRecordBytes (block p)

@[simp] theorem oldBlockBytes_length (r : Nat) (block : Nat → RecordFields) :
    (oldBlockBytes r block).length = 534 * r := by
  unfold oldBlockBytes
  rw [List.length_flatMap, List.map_congr_left (fun p _ => oldRecordBytes_length (block p))]
  simp [Nat.mul_comm]

/-- Today's full proof bytes for `k` records `recs 0 .. recs (k - 1)` followed by `cap`. -/
def oldProofBytes (k : Nat) (recs : Nat → RecordFields) (cap : Proof) : Proof :=
  oldBlockBytes k recs ++ cap

@[simp] theorem oldProofBytes_length (k : Nat) (recs : Nat → RecordFields) (cap : Proof) :
    (oldProofBytes k recs cap).length = 534 * k + cap.length := by
  simp [oldProofBytes]

/-- The three aligned 64-bit Band-A tail words written at offsets `272`, `280`, `288` of each phase.
Matches the V1 opener's `slli`/`or`/`srli`/`sd` instructions verbatim. -/
def bandATailWord (f : RecordFields) (w : Fin 3) : Word :=
  let t0 := ((f.bandA 0).extractLsb' 192 48).zeroExtend 64
  let t1 := ((f.bandA 1).extractLsb' 192 48).zeroExtend 64
  let t2 := ((f.bandA 2).extractLsb' 192 48).zeroExtend 64
  let t3 := ((f.bandA 3).extractLsb' 192 48).zeroExtend 64
  match w with
  | ⟨0, _⟩ => t0 ||| (t1 <<< 48)
  | ⟨1, _⟩ => (t1 >>> 16) ||| (t2 <<< 32)
  | ⟨2, _⟩ => (t2 >>> 32) ||| (t3 <<< 16)

/-- Bit `sbit` of the logical Band-B 46-bit tail stream across a superblock's records (`368` bits
per record: `8` siblings × `46` tail bits `192..237`). -/
def bandBStreamBit (block : Nat → RecordFields) (sbit : Nat) : Bool :=
  let p := sbit / 368
  let s := sbit % 368
  let j := s / 46
  let t := s % 46
  if hj : j < 8 then (block p).bandB ⟨j, hj⟩ |>.getLsbD (192 + t) else false

/-- 64-bit stream dword `dw` of the Band-B 46-bit tail stream (`dw ∈ 0..22` for full 4-record block). -/
def bandBStreamDword (block : Nat → RecordFields) (dw : Nat) : Word :=
  wordOfBits fun b => bandBStreamBit block (64 * dw + b)

theorem bandBStreamDword_getLsbD (block : Nat → RecordFields) (dw b : Nat) (hb : b < 64) :
    (bandBStreamDword block dw).getLsbD b = bandBStreamBit block (64 * dw + b) :=
  wordOfBits_getLsbD _ b hb

/-- Fixed 488-byte prefix of phase `p` for record `f`:
- `[0..15]`:    salt (16B)
- `[16..47]`:   mate 0 (32B)
- `[48..79]`:   mate 1 (32B)
- `[80..111]`:  mate 2 (32B)
- `[112..143]`: sib0 / L22 (32B)
- `[144..175]`: sib1 / L21 (32B)
- `[176..271]`: Band-A bodies `0..3` (4 × 24B at `176, 200, 224, 248`)
- `[272..295]`: Band-A packed tails `bandATailWord 0..2` (3 × 8B at `272, 280, 288`)
- `[296..487]`: Band-B bodies `0..7` (8 × 24B at `296, 320, 344, 368, 392, 416, 440, 464`) -/
def newPhaseFixedBytes (f : RecordFields) : Proof :=
  leBytes (n := 16) f.salt ++
  leBytes (n := 32) (f.mate 0) ++
  leBytes (n := 32) (f.mate 1) ++
  leBytes (n := 32) (f.mate 2) ++
  leBytes (n := 32) f.sib0 ++
  leBytes (n := 32) f.sib1 ++
  leBytes (n := 24) ((f.bandA 0).extractLsb' 0 192) ++
  leBytes (n := 24) ((f.bandA 1).extractLsb' 0 192) ++
  leBytes (n := 24) ((f.bandA 2).extractLsb' 0 192) ++
  leBytes (n := 24) ((f.bandA 3).extractLsb' 0 192) ++
  wordBytes (bandATailWord f 0) ++
  wordBytes (bandATailWord f 1) ++
  wordBytes (bandATailWord f 2) ++
  leBytes (n := 24) ((f.bandB 0).extractLsb' 0 192) ++
  leBytes (n := 24) ((f.bandB 1).extractLsb' 0 192) ++
  leBytes (n := 24) ((f.bandB 2).extractLsb' 0 192) ++
  leBytes (n := 24) ((f.bandB 3).extractLsb' 0 192) ++
  leBytes (n := 24) ((f.bandB 4).extractLsb' 0 192) ++
  leBytes (n := 24) ((f.bandB 5).extractLsb' 0 192) ++
  leBytes (n := 24) ((f.bandB 6).extractLsb' 0 192) ++
  leBytes (n := 24) ((f.bandB 7).extractLsb' 0 192)

@[simp] theorem newPhaseFixedBytes_length (f : RecordFields) :
    (newPhaseFixedBytes f).length = 488 := by
  simp [newPhaseFixedBytes]

/-- Full bytes emitted by phase `p ∈ {0, 1, 2, 3}`: `488B` fixed fields plus `5` (for `p = 0`)
or `6` (for `p = 1, 2, 3`) aligned 64-bit Band-B stream dwords (`528B` or `536B`). -/
def newPhaseBytes (p : Nat) (block : Nat → RecordFields) : Proof :=
  newPhaseFixedBytes (block p) ++
    (List.range (phaseStreamCount p)).flatMap fun d =>
      wordBytes (bandBStreamDword block (phaseStreamStart p + d))

@[simp] theorem newPhaseBytes_length (p : Nat) (block : Nat → RecordFields) :
    (newPhaseBytes p block).length = if p = 0 then 528 else 536 := by
  unfold newPhaseBytes phaseStreamCount
  rw [List.length_append, newPhaseFixedBytes_length, List.length_flatMap,
    List.map_congr_left (fun _ _ => wordBytes_length _)]
  split_ifs <;> simp

/-- Trailing Band-B carry flush written at `phaseBase r` for a partial block of `r ∈ {1, 2, 3}`
records (`6 / 4 / 2` bytes at `528 / 1064 / 1600`; empty for `r = 0` or `r = 4`). -/
def newPartialFlush (r : Nat) (block : Nat → RecordFields) : Proof :=
  if r = 1 then (wordBytes (bandBStreamDword block 5)).take 6
  else if r = 2 then (wordBytes (bandBStreamDword block 11)).take 4
  else if r = 3 then (wordBytes (bandBStreamDword block 17)).take 2
  else []

@[simp] theorem newPartialFlush_length (r : Nat) (block : Nat → RecordFields) :
    (newPartialFlush r block).length =
      if r = 1 then 6 else if r = 2 then 4 else if r = 3 then 2 else 0 := by
  unfold newPartialFlush
  split_ifs <;> simp

/-- Complete Layout 2 V1 bytes for an `r`-record block (`r ∈ {1, 2, 3, 4}`, `534 * r` bytes). -/
def newBlockBytes (r : Nat) (block : Nat → RecordFields) : Proof :=
  (List.range r).flatMap (fun p => newPhaseBytes p block) ++ newPartialFlush r block

theorem newBlockBytes_length (r : Nat) (lo : 1 ≤ r) (hi : r ≤ 4) (block : Nat → RecordFields) :
    (newBlockBytes r block).length = 534 * r := by
  have hr : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by omega
  rcases hr with rfl | rfl | rfl | rfl <;>
    simp [newBlockBytes, List.range_succ, List.flatMap_append]

/-- Complete Layout 2 V1 proof bytes for `k` records followed by unchanged `cap`. -/
def newProofBytes (k : Nat) (recs : Nat → RecordFields) (cap : Proof) : Proof :=
  (List.range (k / 4)).flatMap (fun g => newBlockBytes 4 (fun p => recs (4 * g + p))) ++
  (if k % 4 = 0 then [] else newBlockBytes (k % 4) (fun p => recs (4 * (k / 4) + p))) ++
  cap

theorem newProofBytes_length (k : Nat) (recs : Nat → RecordFields) (cap : Proof) :
    (newProofBytes k recs cap).length = (oldProofBytes k recs cap).length := by
  unfold newProofBytes
  rw [List.length_append, List.length_append, oldProofBytes_length, List.length_flatMap,
    List.map_congr_left (fun g _ => newBlockBytes_length 4 (by decide) (by decide) _)]
  simp only [List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
  split_ifs with h
  · simp; omega
  · rw [newBlockBytes_length (k % 4) (by omega) (by omega)]; omega

/-! ### 4. Bit-Level Proof that `convert encTables k (oldProofBytes k recs cap) = newProofBytes k recs cap` -/

private theorem getElem_append_nat {α : Type} (xs ys : List α) (i : Nat) (d : α) :
    (xs ++ ys)[i]?.getD d = if i < xs.length then xs[i]?.getD d else ys[i - xs.length]?.getD d := by
  by_cases h : i < xs.length
  · rw [ite_pos h, List.getElem?_append_left h]
  · rw [ite_neg h, List.getElem?_append_right (by omega)]

private theorem leBytes_getD {n : Nat} (v : BitVec (8 * n)) (i : Nat) (hi : i < n) :
    (leBytes v)[i]?.getD 0 = v.extractLsb' (8 * i) 8 := by
  simp [leBytes, hi]

private theorem wordBytes_getD (w : Word) (i : Nat) (hi : i < 8) :
    (wordBytes w)[i]?.getD 0 = w.extractLsb' (8 * i) 8 :=
  leBytes_getD (n := 8) w i hi

private theorem oldBlockBytes_getD (r : Nat) (block : Nat → RecordFields) (j : Nat)
    (hj : j < 534 * r) :
    (oldBlockBytes r block)[j]?.getD 0 = oldRecordByte (block (j / 534)) (j % 534) := by
  induction r generalizing j with
  | zero => omega
  | succ m ih =>
    unfold oldBlockBytes
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, getElem_append_nat]
    change (if j < (oldBlockBytes m block).length then _ else _) = _
    rw [oldBlockBytes_length]
    by_cases h : j < 534 * m
    · rw [ite_pos h]; exact ih j h
    · rw [ite_neg h, show (List.flatMap (fun p => oldRecordBytes (block p)) (List.range m)).length = 534 * m from
        oldBlockBytes_length m block]
      have hdiv : j / 534 = m := by omega
      have hmod : j % 534 = j - 534 * m := by omega
      have hlt : j - 534 * m < 534 := by omega
      rw [hdiv, hmod]
      simp only [oldRecordBytes, List.getElem?_ofFn, hlt, dite_true, Option.getD_some]

private theorem oldRecordByte_getLsbD_bandB_clean (f : RecordFields) (clean : BandBClean f)
    (j : Nat) (hj : j < 7) (u : Nat) (hu : u < 240) :
    let b := 296 + 30 * j + u / 8
    (oldRecordByte f b).getLsbD (u % 8) =
      if u < 238 then (f.bandB ⟨j, by omega⟩).getLsbD u
      else (f.bandB 7).getLsbD (224 + 2 * j + (u - 238)) := by
  dsimp only
  have h1 : ¬ (296 + 30 * j + u / 8 < 16) := by omega
  have h2 : ¬ (296 + 30 * j + u / 8 < 48) := by omega
  have h3 : ¬ (296 + 30 * j + u / 8 < 80) := by omega
  have h4 : ¬ (296 + 30 * j + u / 8 < 112) := by omega
  have h5 : ¬ (296 + 30 * j + u / 8 < 144) := by omega
  have h6 : ¬ (296 + 30 * j + u / 8 < 176) := by omega
  have h7 : ¬ (296 + 30 * j + u / 8 < 296) := by omega
  have h8 : 296 + 30 * j + u / 8 < 506 := by omega
  unfold oldRecordByte
  rw [dite_neg h7, dite_pos h8]
  simp only [h1, h2, h3, h4, h5, h6, ite_false]
  have hdiv : (296 + 30 * j + u / 8 - 296) / 30 = j := by omega
  have hmod : (296 + 30 * j + u / 8 - 296) % 30 = u / 8 := by omega
  simp only [hdiv, hmod]
  by_cases hlow : u / 8 < 28
  · rw [ite_pos hlow, ite_pos (by omega)]
    rw [BitVec.getLsbD_extractLsb']
    simp [show u % 8 < 8 by omega, show 8 * (u / 8) + u % 8 = u by omega]
  · rw [ite_neg hlow]
    have hclean := clean ⟨j, hj⟩
    have htop0 : (f.bandB ⟨j, by omega⟩).getLsbD 238 = false := by
      have b := congrArg (fun v : BitVec 18 => v.getLsbD 0) hclean
      simpa [BitVec.getLsbD_extractLsb'] using b
    have htop1 : (f.bandB ⟨j, by omega⟩).getLsbD 239 = false := by
      have b := congrArg (fun v : BitVec 18 => v.getLsbD 1) hclean
      simpa [BitVec.getLsbD_extractLsb'] using b
    have htop0e : (f.bandB ⟨j, by omega⟩)[238] = false := by
      rw [← BitVec.getLsbD_eq_getElem]; exact htop0
    have htop1e : (f.bandB ⟨j, by omega⟩)[239] = false := by
      rw [← BitVec.getLsbD_eq_getElem]; exact htop1
    rw [BitVec.getLsbD_extractLsb']
    simp only [show u % 8 < 8 by omega, decide_true, Bool.true_and]
    unfold v1FoldHalf
    rw [BitVec.getLsbD_or, BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb']
    by_cases hlt238 : u < 238
    · rw [ite_pos hlt238]
      have h14 : ¬ (14 ≤ 8 * (u / 8 - 28) + u % 8) := by omega
      have h16 : 8 * (u / 8 - 28) + u % 8 < 16 := by omega
      have heq : 224 + (8 * (u / 8 - 28) + u % 8) = u := by omega
      simp [h14, h16, heq]
    · rw [ite_neg hlt238]
      have hu_eq : u = 238 ∨ u = 239 := by omega
      rcases hu_eq with rfl | rfl
      · simp [htop0e, show 2 * j < 16 by omega]
      · simp [htop1e, show 2 * j + 1 < 16 by omega, Nat.add_assoc]

private theorem oldBlock_bit_of_streamBitToOldBit (r : Nat) (block : Nat → RecordFields)
    (clean : ∀ p < r, BandBClean (block p)) (sbit : Nat) (hs : sbit < 368 * r) :
    let ob := streamBitToOldBit sbit
    ((oldBlockBytes r block)[ob / 8]?.getD 0).getLsbD (ob % 8) = bandBStreamBit block sbit := by
  dsimp only
  have hob_lt : streamBitToOldBit sbit < 4272 * r := streamBitToOldBit_lt r sbit hs
  rw [oldBlockBytes_getD r block (streamBitToOldBit sbit / 8) (by omega)]
  unfold streamBitToOldBit bandBStreamBit
  dsimp only
  set p := sbit / 368
  set s := sbit % 368
  have hp : p < r := by dsimp [p]; omega
  have hs_lt : s < 368 := Nat.mod_lt _ (by decide)
  by_cases h1 : s < 322
  · rw [ite_pos h1]
    set j := s / 46
    set t := s % 46
    have hj : j < 7 := by dsimp [j]; omega
    have ht : t < 46 := Nat.mod_lt _ (by decide)
    have hdiv1 : (4272 * p + 2560 + 240 * j + t) / 8 / 534 = p := by omega
    have hmod1 : (4272 * p + 2560 + 240 * j + t) / 8 % 534 = 296 + 30 * j + (192 + t) / 8 := by omega
    have hbit1 : (4272 * p + 2560 + 240 * j + t) % 8 = (192 + t) % 8 := by omega
    rw [hdiv1, hmod1, hbit1, oldRecordByte_getLsbD_bandB_clean (block p) (clean p hp) j hj (192 + t) (by omega)]
    rw [ite_pos (by omega), dite_pos (by omega)]
  · rw [ite_neg h1]
    by_cases h2 : s < 354
    · rw [ite_pos h2]
      have hdiv1 : (4272 * p + 4240 + (s - 322)) / 8 / 534 = p := by omega
      have hmod1 : (4272 * p + 4240 + (s - 322)) / 8 % 534 = 506 + (192 + (s - 322)) / 8 := by omega
      have hbit1 : (4272 * p + 4240 + (s - 322)) % 8 = (192 + (s - 322)) % 8 := by omega
      rw [hdiv1, hmod1, hbit1]
      unfold oldRecordByte
      have hlt506 : ¬ (506 + (192 + (s - 322)) / 8 < 506) := by omega
      have hlt296 : ¬ (506 + (192 + (s - 322)) / 8 < 296) := by omega
      rw [dite_neg hlt296, dite_neg hlt506]
      simp only [show ¬ (506 + (192 + (s - 322)) / 8 < 16) by omega,
        show ¬ (506 + (192 + (s - 322)) / 8 < 48) by omega,
        show ¬ (506 + (192 + (s - 322)) / 8 < 80) by omega,
        show ¬ (506 + (192 + (s - 322)) / 8 < 112) by omega,
        show ¬ (506 + (192 + (s - 322)) / 8 < 144) by omega,
        show ¬ (506 + (192 + (s - 322)) / 8 < 176) by omega, ite_false]
      rw [BitVec.getLsbD_extractLsb']
      have hj7 : s / 46 = 7 := by omega
      have ht7 : s % 46 = s - 322 := by omega
      simp [hj7, ht7, show (192 + (s - 322)) % 8 < 8 by omega,
        show 8 * ((192 + (s - 322)) / 8) + (192 + (s - 322)) % 8 = 192 + (s - 322) by omega]
    · rw [ite_neg h2]
      set j := (s - 354) / 2
      set u := (s - 354) % 2
      have hj : j < 7 := by dsimp [j]; omega
      have hu : u < 2 := Nat.mod_lt _ (by decide)
      have hdiv1 : (4272 * p + 2606 + 240 * j + u) / 8 / 534 = p := by omega
      have hmod1 : (4272 * p + 2606 + 240 * j + u) / 8 % 534 = 296 + 30 * j + (238 + u) / 8 := by omega
      have hbit1 : (4272 * p + 2606 + 240 * j + u) % 8 = (238 + u) % 8 := by omega
      rw [hdiv1, hmod1, hbit1, oldRecordByte_getLsbD_bandB_clean (block p) (clean p hp) j hj (238 + u) (by omega)]
      rw [ite_neg (by omega)]
      have hj7 : s / 46 = 7 := by omega
      have ht7 : 192 + s % 46 = 224 + 2 * j + (238 + u - 238) := by dsimp [j, u]; omega
      simp [hj7, ht7]

private theorem bandATailWord_getLsbD (f : RecordFields) (w : Fin 3) (b : Nat) (hb : b < 64) :
    (bandATailWord f w).getLsbD b =
      let off := 64 * w.val + b
      let a := off / 48
      let u := off % 48
      if ha : a < 4 then (f.bandA ⟨a, ha⟩).getLsbD (192 + u) else false := by
  fin_cases w
  · simp only [bandATailWord, Fin.zero_eta, Fin.val_zero, Nat.mul_zero, Nat.zero_add,
      BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb']
    by_cases h : b < 48
    · have ha : b / 48 = 0 := by omega
      have hu : b % 48 = b := by omega
      simp [h, hb, ha, hu]
    · have ha : b / 48 = 1 := by omega
      have hu : b % 48 = b - 48 := by omega
      simp [h, hb, ha, hu, show 48 ≤ b by omega, show b - 48 < 48 by omega, show b - 48 < 64 by omega]
  · simp only [bandATailWord, Fin.mk_one, Fin.val_one, Nat.mul_one,
      BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb']
    by_cases h : b < 32
    · have ha : (64 + b) / 48 = 1 := by omega
      have hu : (64 + b) % 48 = 16 + b := by omega
      simp [h, hb, ha, hu, show 16 + b < 48 by omega, show 16 + b < 64 by omega,
        show 192 + (16 + b) = 192 + (b + 16) by omega]
    · have ha : (64 + b) / 48 = 2 := by omega
      have hu : (64 + b) % 48 = b - 32 := by omega
      simp [h, hb, ha, hu, show 32 ≤ b by omega, show ¬ (16 + b < 48) by omega,
        show b - 32 < 48 by omega, show b - 32 < 64 by omega]
  · simp only [bandATailWord, Fin.reduceFinMk, Fin.val_two,
      BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb']
    by_cases h : b < 16
    · have ha : (128 + b) / 48 = 2 := by omega
      have hu : (128 + b) % 48 = 32 + b := by omega
      simp [h, hb, ha, hu, show 32 + b < 48 by omega, show 32 + b < 64 by omega,
        show 192 + (32 + b) = 192 + (b + 32) by omega]
    · have ha : (128 + b) / 48 = 3 := by omega
      have hu : (128 + b) % 48 = b - 16 := by omega
      simp [h, hb, ha, hu, show 16 ≤ b by omega, show ¬ (32 + b < 48) by omega,
        show b - 16 < 48 by omega, show b - 16 < 64 by omega]

private theorem newPhaseFixedBytes_getLsbD (f : RecordFields) (j b : Nat)
    (hj : j < 488) (hb : b < 8) :
    ((newPhaseFixedBytes f)[j]?.getD 0).getLsbD b =
      let off := 8 * j + b
      if off < 128 then f.salt.getLsbD off
      else if off < 384 then (f.mate 0).getLsbD (off - 128)
      else if off < 640 then (f.mate 1).getLsbD (off - 384)
      else if off < 896 then (f.mate 2).getLsbD (off - 640)
      else if off < 1152 then f.sib0.getLsbD (off - 896)
      else if off < 1408 then f.sib1.getLsbD (off - 1152)
      else if hA : off < 2176 then
        let a := (off - 1408) / 192
        let u := (off - 1408) % 192
        (f.bandA ⟨a, by omega⟩).getLsbD u
      else if hAt : off < 2368 then
        let a := (off - 2176) / 48
        let u := (off - 2176) % 48
        (f.bandA ⟨a, by omega⟩).getLsbD (192 + u)
      else
        let k := (off - 2368) / 192
        let u := (off - 2368) % 192
        if hk : k < 8 then (f.bandB ⟨k, hk⟩).getLsbD u else false := by
  -- Peel each fixed-size chunk of `newPhaseFixedBytes` directly via `getElem_append_nat`
  unfold newPhaseFixedBytes
  simp only [List.append_assoc, getElem_append_nat, leBytes_length, wordBytes_length]
  by_cases c0 : j < 16
  · rw [ite_pos c0, leBytes_getD _ _ c0, BitVec.getLsbD_extractLsb']; simp [hb, show 8 * j + b < 128 by omega]
  rw [ite_neg c0]
  by_cases c1 : j - 16 < 32
  · rw [ite_pos c1, leBytes_getD _ _ c1, BitVec.getLsbD_extractLsb']
    simp [hb, show ¬ (8 * j + b < 128) by omega, show 8 * j + b < 384 by omega,
      show 8 * (j - 16) + b = 8 * j + b - 128 by omega]
  rw [ite_neg c1]
  by_cases c2 : j - 16 - 32 < 32
  · rw [ite_pos c2, leBytes_getD _ _ c2, BitVec.getLsbD_extractLsb']
    simp [hb, show ¬ (8 * j + b < 128) by omega, show ¬ (8 * j + b < 384) by omega,
      show 8 * j + b < 640 by omega, show 8 * (j - 16 - 32) + b = 8 * j + b - 384 by omega]
  rw [ite_neg c2]
  by_cases c3 : j - 16 - 32 - 32 < 32
  · rw [ite_pos c3, leBytes_getD _ _ c3, BitVec.getLsbD_extractLsb']
    simp [hb, show ¬ (8 * j + b < 128) by omega, show ¬ (8 * j + b < 384) by omega,
      show ¬ (8 * j + b < 640) by omega, show 8 * j + b < 896 by omega,
      show 8 * (j - 16 - 32 - 32) + b = 8 * j + b - 640 by omega]
  rw [ite_neg c3]
  by_cases c4 : j - 16 - 32 - 32 - 32 < 32
  · rw [ite_pos c4, leBytes_getD _ _ c4, BitVec.getLsbD_extractLsb']
    simp [hb, show ¬ (8 * j + b < 128) by omega, show ¬ (8 * j + b < 384) by omega,
      show ¬ (8 * j + b < 640) by omega, show ¬ (8 * j + b < 896) by omega,
      show 8 * j + b < 1152 by omega, show 8 * (j - 16 - 32 - 32 - 32) + b = 8 * j + b - 896 by omega]
  rw [ite_neg c4]
  by_cases c5 : j - 16 - 32 - 32 - 32 - 32 < 32
  · rw [ite_pos c5, leBytes_getD _ _ c5, BitVec.getLsbD_extractLsb']
    simp [hb, show ¬ (8 * j + b < 128) by omega, show ¬ (8 * j + b < 384) by omega,
      show ¬ (8 * j + b < 640) by omega, show ¬ (8 * j + b < 896) by omega,
      show ¬ (8 * j + b < 1152) by omega, show 8 * j + b < 1408 by omega,
      show 8 * (j - 16 - 32 - 32 - 32 - 32) + b = 8 * j + b - 1152 by omega]
  rw [ite_neg c5]
  -- Band A bodies 0..3
  by_cases a0 : j - 16 - 32 - 32 - 32 - 32 - 32 < 24
  · rw [ite_pos a0, leBytes_getD _ _ a0, BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb']
    simp [hb, show ¬ (8 * j + b < 128) by omega, show ¬ (8 * j + b < 384) by omega,
      show ¬ (8 * j + b < 640) by omega, show ¬ (8 * j + b < 896) by omega,
      show ¬ (8 * j + b < 1152) by omega, show ¬ (8 * j + b < 1408) by omega,
      show 8 * j + b < 2176 by omega, show (8 * j + b - 1408) / 192 = 0 by omega,
      show (8 * j + b - 1408) % 192 = 8 * (j - 16 - 32 - 32 - 32 - 32 - 32) + b by omega,
      show 8 * (j - 16 - 32 - 32 - 32 - 32 - 32) + b < 192 by omega]
  rw [ite_neg a0]
  by_cases a1 : j - 16 - 32 - 32 - 32 - 32 - 32 - 24 < 24
  · rw [ite_pos a1, leBytes_getD _ _ a1, BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb']
    simp [hb, show ¬ (8 * j + b < 128) by omega, show ¬ (8 * j + b < 384) by omega,
      show ¬ (8 * j + b < 640) by omega, show ¬ (8 * j + b < 896) by omega,
      show ¬ (8 * j + b < 1152) by omega, show ¬ (8 * j + b < 1408) by omega,
      show 8 * j + b < 2176 by omega, show (8 * j + b - 1408) / 192 = 1 by omega,
      show (8 * j + b - 1408) % 192 = 8 * (j - 16 - 32 - 32 - 32 - 32 - 32 - 24) + b by omega,
      show 8 * (j - 16 - 32 - 32 - 32 - 32 - 32 - 24) + b < 192 by omega]
  rw [ite_neg a1]
  by_cases a2 : j - 16 - 32 - 32 - 32 - 32 - 32 - 24 - 24 < 24
  · rw [ite_pos a2, leBytes_getD _ _ a2, BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb']
    simp [hb, show ¬ (8 * j + b < 128) by omega, show ¬ (8 * j + b < 384) by omega,
      show ¬ (8 * j + b < 640) by omega, show ¬ (8 * j + b < 896) by omega,
      show ¬ (8 * j + b < 1152) by omega, show ¬ (8 * j + b < 1408) by omega,
      show 8 * j + b < 2176 by omega, show (8 * j + b - 1408) / 192 = 2 by omega,
      show (8 * j + b - 1408) % 192 = 8 * (j - 16 - 32 - 32 - 32 - 32 - 32 - 24 - 24) + b by omega,
      show 8 * (j - 16 - 32 - 32 - 32 - 32 - 32 - 24 - 24) + b < 192 by omega]
  rw [ite_neg a2]
  by_cases a3 : j - 16 - 32 - 32 - 32 - 32 - 32 - 24 - 24 - 24 < 24
  · rw [ite_pos a3, leBytes_getD _ _ a3, BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb']
    simp [hb, show ¬ (8 * j + b < 128) by omega, show ¬ (8 * j + b < 384) by omega,
      show ¬ (8 * j + b < 640) by omega, show ¬ (8 * j + b < 896) by omega,
      show ¬ (8 * j + b < 1152) by omega, show ¬ (8 * j + b < 1408) by omega,
      show 8 * j + b < 2176 by omega, show (8 * j + b - 1408) / 192 = 3 by omega,
      show (8 * j + b - 1408) % 192 = 8 * (j - 16 - 32 - 32 - 32 - 32 - 32 - 24 - 24 - 24) + b by omega,
      show 8 * (j - 16 - 32 - 32 - 32 - 32 - 32 - 24 - 24 - 24) + b < 192 by omega]
  rw [ite_neg a3]
  -- Band A tail words 0..2
  by_cases w0 : j - 16 - 32 - 32 - 32 - 32 - 32 - 24 - 24 - 24 - 24 < 8
  · rw [ite_pos w0, wordBytes_getD _ _ w0, BitVec.getLsbD_extractLsb']
    simp only [hb, decide_true, Bool.true_and]
    rw [bandATailWord_getLsbD f 0 _ (by omega)]
    have ho : 8 * (j - 16 - 32 - 32 - 32 - 32 - 32 - 24 - 24 - 24 - 24) + b = 8 * j + b - 2176 := by omega
    simp [ho, show ¬ (8 * j + b < 128) by omega, show ¬ (8 * j + b < 384) by omega,
      show ¬ (8 * j + b < 640) by omega, show ¬ (8 * j + b < 896) by omega,
      show ¬ (8 * j + b < 1152) by omega, show ¬ (8 * j + b < 1408) by omega,
      show ¬ (8 * j + b < 2176) by omega, show 8 * j + b < 2368 by omega,
      show (8 * j + b - 2176) / 48 < 4 by omega]
  rw [ite_neg w0]
  by_cases w1 : j - 16 - 32 - 32 - 32 - 32 - 32 - 24 - 24 - 24 - 24 - 8 < 8
  · rw [ite_pos w1, wordBytes_getD _ _ w1, BitVec.getLsbD_extractLsb']
    simp only [hb, decide_true, Bool.true_and]
    rw [bandATailWord_getLsbD f 1 _ (by omega)]
    have ho : 64 + (8 * (j - 16 - 32 - 32 - 32 - 32 - 32 - 24 - 24 - 24 - 24 - 8) + b) = 8 * j + b - 2176 := by omega
    simp [ho, show ¬ (8 * j + b < 128) by omega, show ¬ (8 * j + b < 384) by omega,
      show ¬ (8 * j + b < 640) by omega, show ¬ (8 * j + b < 896) by omega,
      show ¬ (8 * j + b < 1152) by omega, show ¬ (8 * j + b < 1408) by omega,
      show ¬ (8 * j + b < 2176) by omega, show 8 * j + b < 2368 by omega,
      show (8 * j + b - 2176) / 48 < 4 by omega]
  rw [ite_neg w1]
  by_cases w2 : j - 16 - 32 - 32 - 32 - 32 - 32 - 24 - 24 - 24 - 24 - 8 - 8 < 8
  · rw [ite_pos w2, wordBytes_getD _ _ w2, BitVec.getLsbD_extractLsb']
    simp only [hb, decide_true, Bool.true_and]
    rw [bandATailWord_getLsbD f 2 _ (by omega)]
    have ho : 128 + (8 * (j - 16 - 32 - 32 - 32 - 32 - 32 - 24 - 24 - 24 - 24 - 8 - 8) + b) = 8 * j + b - 2176 := by omega
    simp [ho, show ¬ (8 * j + b < 128) by omega, show ¬ (8 * j + b < 384) by omega,
      show ¬ (8 * j + b < 640) by omega, show ¬ (8 * j + b < 896) by omega,
      show ¬ (8 * j + b < 1152) by omega, show ¬ (8 * j + b < 1408) by omega,
      show ¬ (8 * j + b < 2176) by omega, show 8 * j + b < 2368 by omega,
      show (8 * j + b - 2176) / 48 < 4 by omega]
  rw [ite_neg w2]
  -- Band B bodies 0..7
  by_cases b0 : j - 16 - 32 - 32 - 32 - 32 - 32 - 24 - 24 - 24 - 24 - 8 - 8 - 8 < 24
  · rw [ite_pos b0, leBytes_getD _ _ b0, BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb']
    simp [hb, show ¬ (8 * j + b < 128) by omega, show ¬ (8 * j + b < 384) by omega,
      show ¬ (8 * j + b < 640) by omega, show ¬ (8 * j + b < 896) by omega,
      show ¬ (8 * j + b < 1152) by omega, show ¬ (8 * j + b < 1408) by omega,
      show ¬ (8 * j + b < 2176) by omega, show ¬ (8 * j + b < 2368) by omega,
      show (8 * j + b - 2368) / 192 = 0 by omega,
      show (8 * j + b - 2368) % 192 = 8 * (j - 16 - 32 - 32 - 32 - 32 - 32 - 24 - 24 - 24 - 24 - 8 - 8 - 8) + b by omega,
      show 8 * (j - 16 - 32 - 32 - 32 - 32 - 32 - 24 - 24 - 24 - 24 - 8 - 8 - 8) + b < 192 by omega]
  rw [ite_neg b0]
  by_cases b1 : j - 16 - 32 - 32 - 32 - 32 - 32 - 24 - 24 - 24 - 24 - 8 - 8 - 8 - 24 < 24
  · rw [ite_pos b1, leBytes_getD _ _ b1, BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb']
    simp [hb, show ¬ (8 * j + b < 128) by omega, show ¬ (8 * j + b < 384) by omega,
      show ¬ (8 * j + b < 640) by omega, show ¬ (8 * j + b < 896) by omega,
      show ¬ (8 * j + b < 1152) by omega, show ¬ (8 * j + b < 1408) by omega,
      show ¬ (8 * j + b < 2176) by omega, show ¬ (8 * j + b < 2368) by omega,
      show (8 * j + b - 2368) / 192 = 1 by omega,
      show (8 * j + b - 2368) % 192 = 8 * (j - 16 - 32 - 32 - 32 - 32 - 32 - 24 - 24 - 24 - 24 - 8 - 8 - 8 - 24) + b by omega,
      show 8 * (j - 16 - 32 - 32 - 32 - 32 - 32 - 24 - 24 - 24 - 24 - 8 - 8 - 8 - 24) + b < 192 by omega]
  rw [ite_neg b1]
  by_cases b2 : j - 16 - 32 - 32 - 32 - 32 - 32 - 24 - 24 - 24 - 24 - 8 - 8 - 8 - 24 - 24 < 24
  · rw [ite_pos b2, leBytes_getD _ _ b2, BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb']
    simp [hb, show ¬ (8 * j + b < 128) by omega, show ¬ (8 * j + b < 384) by omega,
      show ¬ (8 * j + b < 640) by omega, show ¬ (8 * j + b < 896) by omega,
      show ¬ (8 * j + b < 1152) by omega, show ¬ (8 * j + b < 1408) by omega,
      show ¬ (8 * j + b < 2176) by omega, show ¬ (8 * j + b < 2368) by omega,
      show (8 * j + b - 2368) / 192 = 2 by omega,
      show (8 * j + b - 2368) % 192 = 8 * (j - 16 - 32 - 32 - 32 - 32 - 32 - 24 - 24 - 24 - 24 - 8 - 8 - 8 - 24 - 24) + b by omega,
      show 8 * (j - 16 - 32 - 32 - 32 - 32 - 32 - 24 - 24 - 24 - 24 - 8 - 8 - 8 - 24 - 24) + b < 192 by omega]
  rw [ite_neg b2]
  by_cases b3 : j - 16 - 32 - 32 - 32 - 32 - 32 - 24 - 24 - 24 - 24 - 8 - 8 - 8 - 24 - 24 - 24 < 24
  · rw [ite_pos b3, leBytes_getD _ _ b3, BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb']
    simp [hb, show ¬ (8 * j + b < 128) by omega, show ¬ (8 * j + b < 384) by omega,
      show ¬ (8 * j + b < 640) by omega, show ¬ (8 * j + b < 896) by omega,
      show ¬ (8 * j + b < 1152) by omega, show ¬ (8 * j + b < 1408) by omega,
      show ¬ (8 * j + b < 2176) by omega, show ¬ (8 * j + b < 2368) by omega,
      show (8 * j + b - 2368) / 192 = 3 by omega,
      show (8 * j + b - 2368) % 192 = 8 * (j - 16 - 32 - 32 - 32 - 32 - 32 - 24 - 24 - 24 - 24 - 8 - 8 - 8 - 24 - 24 - 24) + b by omega,
      show 8 * (j - 16 - 32 - 32 - 32 - 32 - 32 - 24 - 24 - 24 - 24 - 8 - 8 - 8 - 24 - 24 - 24) + b < 192 by omega]
  rw [ite_neg b3]
  by_cases b4 : j - 16 - 32 - 32 - 32 - 32 - 32 - 24 - 24 - 24 - 24 - 8 - 8 - 8 - 24 - 24 - 24 - 24 < 24
  · rw [ite_pos b4, leBytes_getD _ _ b4, BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb']
    simp [hb, show ¬ (8 * j + b < 128) by omega, show ¬ (8 * j + b < 384) by omega,
      show ¬ (8 * j + b < 640) by omega, show ¬ (8 * j + b < 896) by omega,
      show ¬ (8 * j + b < 1152) by omega, show ¬ (8 * j + b < 1408) by omega,
      show ¬ (8 * j + b < 2176) by omega, show ¬ (8 * j + b < 2368) by omega,
      show (8 * j + b - 2368) / 192 = 4 by omega,
      show (8 * j + b - 2368) % 192 = 8 * (j - 16 - 32 - 32 - 32 - 32 - 32 - 24 - 24 - 24 - 24 - 8 - 8 - 8 - 24 - 24 - 24 - 24) + b by omega,
      show 8 * (j - 16 - 32 - 32 - 32 - 32 - 32 - 24 - 24 - 24 - 24 - 8 - 8 - 8 - 24 - 24 - 24 - 24) + b < 192 by omega]
  rw [ite_neg b4]
  by_cases b5 : j - 16 - 32 - 32 - 32 - 32 - 32 - 24 - 24 - 24 - 24 - 8 - 8 - 8 - 24 - 24 - 24 - 24 - 24 < 24
  · rw [ite_pos b5, leBytes_getD _ _ b5, BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb']
    simp [hb, show ¬ (8 * j + b < 128) by omega, show ¬ (8 * j + b < 384) by omega,
      show ¬ (8 * j + b < 640) by omega, show ¬ (8 * j + b < 896) by omega,
      show ¬ (8 * j + b < 1152) by omega, show ¬ (8 * j + b < 1408) by omega,
      show ¬ (8 * j + b < 2176) by omega, show ¬ (8 * j + b < 2368) by omega,
      show (8 * j + b - 2368) / 192 = 5 by omega,
      show (8 * j + b - 2368) % 192 = 8 * (j - 16 - 32 - 32 - 32 - 32 - 32 - 24 - 24 - 24 - 24 - 8 - 8 - 8 - 24 - 24 - 24 - 24 - 24) + b by omega,
      show 8 * (j - 16 - 32 - 32 - 32 - 32 - 32 - 24 - 24 - 24 - 24 - 8 - 8 - 8 - 24 - 24 - 24 - 24 - 24) + b < 192 by omega]
  rw [ite_neg b5]
  by_cases b6 : j - 16 - 32 - 32 - 32 - 32 - 32 - 24 - 24 - 24 - 24 - 8 - 8 - 8 - 24 - 24 - 24 - 24 - 24 - 24 < 24
  · rw [ite_pos b6, leBytes_getD _ _ b6, BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb']
    simp [hb, show ¬ (8 * j + b < 128) by omega, show ¬ (8 * j + b < 384) by omega,
      show ¬ (8 * j + b < 640) by omega, show ¬ (8 * j + b < 896) by omega,
      show ¬ (8 * j + b < 1152) by omega, show ¬ (8 * j + b < 1408) by omega,
      show ¬ (8 * j + b < 2176) by omega, show ¬ (8 * j + b < 2368) by omega,
      show (8 * j + b - 2368) / 192 = 6 by omega,
      show (8 * j + b - 2368) % 192 = 8 * (j - 16 - 32 - 32 - 32 - 32 - 32 - 24 - 24 - 24 - 24 - 8 - 8 - 8 - 24 - 24 - 24 - 24 - 24 - 24) + b by omega,
      show 8 * (j - 16 - 32 - 32 - 32 - 32 - 32 - 24 - 24 - 24 - 24 - 8 - 8 - 8 - 24 - 24 - 24 - 24 - 24 - 24) + b < 192 by omega]
  rw [ite_neg b6]
  rw [leBytes_getD _ _ (by omega), BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb']
  simp [hb, show ¬ (8 * j + b < 128) by omega, show ¬ (8 * j + b < 384) by omega,
    show ¬ (8 * j + b < 640) by omega, show ¬ (8 * j + b < 896) by omega,
    show ¬ (8 * j + b < 1152) by omega, show ¬ (8 * j + b < 1408) by omega,
    show ¬ (8 * j + b < 2176) by omega, show ¬ (8 * j + b < 2368) by omega,
    show (8 * j + b - 2368) / 192 = 7 by omega,
    show (8 * j + b - 2368) % 192 = 8 * (j - 16 - 32 - 32 - 32 - 32 - 32 - 24 - 24 - 24 - 24 - 8 - 8 - 8 - 24 - 24 - 24 - 24 - 24 - 24 - 24) + b by omega,
    show 8 * (j - 16 - 32 - 32 - 32 - 32 - 32 - 24 - 24 - 24 - 24 - 8 - 8 - 8 - 24 - 24 - 24 - 24 - 24 - 24 - 24) + b < 192 by omega]

private theorem oldBlock_bit_of_nonStreamToOldBit (r : Nat) (block : Nat → RecordFields)
    (clean : ∀ p < r, BandBClean (block p)) (p : Nat) (hp : p < r) (j b : Nat)
    (hj : j < 488) (hb : b < 8) :
    let ob := nonStreamToOldBit p (8 * j + b)
    ((oldBlockBytes r block)[ob / 8]?.getD 0).getLsbD (ob % 8) =
      ((newPhaseFixedBytes (block p))[j]?.getD 0).getLsbD b := by
  dsimp only
  have hob_lt : nonStreamToOldBit p (8 * j + b) < 4272 * r :=
    nonStreamToOldBit_lt r p (8 * j + b) hp (by omega)
  rw [oldBlockBytes_getD r block (nonStreamToOldBit p (8 * j + b) / 8) (by omega),
    newPhaseFixedBytes_getLsbD (block p) j b hj hb]
  unfold nonStreamToOldBit
  dsimp only
  by_cases h1 : 8 * j + b < 1408
  · rw [ite_pos h1]
    have hdiv : (4272 * p + (8 * j + b)) / 8 / 534 = p := by omega
    have hmod : (4272 * p + (8 * j + b)) / 8 % 534 = j := by omega
    have hbit : (4272 * p + (8 * j + b)) % 8 = b := by omega
    rw [hdiv, hmod, hbit]
    unfold oldRecordByte
    split_ifs <;> try omega
    all_goals (rw [BitVec.getLsbD_extractLsb']; simp [hb]; try (congr 1; omega))
  · rw [ite_neg h1]
    by_cases h2 : 8 * j + b < 2176
    · rw [ite_pos h2]
      set a := (8 * j + b - 1408) / 192
      set u := (8 * j + b - 1408) % 192
      have ha : a < 4 := by dsimp [a]; omega
      have hu : u < 192 := Nat.mod_lt _ (by decide)
      have hdiv : (4272 * p + 1408 + 240 * a + u) / 8 / 534 = p := by omega
      have hmod : (4272 * p + 1408 + 240 * a + u) / 8 % 534 = 176 + 30 * a + u / 8 := by omega
      have hbit : (4272 * p + 1408 + 240 * a + u) % 8 = u % 8 := by omega
      rw [hdiv, hmod, hbit]
      unfold oldRecordByte
      have hA : 176 + 30 * a + u / 8 < 296 := by omega
      rw [dite_pos hA]
      simp only [show ¬ (176 + 30 * a + u / 8 < 16) by omega, show ¬ (176 + 30 * a + u / 8 < 48) by omega,
        show ¬ (176 + 30 * a + u / 8 < 80) by omega, show ¬ (176 + 30 * a + u / 8 < 112) by omega,
        show ¬ (176 + 30 * a + u / 8 < 144) by omega, show ¬ (176 + 30 * a + u / 8 < 176) by omega,
        show ¬ (8 * j + b < 128) by omega, show ¬ (8 * j + b < 384) by omega,
        show ¬ (8 * j + b < 640) by omega, show ¬ (8 * j + b < 896) by omega,
        show ¬ (8 * j + b < 1152) by omega, h1, h2, ite_false, dite_true]
      rw [BitVec.getLsbD_extractLsb']
      simp only [show u % 8 < 8 by omega, decide_true, Bool.true_and,
        show (176 + 30 * a + u / 8 - 176) / 30 = a by omega,
        show (176 + 30 * a + u / 8 - 176) % 30 = u / 8 by omega, show 8 * (u / 8) + u % 8 = u by omega]
      rfl
    · rw [ite_neg h2]
      by_cases h3 : 8 * j + b < 2368
      · rw [ite_pos h3]
        set a := (8 * j + b - 2176) / 48
        set u := (8 * j + b - 2176) % 48
        have ha : a < 4 := by dsimp [a]; omega
        have hu : u < 48 := Nat.mod_lt _ (by decide)
        have hdiv : (4272 * p + 1600 + 240 * a + u) / 8 / 534 = p := by omega
        have hmod : (4272 * p + 1600 + 240 * a + u) / 8 % 534 = 176 + 30 * a + (192 + u) / 8 := by omega
        have hbit : (4272 * p + 1600 + 240 * a + u) % 8 = (192 + u) % 8 := by omega
        rw [hdiv, hmod, hbit]
        unfold oldRecordByte
        have hA : 176 + 30 * a + (192 + u) / 8 < 296 := by omega
        rw [dite_pos hA]
        simp only [show ¬ (176 + 30 * a + (192 + u) / 8 < 16) by omega,
          show ¬ (176 + 30 * a + (192 + u) / 8 < 48) by omega,
          show ¬ (176 + 30 * a + (192 + u) / 8 < 80) by omega,
          show ¬ (176 + 30 * a + (192 + u) / 8 < 112) by omega,
          show ¬ (176 + 30 * a + (192 + u) / 8 < 144) by omega,
          show ¬ (176 + 30 * a + (192 + u) / 8 < 176) by omega,
          show ¬ (8 * j + b < 128) by omega, show ¬ (8 * j + b < 384) by omega,
          show ¬ (8 * j + b < 640) by omega, show ¬ (8 * j + b < 896) by omega,
          show ¬ (8 * j + b < 1152) by omega, h1, h2, h3, ite_false, dite_false, dite_true]
        rw [BitVec.getLsbD_extractLsb']
        simp only [show (192 + u) % 8 < 8 by omega, decide_true, Bool.true_and,
          show (176 + 30 * a + (192 + u) / 8 - 176) / 30 = a by omega,
          show (176 + 30 * a + (192 + u) / 8 - 176) % 30 = (192 + u) / 8 by omega,
          show 8 * ((192 + u) / 8) + (192 + u) % 8 = 192 + u by omega]
        rfl
      · rw [ite_neg h3]
        by_cases h4 : 8 * j + b < 3712
        · rw [ite_pos h4]
          set k := (8 * j + b - 2368) / 192
          set u := (8 * j + b - 2368) % 192
          have hk : k < 7 := by dsimp [k]; omega
          have hu : u < 192 := Nat.mod_lt _ (by decide)
          have hdiv : (4272 * p + 2368 + 240 * k + u) / 8 / 534 = p := by omega
          have hmod : (4272 * p + 2368 + 240 * k + u) / 8 % 534 = 296 + 30 * k + u / 8 := by omega
          have hbit : (4272 * p + 2368 + 240 * k + u) % 8 = u % 8 := by omega
          rw [hdiv, hmod, hbit,
            oldRecordByte_getLsbD_bandB_clean (block p) (clean p hp) k hk u (by omega)]
          rw [ite_pos (by omega)]
          simp [show ¬ (8 * j + b < 128) by omega, show ¬ (8 * j + b < 384) by omega,
            show ¬ (8 * j + b < 640) by omega, show ¬ (8 * j + b < 896) by omega,
            show ¬ (8 * j + b < 1152) by omega, h1, h2, h3, show k < 8 by omega]
        · rw [ite_neg h4]
          set u := 8 * j + b - 3712
          have hu : u < 192 := by dsimp [u]; omega
          have hdiv : (4272 * p + 4048 + u) / 8 / 534 = p := by omega
          have hmod : (4272 * p + 4048 + u) / 8 % 534 = 506 + u / 8 := by omega
          have hbit : (4272 * p + 4048 + u) % 8 = u % 8 := by omega
          rw [hdiv, hmod, hbit]
          unfold oldRecordByte
          rw [dite_neg (by omega), dite_neg (by omega)]
          simp only [show ¬ (506 + u / 8 < 16) by omega, show ¬ (506 + u / 8 < 48) by omega,
            show ¬ (506 + u / 8 < 80) by omega, show ¬ (506 + u / 8 < 112) by omega,
            show ¬ (506 + u / 8 < 144) by omega, show ¬ (506 + u / 8 < 176) by omega,
            show ¬ (8 * j + b < 128) by omega, show ¬ (8 * j + b < 384) by omega,
            show ¬ (8 * j + b < 640) by omega, show ¬ (8 * j + b < 896) by omega,
            show ¬ (8 * j + b < 1152) by omega, h1, h2, h3, ite_false, dite_false]
          rw [BitVec.getLsbD_extractLsb']
          simp [show u % 8 < 8 by omega, show (8 * j + b - 2368) / 192 = 7 by omega,
            show (8 * j + b - 2368) % 192 = u by omega, show 8 * (u / 8) + u % 8 = u by omega]

private theorem streamDwords_getD (block : Nat → RecordFields) (start cnt j : Nat) (hj : j < 8 * cnt) :
    (((List.range cnt).flatMap fun d => wordBytes (bandBStreamDword block (start + d)))[j]?.getD 0) =
      (bandBStreamDword block (start + j / 8)).extractLsb' (8 * (j % 8)) 8 := by
  induction cnt generalizing j with
  | zero => omega
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, getElem_append_nat]
    have hlen : ((List.range m).flatMap fun d => wordBytes (bandBStreamDword block (start + d))).length = 8 * m := by
      rw [List.length_flatMap, List.map_congr_left (fun _ _ => wordBytes_length _)]
      simp [Nat.mul_comm]
    rw [hlen]
    by_cases h : j < 8 * m
    · rw [ite_pos h]; exact ih j h
    · rw [ite_neg h]
      have hdiv : j / 8 = m := by omega
      have hmod : j % 8 = j - 8 * m := by omega
      rw [hdiv, hmod, wordBytes_getD _ _ (by omega)]

private theorem newPhaseBytes_getD_fixed (p : Nat) (block : Nat → RecordFields) (j : Nat) (hj : j < 488) :
    (newPhaseBytes p block)[j]?.getD 0 = (newPhaseFixedBytes (block p))[j]?.getD 0 := by
  unfold newPhaseBytes
  rw [getElem_append_nat, newPhaseFixedBytes_length, ite_pos hj]

private theorem newPhaseBytes_getD_stream (p : Nat) (block : Nat → RecordFields) (j : Nat)
    (lo : 488 ≤ j) (hi : j < 488 + 8 * phaseStreamCount p) :
    (newPhaseBytes p block)[j]?.getD 0 =
      (bandBStreamDword block (phaseStreamStart p + (j - 488) / 8)).extractLsb' (8 * ((j - 488) % 8)) 8 := by
  unfold newPhaseBytes
  rw [getElem_append_nat, newPhaseFixedBytes_length, ite_neg (by omega)]
  exact streamDwords_getD block (phaseStreamStart p) (phaseStreamCount p) (j - 488) (by omega)

private theorem newBlockBytes_getLsbD (r : Nat) (lo : 1 ≤ r) (hi : r ≤ 4)
    (block : Nat → RecordFields) (clean : ∀ p < r, BandBClean (block p))
    (j b : Nat) (hj : j < 534 * r) (hb : b < 8) :
    ((newBlockBytes r block)[j]?.getD 0).getLsbD b =
      let ob := encTables r (8 * j + b)
      ((oldBlockBytes r block)[ob / 8]?.getD 0).getLsbD (ob % 8) := by
  have hr : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by omega
  rcases hr with rfl | rfl | rfl | rfl
  · -- r = 1
    unfold newBlockBytes newPartialFlush
    simp only [List.range_succ, List.range_zero, List.nil_append, List.flatMap_singleton, ite_true,
      getElem_append_nat, newPhaseBytes_length]
    by_cases h488 : j < 488
    · rw [ite_pos (by omega), newPhaseBytes_getD_fixed 0 block j h488]
      have henc : encTables 1 (8 * j + b) = nonStreamToOldBit 0 (8 * j + b) := by
        unfold encTables; rw [ite_pos (by omega)]
      rw [henc, oldBlock_bit_of_nonStreamToOldBit 1 block clean 0 (by decide) j b h488 hb]
    · by_cases h528 : j < 528
      · rw [ite_pos h528, newPhaseBytes_getD_stream 0 block j (by omega) (by rw [phaseStreamCount_0]; omega)]
        rw [BitVec.getLsbD_extractLsb', bandBStreamDword_getLsbD _ _ _ (by omega)]
        have henc : encTables 1 (8 * j + b) = streamBitToOldBit (8 * j + b - 3904) := by
          unfold encTables; rw [ite_neg (by omega), ite_pos rfl]
        rw [henc, oldBlock_bit_of_streamBitToOldBit 1 block clean _ (by omega)]
        simp only [hb, decide_true, Bool.true_and, phaseStreamStart_0, Nat.zero_add]
        exact congrArg (bandBStreamBit block) (by omega)
      · rw [ite_neg h528, List.getElem?_take_of_lt (by omega), wordBytes_getD _ _ (by omega),
          BitVec.getLsbD_extractLsb', bandBStreamDword_getLsbD _ _ _ (by omega)]
        have henc : encTables 1 (8 * j + b) = streamBitToOldBit (8 * j + b - 3904) := by
          unfold encTables; rw [ite_neg (by omega), ite_pos rfl]
        rw [henc, oldBlock_bit_of_streamBitToOldBit 1 block clean _ (by omega)]
        simp only [hb, decide_true, Bool.true_and]
        exact congrArg (bandBStreamBit block) (by omega)
  · -- r = 2
    unfold newBlockBytes newPartialFlush
    simp only [List.range_succ, List.range_zero, List.nil_append, List.flatMap_append,
      List.flatMap_singleton, List.append_assoc, show ¬ (2 = 1) by decide,
      show ¬ (1 = 0) by decide, ite_false, ite_true, getElem_append_nat, newPhaseBytes_length]
    by_cases h528 : j < 528
    · rw [ite_pos h528]
      by_cases h488 : j < 488
      · rw [newPhaseBytes_getD_fixed 0 block j h488]
        have henc : encTables 2 (8 * j + b) = nonStreamToOldBit 0 (8 * j + b) := by
          unfold encTables; rw [ite_pos (by omega)]
        rw [henc, oldBlock_bit_of_nonStreamToOldBit 2 block clean 0 (by decide) j b h488 hb]
      · rw [newPhaseBytes_getD_stream 0 block j (by omega) (by rw [phaseStreamCount_0]; omega),
          BitVec.getLsbD_extractLsb', bandBStreamDword_getLsbD _ _ _ (by omega)]
        have henc : encTables 2 (8 * j + b) = streamBitToOldBit (8 * j + b - 3904) := by
          unfold encTables; rw [ite_neg (by omega), ite_neg (by decide), ite_pos (by omega)]
        rw [henc, oldBlock_bit_of_streamBitToOldBit 2 block clean _ (by omega)]
        simp only [hb, decide_true, Bool.true_and, phaseStreamStart_0, Nat.zero_add]
        exact congrArg (bandBStreamBit block) (by omega)
    · rw [ite_neg h528]
      by_cases h1064 : j - 528 < 536
      · rw [ite_pos h1064]
        by_cases h488 : j - 528 < 488
        · rw [newPhaseBytes_getD_fixed 1 block (j - 528) h488]
          have henc : encTables 2 (8 * j + b) = nonStreamToOldBit 1 (8 * (j - 528) + b) := by
            unfold encTables
            rw [ite_neg (by omega), ite_neg (by decide), ite_neg (by omega), ite_pos (by omega)]
            exact congrArg (nonStreamToOldBit 1) (by omega)
          rw [henc, oldBlock_bit_of_nonStreamToOldBit 2 block clean 1 (by decide) (j - 528) b h488 hb]
        · rw [newPhaseBytes_getD_stream 1 block (j - 528) (by omega) (by rw [phaseStreamCount_1]; omega),
            BitVec.getLsbD_extractLsb', bandBStreamDword_getLsbD _ _ _ (by omega)]
          have henc : encTables 2 (8 * j + b) = streamBitToOldBit (320 + (8 * j + b - 8128)) := by
            unfold encTables
            rw [ite_neg (by omega), ite_neg (by decide), ite_neg (by omega), ite_neg (by omega), ite_pos rfl]
          rw [henc, oldBlock_bit_of_streamBitToOldBit 2 block clean _ (by omega)]
          simp only [hb, decide_true, Bool.true_and, phaseStreamStart_1]
          exact congrArg (bandBStreamBit block) (by omega)
      · rw [ite_neg h1064, List.getElem?_take_of_lt (by omega), wordBytes_getD _ _ (by omega),
          BitVec.getLsbD_extractLsb', bandBStreamDword_getLsbD _ _ _ (by omega)]
        have henc : encTables 2 (8 * j + b) = streamBitToOldBit (320 + (8 * j + b - 8128)) := by
          unfold encTables
          rw [ite_neg (by omega), ite_neg (by decide), ite_neg (by omega), ite_neg (by omega), ite_pos rfl]
        rw [henc, oldBlock_bit_of_streamBitToOldBit 2 block clean _ (by omega)]
        simp only [hb, decide_true, Bool.true_and]
        exact congrArg (bandBStreamBit block) (by omega)
  · -- r = 3
    unfold newBlockBytes newPartialFlush
    simp only [List.range_succ, List.range_zero, List.nil_append, List.flatMap_append,
      List.flatMap_singleton, List.append_assoc, show ¬ (3 = 1) by decide, show ¬ (3 = 2) by decide,
      show ¬ (1 = 0) by decide, show ¬ (2 = 0) by decide,
      ite_false, ite_true, getElem_append_nat, newPhaseBytes_length]
    by_cases h528 : j < 528
    · rw [ite_pos h528]
      by_cases h488 : j < 488
      · rw [newPhaseBytes_getD_fixed 0 block j h488]
        have henc : encTables 3 (8 * j + b) = nonStreamToOldBit 0 (8 * j + b) := by
          unfold encTables; rw [ite_pos (by omega)]
        rw [henc, oldBlock_bit_of_nonStreamToOldBit 3 block clean 0 (by decide) j b h488 hb]
      · rw [newPhaseBytes_getD_stream 0 block j (by omega) (by rw [phaseStreamCount_0]; omega),
          BitVec.getLsbD_extractLsb', bandBStreamDword_getLsbD _ _ _ (by omega)]
        have henc : encTables 3 (8 * j + b) = streamBitToOldBit (8 * j + b - 3904) := by
          unfold encTables; rw [ite_neg (by omega), ite_neg (by decide), ite_pos (by omega)]
        rw [henc, oldBlock_bit_of_streamBitToOldBit 3 block clean _ (by omega)]
        simp only [hb, decide_true, Bool.true_and, phaseStreamStart_0, Nat.zero_add]
        exact congrArg (bandBStreamBit block) (by omega)
    · rw [ite_neg h528]
      by_cases h1064 : j - 528 < 536
      · rw [ite_pos h1064]
        by_cases h488 : j - 528 < 488
        · rw [newPhaseBytes_getD_fixed 1 block (j - 528) h488]
          have henc : encTables 3 (8 * j + b) = nonStreamToOldBit 1 (8 * (j - 528) + b) := by
            unfold encTables
            rw [ite_neg (by omega), ite_neg (by decide), ite_neg (by omega), ite_pos (by omega)]
            exact congrArg (nonStreamToOldBit 1) (by omega)
          rw [henc, oldBlock_bit_of_nonStreamToOldBit 3 block clean 1 (by decide) (j - 528) b h488 hb]
        · rw [newPhaseBytes_getD_stream 1 block (j - 528) (by omega) (by rw [phaseStreamCount_1]; omega),
            BitVec.getLsbD_extractLsb', bandBStreamDword_getLsbD _ _ _ (by omega)]
          have henc : encTables 3 (8 * j + b) = streamBitToOldBit (320 + (8 * j + b - 8128)) := by
            unfold encTables
            rw [ite_neg (by omega), ite_neg (by decide), ite_neg (by omega), ite_neg (by omega),
              ite_neg (by decide), ite_pos (by omega)]
          rw [henc, oldBlock_bit_of_streamBitToOldBit 3 block clean _ (by omega)]
          simp only [hb, decide_true, Bool.true_and, phaseStreamStart_1]
          exact congrArg (bandBStreamBit block) (by omega)
      · rw [ite_neg h1064]
        by_cases h1600 : j - 528 - 536 < 536
        · rw [ite_pos h1600]
          by_cases h488 : j - 528 - 536 < 488
          · rw [newPhaseBytes_getD_fixed 2 block (j - 528 - 536) h488]
            have henc : encTables 3 (8 * j + b) = nonStreamToOldBit 2 (8 * (j - 528 - 536) + b) := by
              unfold encTables
              rw [ite_neg (by omega), ite_neg (by decide), ite_neg (by omega), ite_neg (by omega),
                ite_neg (by decide), ite_neg (by omega), ite_pos (by omega)]
              exact congrArg (nonStreamToOldBit 2) (by omega)
            rw [henc, oldBlock_bit_of_nonStreamToOldBit 3 block clean 2 (by decide) (j - 528 - 536) b h488 hb]
          · rw [newPhaseBytes_getD_stream 2 block (j - 528 - 536) (by omega) (by rw [phaseStreamCount_2]; omega),
              BitVec.getLsbD_extractLsb', bandBStreamDword_getLsbD _ _ _ (by omega)]
            have henc : encTables 3 (8 * j + b) = streamBitToOldBit (704 + (8 * j + b - 12416)) := by
              unfold encTables
              rw [ite_neg (by omega), ite_neg (by decide), ite_neg (by omega), ite_neg (by omega),
                ite_neg (by decide), ite_neg (by omega), ite_neg (by omega), ite_pos rfl]
            rw [henc, oldBlock_bit_of_streamBitToOldBit 3 block clean _ (by omega)]
            simp only [hb, decide_true, Bool.true_and, phaseStreamStart_2]
            exact congrArg (bandBStreamBit block) (by omega)
        · rw [ite_neg h1600, List.getElem?_take_of_lt (by omega), wordBytes_getD _ _ (by omega),
            BitVec.getLsbD_extractLsb', bandBStreamDword_getLsbD _ _ _ (by omega)]
          have henc : encTables 3 (8 * j + b) = streamBitToOldBit (704 + (8 * j + b - 12416)) := by
            unfold encTables
            rw [ite_neg (by omega), ite_neg (by decide), ite_neg (by omega), ite_neg (by omega),
              ite_neg (by decide), ite_neg (by omega), ite_neg (by omega), ite_pos rfl]
          rw [henc, oldBlock_bit_of_streamBitToOldBit 3 block clean _ (by omega)]
          simp only [hb, decide_true, Bool.true_and]
          exact congrArg (bandBStreamBit block) (by omega)
  · -- r = 4
    unfold newBlockBytes newPartialFlush
    simp only [List.range_succ, List.range_zero, List.nil_append, List.flatMap_append,
      List.flatMap_singleton, List.append_assoc, List.append_nil,
      show ¬ (4 = 1) by decide, show ¬ (4 = 2) by decide, show ¬ (4 = 3) by decide,
      show ¬ (1 = 0) by decide, show ¬ (2 = 0) by decide,
      ite_false, ite_true, getElem_append_nat, newPhaseBytes_length]
    by_cases h528 : j < 528
    · rw [ite_pos h528]
      by_cases h488 : j < 488
      · rw [newPhaseBytes_getD_fixed 0 block j h488]
        have henc : encTables 4 (8 * j + b) = nonStreamToOldBit 0 (8 * j + b) := by
          unfold encTables; rw [ite_pos (by omega)]
        rw [henc, oldBlock_bit_of_nonStreamToOldBit 4 block clean 0 (by decide) j b h488 hb]
      · rw [newPhaseBytes_getD_stream 0 block j (by omega) (by rw [phaseStreamCount_0]; omega),
          BitVec.getLsbD_extractLsb', bandBStreamDword_getLsbD _ _ _ (by omega)]
        have henc : encTables 4 (8 * j + b) = streamBitToOldBit (8 * j + b - 3904) := by
          unfold encTables; rw [ite_neg (by omega), ite_neg (by decide), ite_pos (by omega)]
        rw [henc, oldBlock_bit_of_streamBitToOldBit 4 block clean _ (by omega)]
        simp only [hb, decide_true, Bool.true_and, phaseStreamStart_0, Nat.zero_add]
        exact congrArg (bandBStreamBit block) (by omega)
    · rw [ite_neg h528]
      by_cases h1064 : j - 528 < 536
      · rw [ite_pos h1064]
        by_cases h488 : j - 528 < 488
        · rw [newPhaseBytes_getD_fixed 1 block (j - 528) h488]
          have henc : encTables 4 (8 * j + b) = nonStreamToOldBit 1 (8 * (j - 528) + b) := by
            unfold encTables
            rw [ite_neg (by omega), ite_neg (by decide), ite_neg (by omega), ite_pos (by omega)]
            exact congrArg (nonStreamToOldBit 1) (by omega)
          rw [henc, oldBlock_bit_of_nonStreamToOldBit 4 block clean 1 (by decide) (j - 528) b h488 hb]
        · rw [newPhaseBytes_getD_stream 1 block (j - 528) (by omega) (by rw [phaseStreamCount_1]; omega),
            BitVec.getLsbD_extractLsb', bandBStreamDword_getLsbD _ _ _ (by omega)]
          have henc : encTables 4 (8 * j + b) = streamBitToOldBit (320 + (8 * j + b - 8128)) := by
            unfold encTables
            rw [ite_neg (by omega), ite_neg (by decide), ite_neg (by omega), ite_neg (by omega),
              ite_neg (by decide), ite_pos (by omega)]
          rw [henc, oldBlock_bit_of_streamBitToOldBit 4 block clean _ (by omega)]
          simp only [hb, decide_true, Bool.true_and, phaseStreamStart_1]
          exact congrArg (bandBStreamBit block) (by omega)
      · rw [ite_neg h1064]
        by_cases h1600 : j - 528 - 536 < 536
        · rw [ite_pos h1600]
          by_cases h488 : j - 528 - 536 < 488
          · rw [newPhaseBytes_getD_fixed 2 block (j - 528 - 536) h488]
            have henc : encTables 4 (8 * j + b) = nonStreamToOldBit 2 (8 * (j - 528 - 536) + b) := by
              unfold encTables
              rw [ite_neg (by omega), ite_neg (by decide), ite_neg (by omega), ite_neg (by omega),
                ite_neg (by decide), ite_neg (by omega), ite_pos (by omega)]
              exact congrArg (nonStreamToOldBit 2) (by omega)
            rw [henc, oldBlock_bit_of_nonStreamToOldBit 4 block clean 2 (by decide) (j - 528 - 536) b h488 hb]
          · rw [newPhaseBytes_getD_stream 2 block (j - 528 - 536) (by omega) (by rw [phaseStreamCount_2]; omega),
              BitVec.getLsbD_extractLsb', bandBStreamDword_getLsbD _ _ _ (by omega)]
            have henc : encTables 4 (8 * j + b) = streamBitToOldBit (704 + (8 * j + b - 12416)) := by
              unfold encTables
              rw [ite_neg (by omega), ite_neg (by decide), ite_neg (by omega), ite_neg (by omega),
                ite_neg (by decide), ite_neg (by omega), ite_neg (by omega), ite_neg (by decide),
                ite_pos (by omega)]
            rw [henc, oldBlock_bit_of_streamBitToOldBit 4 block clean _ (by omega)]
            simp only [hb, decide_true, Bool.true_and, phaseStreamStart_2]
            exact congrArg (bandBStreamBit block) (by omega)
        · rw [ite_neg h1600]
          by_cases h488 : j - 528 - 536 - 536 < 488
          · rw [newPhaseBytes_getD_fixed 3 block (j - 528 - 536 - 536) h488]
            have henc : encTables 4 (8 * j + b) = nonStreamToOldBit 3 (8 * (j - 528 - 536 - 536) + b) := by
              unfold encTables
              rw [ite_neg (by omega), ite_neg (by decide), ite_neg (by omega), ite_neg (by omega),
                ite_neg (by decide), ite_neg (by omega), ite_neg (by omega), ite_neg (by decide),
                ite_neg (by omega), ite_pos (by omega)]
              exact congrArg (nonStreamToOldBit 3) (by omega)
            rw [henc, oldBlock_bit_of_nonStreamToOldBit 4 block clean 3 (by decide) (j - 528 - 536 - 536) b h488 hb]
          · rw [newPhaseBytes_getD_stream 3 block (j - 528 - 536 - 536) (by omega) (by rw [phaseStreamCount_3]; omega),
              BitVec.getLsbD_extractLsb', bandBStreamDword_getLsbD _ _ _ (by omega)]
            have henc : encTables 4 (8 * j + b) = streamBitToOldBit (1088 + (8 * j + b - 16704)) := by
              unfold encTables
              rw [ite_neg (by omega), ite_neg (by decide), ite_neg (by omega), ite_neg (by omega),
                ite_neg (by decide), ite_neg (by omega), ite_neg (by omega), ite_neg (by decide),
                ite_neg (by omega), ite_neg (by omega)]
            rw [henc, oldBlock_bit_of_streamBitToOldBit 4 block clean _ (by omega)]
            simp only [hb, decide_true, Bool.true_and, phaseStreamStart_3]
            exact congrArg (bandBStreamBit block) (by omega)

/-- Block-level equivalence: applying `gather encTables r` to today's `r`-record block produces
`newBlockBytes r block` byte-for-byte. -/
theorem gather_enc_block (r : Nat) (lo : 1 ≤ r) (hi : r ≤ 4) (block : Nat → RecordFields)
    (clean : ∀ p < r, BandBClean (block p)) (j : Nat) (hj : j < 534 * r) :
    gather encTables r (fun b => (oldBlockBytes r block)[b]?.getD 0) j =
      (newBlockBytes r block)[j]?.getD 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  rw [gather_bit encTables r _ j b hb, newBlockBytes_getLsbD r lo hi block clean j b hj hb]

theorem convert_enc_block (r : Nat) (lo : 1 ≤ r) (hi : r ≤ 4) (block : Nat → RecordFields)
    (clean : ∀ p < r, BandBClean (block p)) :
    (List.ofFn fun j : Fin (534 * r) =>
      gather encTables r (fun b => (oldBlockBytes r block)[b]?.getD 0) j.val) =
    newBlockBytes r block := by
  apply List.ext_getElem
  · simp [newBlockBytes_length r lo hi block]
  · intro j h1 h2
    have hj : j < 534 * r := by simpa using h1
    simp only [List.getElem_ofFn]
    rw [gather_enc_block r lo hi block clean j hj, List.getElem?_eq_getElem h2]
    rfl

private theorem newFullBlocks_getD (n : Nat) (recs : Nat → RecordFields) (j : Nat)
    (hj : j < 2136 * n) :
    (((List.range n).flatMap fun g => newBlockBytes 4 (fun p => recs (4 * g + p)))[j]?.getD 0) =
      (newBlockBytes 4 (fun p => recs (4 * (j / 2136) + p)))[j % 2136]?.getD 0 := by
  induction n generalizing j with
  | zero => omega
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, getElem_append_nat]
    have hlen : ((List.range m).flatMap fun g => newBlockBytes 4 (fun p => recs (4 * g + p))).length = 2136 * m := by
      rw [List.length_flatMap,
        List.map_congr_left (fun _ _ => newBlockBytes_length 4 (by decide) (by decide) _)]
      simp [Nat.mul_comm]
    rw [hlen]
    by_cases h : j < 2136 * m
    · rw [ite_pos h]; exact ih j h
    · rw [ite_neg h]
      have hdiv : j / 2136 = m := by omega
      have hmod : j % 2136 = j - 2136 * m := by omega
      rw [hdiv, hmod]

/-- Whole-proof opener theorem: `convert encTables k` of today's proof bytes (`k` records + cap)
equals `newProofBytes k recs cap` (the exact phased record layout + unchanged cap bytes). -/
theorem convert_enc_oldProofBytes (k : Nat) (recs : Nat → RecordFields) (cap : Proof)
    (clean : ∀ i < k, BandBClean (recs i)) :
    convert encTables k (oldProofBytes k recs cap) = newProofBytes k recs cap := by
  apply List.ext_getElem
  · rw [convert_length, newProofBytes_length]
  · intro j h1 h2
    have hlen : j < 534 * k + cap.length := by simpa [oldProofBytes_length] using h1
    simp only [convert, List.getElem_ofFn]
    have hfullLen : ((List.range (k / 4)).flatMap fun g => newBlockBytes 4 (fun p => recs (4 * g + p))).length =
        2136 * (k / 4) := by
      rw [List.length_flatMap,
        List.map_congr_left (fun _ _ => newBlockBytes_length 4 (by decide) (by decide) _)]
      simp [Nat.mul_comm]
    have htailLen : (if k % 4 = 0 then [] else newBlockBytes (k % 4) (fun p => recs (4 * (k / 4) + p))).length =
        534 * (k % 4) := by
      split_ifs with h
      · simp [h]
      · exact newBlockBytes_length (k % 4) (by omega) (by omega) _
    by_cases hrec : j < 534 * k
    · let g := j / 2136
      let r := blockSize k g
      let b := j % 2136
      have hlim : g ≤ k / 4 := by dsimp [g]; omega
      have hrange : 1 ≤ r ∧ r ≤ 4 ∧ b < 534 * r ∧ 2136 * g + 534 * r ≤ 534 * k := by
        dsimp only [r, blockSize, g, b]; split_ifs <;> omega
      have hatJ : 2136 * g + b = j := by dsimp [g, b]; omega
      have hblk := at_block encTables k g r b (fun n => (oldProofBytes k recs cap)[n]?.getD 0)
        hrange.2.2.1 hlim rfl
      rw [hatJ] at hblk
      rw [hblk]
      have hagree : ∀ q < 534 * r,
          (oldProofBytes k recs cap)[2136 * g + q]?.getD 0 =
            (oldBlockBytes r (fun p => recs (4 * g + p)))[q]?.getD 0 := by
        intro q hq
        unfold oldProofBytes
        rw [getElem_append_nat, oldBlockBytes_length, ite_pos (by omega),
          oldBlockBytes_getD k recs (2136 * g + q) (by omega),
          oldBlockBytes_getD r (fun p => recs (4 * g + p)) q hq]
        have hdiv : (2136 * g + q) / 534 = 4 * g + q / 534 := by omega
        have hmod : (2136 * g + q) % 534 = q % 534 := by omega
        rw [hdiv, hmod]
      rw [gather_congr enc_wellFormed hrange.1 hrange.2.1 hrange.2.2.1 hagree]
      rw [gather_enc_block r hrange.1 hrange.2.1 (fun p => recs (4 * g + p))
        (fun p hp => clean (4 * g + p) (by dsimp only [r, blockSize, g] at hp; split_ifs at hp <;> omega))
        b hrange.2.2.1]
      have hrhs : (newProofBytes k recs cap)[j] = (newProofBytes k recs cap)[j]?.getD 0 := by
        rw [List.getElem?_eq_getElem h2]; rfl
      rw [hrhs]
      unfold newProofBytes
      rw [getElem_append_nat, List.length_append, hfullLen, htailLen, ite_pos (by omega),
        getElem_append_nat, hfullLen]
      by_cases hfull : j < 2136 * (k / 4)
      · rw [ite_pos hfull, newFullBlocks_getD (k / 4) recs j hfull]
        have hr4 : r = 4 := by dsimp only [r, blockSize, g]; rw [ite_pos (by omega)]
        rw [hr4]
      · rw [ite_neg hfull]
        have hne : k % 4 ≠ 0 := by omega
        rw [ite_neg hne]
        have hg_eq : g = k / 4 := by dsimp [g]; omega
        have hr_eq : r = k % 4 := by dsimp only [r, blockSize]; rw [hg_eq, ite_neg (by omega)]
        have hb_eq : b = j - 2136 * (k / 4) := by dsimp [b]; omega
        rw [hg_eq, hr_eq, hb_eq]
    · rw [convertAt, ite_neg hrec]
      have hrhs : (newProofBytes k recs cap)[j] = (newProofBytes k recs cap)[j]?.getD 0 := by
        rw [List.getElem?_eq_getElem h2]; rfl
      rw [hrhs]
      unfold newProofBytes oldProofBytes
      rw [getElem_append_nat (oldBlockBytes k recs) cap, oldBlockBytes_length, ite_neg hrec,
        getElem_append_nat _ cap, List.length_append, hfullLen, htailLen, ite_neg (by omega)]
      congr 2; omega

/-- Cap bytes `[534 * k .. len)` are byte-for-byte unchanged by `convert encTables k`. -/
theorem convert_enc_cap_suffix (k : Nat) (p : Proof) (complete : 534 * k ≤ p.length) :
    (convert encTables k p).drop (534 * k) = p.drop (534 * k) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_drop, convert, List.getElem_ofFn, convertAt]
    rw [ite_neg (by omega)]
    have hlt : 534 * k + i < p.length := by simp at h2; omega
    simp [hlt]

/-! ### 5. Explicit Field-by-Field Slice & Word Readback (Offsets as Numerals) -/

private theorem take_append_exact {α : Type} (xs ys : List α) (n : Nat) (h : xs.length = n) :
    (xs ++ ys).take n = xs := by
  rw [← h, List.take_left]

private theorem drop_append_of_le {α : Type} (xs ys : List α) (k : Nat) (h : xs.length ≤ k) :
    (xs ++ ys).drop k = ys.drop (k - xs.length) := by
  rw [List.drop_append, List.drop_eq_nil_of_le h, List.nil_append]

/-- Exact byte slice of each field inside `newPhaseFixedBytes f` (all offsets as numerals). -/
theorem newPhaseFixedBytes_salt (f : RecordFields) :
    (newPhaseFixedBytes f).take 16 = leBytes (n := 16) f.salt := by
  unfold newPhaseFixedBytes
  simp only [List.append_assoc]
  exact take_append_exact _ _ 16 (leBytes_length _)

theorem newPhaseFixedBytes_mate0 (f : RecordFields) :
    ((newPhaseFixedBytes f).drop 16).take 32 = leBytes (n := 32) (f.mate 0) := by
  unfold newPhaseFixedBytes
  simp only [List.append_assoc, drop_append_of_le, leBytes_length, Nat.le_refl, Nat.sub_self, List.drop_zero]
  exact take_append_exact _ _ 32 (leBytes_length _)

theorem newPhaseFixedBytes_mate1 (f : RecordFields) :
    ((newPhaseFixedBytes f).drop 48).take 32 = leBytes (n := 32) (f.mate 1) := by
  unfold newPhaseFixedBytes
  simp only [List.append_assoc, drop_append_of_le, leBytes_length, show 16 ≤ 48 by decide,
    show 32 ≤ 48 - 16 by decide, show 48 - 16 - 32 = 0 by decide, List.drop_zero]
  exact take_append_exact _ _ 32 (leBytes_length _)

theorem newPhaseFixedBytes_mate2 (f : RecordFields) :
    ((newPhaseFixedBytes f).drop 80).take 32 = leBytes (n := 32) (f.mate 2) := by
  unfold newPhaseFixedBytes
  simp only [List.append_assoc, drop_append_of_le, leBytes_length, show 16 ≤ 80 by decide,
    show 32 ≤ 80 - 16 by decide, show 32 ≤ 80 - 16 - 32 by decide,
    show 80 - 16 - 32 - 32 = 0 by decide, List.drop_zero]
  exact take_append_exact _ _ 32 (leBytes_length _)

theorem newPhaseFixedBytes_sib0 (f : RecordFields) :
    ((newPhaseFixedBytes f).drop 112).take 32 = leBytes (n := 32) f.sib0 := by
  unfold newPhaseFixedBytes
  simp only [List.append_assoc, drop_append_of_le, leBytes_length, show 16 ≤ 112 by decide,
    show 32 ≤ 112 - 16 by decide, show 32 ≤ 112 - 16 - 32 by decide,
    show 32 ≤ 112 - 16 - 32 - 32 by decide, show 112 - 16 - 32 - 32 - 32 = 0 by decide, List.drop_zero]
  exact take_append_exact _ _ 32 (leBytes_length _)

theorem newPhaseFixedBytes_sib1 (f : RecordFields) :
    ((newPhaseFixedBytes f).drop 144).take 32 = leBytes (n := 32) f.sib1 := by
  unfold newPhaseFixedBytes
  simp only [List.append_assoc, drop_append_of_le, leBytes_length, show 16 ≤ 144 by decide,
    show 32 ≤ 144 - 16 by decide, show 32 ≤ 144 - 16 - 32 by decide,
    show 32 ≤ 144 - 16 - 32 - 32 by decide, show 32 ≤ 144 - 16 - 32 - 32 - 32 by decide,
    show 144 - 16 - 32 - 32 - 32 - 32 = 0 by decide, List.drop_zero]
  exact take_append_exact _ _ 32 (leBytes_length _)

private theorem newPhaseFixedBytes_slice_eq (f : RecordFields) (off len : Nat) (xs : Proof)
    (hlen : xs.length = len) (hfit : off + len ≤ 488)
    (hbyte : ∀ i < len, ((newPhaseFixedBytes f)[off + i]?.getD 0) = xs[i]?.getD 0) :
    ((newPhaseFixedBytes f).drop off).take len = xs := by
  apply List.ext_getElem
  · simp [newPhaseFixedBytes_length, hlen]; omega
  · intro i h1 h2
    have hi : i < len := by simpa [hlen] using h2
    have hlt : off + i < (newPhaseFixedBytes f).length := by rw [newPhaseFixedBytes_length]; omega
    simp only [List.getElem_take, List.getElem_drop]
    have hb := hbyte i hi
    rw [List.getElem?_eq_getElem hlt, List.getElem?_eq_getElem h2] at hb
    simpa using hb

theorem newPhaseFixedBytes_bandA0 (f : RecordFields) :
    ((newPhaseFixedBytes f).drop 176).take 24 = leBytes (n := 24) ((f.bandA 0).extractLsb' 0 192) := by
  apply newPhaseFixedBytes_slice_eq f 176 24 _ (leBytes_length _) (by decide)
  intro i hi
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  rw [newPhaseFixedBytes_getLsbD f (176 + i) b (by omega) hb, leBytes_getD _ i hi,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb']
  simp [hb, show ¬ (8 * (176 + i) + b < 128) by omega, show ¬ (8 * (176 + i) + b < 384) by omega,
    show ¬ (8 * (176 + i) + b < 640) by omega, show ¬ (8 * (176 + i) + b < 896) by omega,
    show ¬ (8 * (176 + i) + b < 1152) by omega, show ¬ (8 * (176 + i) + b < 1408) by omega,
    show 8 * (176 + i) + b < 2176 by omega, show (8 * (176 + i) + b - 1408) / 192 = 0 by omega,
    show (8 * (176 + i) + b - 1408) % 192 = 8 * i + b by omega, show 8 * i + b < 192 by omega]

theorem newPhaseFixedBytes_bandA1 (f : RecordFields) :
    ((newPhaseFixedBytes f).drop 200).take 24 = leBytes (n := 24) ((f.bandA 1).extractLsb' 0 192) := by
  apply newPhaseFixedBytes_slice_eq f 200 24 _ (leBytes_length _) (by decide)
  intro i hi
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  rw [newPhaseFixedBytes_getLsbD f (200 + i) b (by omega) hb, leBytes_getD _ i hi,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb']
  simp [hb, show ¬ (8 * (200 + i) + b < 128) by omega, show ¬ (8 * (200 + i) + b < 384) by omega,
    show ¬ (8 * (200 + i) + b < 640) by omega, show ¬ (8 * (200 + i) + b < 896) by omega,
    show ¬ (8 * (200 + i) + b < 1152) by omega, show ¬ (8 * (200 + i) + b < 1408) by omega,
    show 8 * (200 + i) + b < 2176 by omega, show (8 * (200 + i) + b - 1408) / 192 = 1 by omega,
    show (8 * (200 + i) + b - 1408) % 192 = 8 * i + b by omega, show 8 * i + b < 192 by omega]

theorem newPhaseFixedBytes_bandA2 (f : RecordFields) :
    ((newPhaseFixedBytes f).drop 224).take 24 = leBytes (n := 24) ((f.bandA 2).extractLsb' 0 192) := by
  apply newPhaseFixedBytes_slice_eq f 224 24 _ (leBytes_length _) (by decide)
  intro i hi
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  rw [newPhaseFixedBytes_getLsbD f (224 + i) b (by omega) hb, leBytes_getD _ i hi,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb']
  simp [hb, show ¬ (8 * (224 + i) + b < 128) by omega, show ¬ (8 * (224 + i) + b < 384) by omega,
    show ¬ (8 * (224 + i) + b < 640) by omega, show ¬ (8 * (224 + i) + b < 896) by omega,
    show ¬ (8 * (224 + i) + b < 1152) by omega, show ¬ (8 * (224 + i) + b < 1408) by omega,
    show 8 * (224 + i) + b < 2176 by omega, show (8 * (224 + i) + b - 1408) / 192 = 2 by omega,
    show (8 * (224 + i) + b - 1408) % 192 = 8 * i + b by omega, show 8 * i + b < 192 by omega]

theorem newPhaseFixedBytes_bandA3 (f : RecordFields) :
    ((newPhaseFixedBytes f).drop 248).take 24 = leBytes (n := 24) ((f.bandA 3).extractLsb' 0 192) := by
  apply newPhaseFixedBytes_slice_eq f 248 24 _ (leBytes_length _) (by decide)
  intro i hi
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  rw [newPhaseFixedBytes_getLsbD f (248 + i) b (by omega) hb, leBytes_getD _ i hi,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb']
  simp [hb, show ¬ (8 * (248 + i) + b < 128) by omega, show ¬ (8 * (248 + i) + b < 384) by omega,
    show ¬ (8 * (248 + i) + b < 640) by omega, show ¬ (8 * (248 + i) + b < 896) by omega,
    show ¬ (8 * (248 + i) + b < 1152) by omega, show ¬ (8 * (248 + i) + b < 1408) by omega,
    show 8 * (248 + i) + b < 2176 by omega, show (8 * (248 + i) + b - 1408) / 192 = 3 by omega,
    show (8 * (248 + i) + b - 1408) % 192 = 8 * i + b by omega, show 8 * i + b < 192 by omega]

theorem newPhaseFixedBytes_bandATail0 (f : RecordFields) :
    ((newPhaseFixedBytes f).drop 272).take 8 = wordBytes (bandATailWord f 0) := by
  apply newPhaseFixedBytes_slice_eq f 272 8 _ (wordBytes_length _) (by decide)
  intro i hi
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  rw [newPhaseFixedBytes_getLsbD f (272 + i) b (by omega) hb, wordBytes_getD _ i hi,
    BitVec.getLsbD_extractLsb', bandATailWord_getLsbD f 0 (8 * i + b) (by omega)]
  simp [hb, show ¬ (8 * (272 + i) + b < 128) by omega, show ¬ (8 * (272 + i) + b < 384) by omega,
    show ¬ (8 * (272 + i) + b < 640) by omega, show ¬ (8 * (272 + i) + b < 896) by omega,
    show ¬ (8 * (272 + i) + b < 1152) by omega, show ¬ (8 * (272 + i) + b < 1408) by omega,
    show ¬ (8 * (272 + i) + b < 2176) by omega, show 8 * (272 + i) + b < 2368 by omega,
    show 8 * (272 + i) + b - 2176 = 8 * i + b by omega, show (8 * i + b) / 48 < 4 by omega]

theorem newPhaseFixedBytes_bandATail1 (f : RecordFields) :
    ((newPhaseFixedBytes f).drop 280).take 8 = wordBytes (bandATailWord f 1) := by
  apply newPhaseFixedBytes_slice_eq f 280 8 _ (wordBytes_length _) (by decide)
  intro i hi
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  rw [newPhaseFixedBytes_getLsbD f (280 + i) b (by omega) hb, wordBytes_getD _ i hi,
    BitVec.getLsbD_extractLsb', bandATailWord_getLsbD f 1 (8 * i + b) (by omega)]
  simp [hb, show ¬ (8 * (280 + i) + b < 128) by omega, show ¬ (8 * (280 + i) + b < 384) by omega,
    show ¬ (8 * (280 + i) + b < 640) by omega, show ¬ (8 * (280 + i) + b < 896) by omega,
    show ¬ (8 * (280 + i) + b < 1152) by omega, show ¬ (8 * (280 + i) + b < 1408) by omega,
    show ¬ (8 * (280 + i) + b < 2176) by omega, show 8 * (280 + i) + b < 2368 by omega,
    show 8 * (280 + i) + b - 2176 = 64 + (8 * i + b) by omega, show (64 + (8 * i + b)) / 48 < 4 by omega]

theorem newPhaseFixedBytes_bandATail2 (f : RecordFields) :
    ((newPhaseFixedBytes f).drop 288).take 8 = wordBytes (bandATailWord f 2) := by
  apply newPhaseFixedBytes_slice_eq f 288 8 _ (wordBytes_length _) (by decide)
  intro i hi
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  rw [newPhaseFixedBytes_getLsbD f (288 + i) b (by omega) hb, wordBytes_getD _ i hi,
    BitVec.getLsbD_extractLsb', bandATailWord_getLsbD f 2 (8 * i + b) (by omega)]
  simp [hb, show ¬ (8 * (288 + i) + b < 128) by omega, show ¬ (8 * (288 + i) + b < 384) by omega,
    show ¬ (8 * (288 + i) + b < 640) by omega, show ¬ (8 * (288 + i) + b < 896) by omega,
    show ¬ (8 * (288 + i) + b < 1152) by omega, show ¬ (8 * (288 + i) + b < 1408) by omega,
    show ¬ (8 * (288 + i) + b < 2176) by omega, show 8 * (288 + i) + b < 2368 by omega,
    show 8 * (288 + i) + b - 2176 = 128 + (8 * i + b) by omega, show (128 + (8 * i + b)) / 48 < 4 by omega]

theorem newPhaseFixedBytes_bandB_body (f : RecordFields) (j : Fin 8) :
    ((newPhaseFixedBytes f).drop (296 + 24 * j.val)).take 24 =
      leBytes (n := 24) ((f.bandB j).extractLsb' 0 192) := by
  apply newPhaseFixedBytes_slice_eq f (296 + 24 * j.val) 24 _ (leBytes_length _) (by omega)
  intro i hi
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  rw [newPhaseFixedBytes_getLsbD f (296 + 24 * j.val + i) b (by omega) hb, leBytes_getD _ i hi,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb']
  have hj8 : j.val < 8 := j.isLt
  simp [hb, show ¬ (8 * (296 + 24 * j.val + i) + b < 128) by omega,
    show ¬ (8 * (296 + 24 * j.val + i) + b < 384) by omega,
    show ¬ (8 * (296 + 24 * j.val + i) + b < 640) by omega,
    show ¬ (8 * (296 + 24 * j.val + i) + b < 896) by omega,
    show ¬ (8 * (296 + 24 * j.val + i) + b < 1152) by omega,
    show ¬ (8 * (296 + 24 * j.val + i) + b < 1408) by omega,
    show ¬ (8 * (296 + 24 * j.val + i) + b < 2176) by omega,
    show ¬ (8 * (296 + 24 * j.val + i) + b < 2368) by omega,
    show (8 * (296 + 24 * j.val + i) + b - 2368) / 192 = j.val by omega,
    show (8 * (296 + 24 * j.val + i) + b - 2368) % 192 = 8 * i + b by omega,
    show 8 * i + b < 192 by omega, hj8]

/-- Exact stream dword slice at offset `488 + 8 * d` inside `newPhaseBytes p block`. -/
theorem newPhaseBytes_stream_dword (p : Nat) (block : Nat → RecordFields) (d : Nat)
    (hd : d < phaseStreamCount p) :
    ((newPhaseBytes p block).drop (488 + 8 * d)).take 8 =
      wordBytes (bandBStreamDword block (phaseStreamStart p + d)) := by
  apply List.ext_getElem
  · have hlen : (newPhaseBytes p block).length = 488 + 8 * phaseStreamCount p := by
      rw [newPhaseBytes_length]; unfold phaseStreamCount; split_ifs <;> omega
    simp [hlen]; omega
  · intro i h1 h2
    have hi : i < 8 := by simpa using h2
    simp only [List.getElem_take, List.getElem_drop]
    have hhi : 488 + 8 * d + i < 488 + 8 * phaseStreamCount p := by omega
    have hlt : 488 + 8 * d + i < (newPhaseBytes p block).length := by
      rw [newPhaseBytes_length]; unfold phaseStreamCount at hhi; split_ifs at hhi ⊢ <;> omega
    have h := newPhaseBytes_getD_stream p block (488 + 8 * d + i) (by omega) hhi
    rw [List.getElem?_eq_getElem hlt] at h
    dsimp only [Option.getD] at h
    rw [h, show (488 + 8 * d + i - 488) / 8 = d by omega,
      show (488 + 8 * d + i - 488) % 8 = i by omega]
    have w := wordBytes_getD (bandBStreamDword block (phaseStreamStart p + d)) i hi
    rw [List.getElem?_eq_getElem h2, Option.getD_some] at w
    exact w.symm

/-! ### 6. Proposed M3 Cut: 3-Branch RV64 Band-B Carry-Register State Machine -/

/-- Exact value of the RV64 Band-B carry register `a1` after packing `n` 46-bit Band-B tails
(`0 ≤ n ≤ 32`): holds bits `64 * ((46 * n) / 64) .. 46 * n - 1` of the stream, zero-extended
to 64 bits (width `c = (46 * n) % 64`). -/
def streamCarry (block : Nat → RecordFields) (n : Nat) : Word :=
  wordOfBits fun b =>
    if b < (46 * n) % 64 then
      bandBStreamBit block (64 * ((46 * n) / 64) + b)
    else false

/-- The `n`-th 46-bit Band-B tail (`0 ≤ n < 32`, record `n / 8`, sibling `n % 8`), zero-extended
to 64 bits. -/
def bandBTailWord46 (block : Nat → RecordFields) (n : Nat) : Word :=
  ((block (n / 8)).bandB ⟨n % 8, Nat.mod_lt _ (by decide)⟩ |>.extractLsb' 192 46).zeroExtend 64

/-- When bits `238..255` of a 256-bit digest are zero (`upper_heap_high`), loading its top 64-bit
dword (`ld t6, 24(t2)`) directly equals the zero-extended 46-bit tail without masking! -/
theorem tail46_eq_word64 (v : BitVec 256) (clean : v.extractLsb' 238 18 = 0) :
    (v.extractLsb' 192 46).zeroExtend 64 = v.extractLsb' 192 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb']
  by_cases h46 : i < 46
  · simp [hi, h46]
  · simp only [hi, h46, decide_false, Bool.false_and, decide_true, Bool.true_and]
    have hbit := congrArg (fun w : BitVec 18 => w.getLsbD (i - 46)) clean
    have hz : (0 : BitVec 18).getLsbD (i - 46) = false := by simp
    rw [BitVec.getLsbD_extractLsb', hz] at hbit
    simp only [show i - 46 < 18 by omega, decide_true, Bool.true_and,
      show 238 + (i - 46) = 192 + i by omega] at hbit
    exact hbit.symm

theorem streamCarry_zero (block : Nat → RecordFields) : streamCarry block 0 = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [streamCarry, wordOfBits_getLsbD _ i hi]

/-- Phase 0's first Band-B tail overwrites `a1` directly (`ld a1, 24(t2)`), ignoring any incoming
physical `a1` value and establishing `streamCarry block 1`. -/
theorem streamCarry_one (block : Nat → RecordFields) :
    bandBTailWord46 block 0 = streamCarry block 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  unfold bandBTailWord46 streamCarry
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', wordOfBits_getLsbD _ i hi]
  by_cases h46 : i < 46
  · simp [hi, h46, bandBStreamBit, show i / 368 = 0 by omega, show i % 368 = i by omega,
      show i / 46 = 0 by omega, show i % 46 = i by omega]
  · simp [hi, h46]

private theorem bandBTailWord46_getLsbD (block : Nat → RecordFields) (n i : Nat) (hi : i < 64) :
    (bandBTailWord46 block n).getLsbD i =
      if i < 46 then bandBStreamBit block (46 * n + i) else false := by
  unfold bandBTailWord46 bandBStreamBit
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb']
  by_cases h46 : i < 46
  · simp [hi, h46, show (46 * n + i) / 368 = n / 8 by omega,
      show (46 * n + i) % 368 / 46 = n % 8 by omega,
      show (46 * n + i) % 368 % 46 = i by omega, Nat.mod_lt n (by decide : 0 < 8)]
  · simp [hi, h46]

/-- Carry step when `(46 * n) % 64 + 46 < 64` (no dword emitted: `a1 := a1 ||| (t6 <<< c)`). -/
theorem streamCarry_step_lt (block : Nat → RecordFields) (n : Nat)
    (hlt : (46 * n) % 64 + 46 < 64) :
    streamCarry block n ||| (bandBTailWord46 block n <<< ((46 * n) % 64)) =
      streamCarry block (n + 1) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  set c := (46 * n) % 64
  set dw := (46 * n) / 64
  have hdw1 : (46 * (n + 1)) / 64 = dw := by dsimp [dw, c] at hlt ⊢; omega
  have hc1 : (46 * (n + 1)) % 64 = c + 46 := by dsimp [c] at hlt ⊢; omega
  rw [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  unfold streamCarry
  rw [wordOfBits_getLsbD _ i hi, wordOfBits_getLsbD _ i hi]
  simp only [hdw1, hc1]
  by_cases h1 : i < c
  · have h1' : i < 46 * n % 64 := h1
    simp only [h1, h1', hi, ite_true, decide_true, Bool.not_true, Bool.and_false, Bool.false_and,
      Bool.or_false, show i < c + 46 by omega]
    rfl
  · have h1' : ¬ (i < 46 * n % 64) := h1
    simp only [h1, h1', hi, ite_false, decide_true, decide_false, Bool.not_false, Bool.true_and,
      Bool.false_or]
    rw [bandBTailWord46_getLsbD block n (i - c) (by omega)]
    by_cases h2 : i < c + 46
    · rw [ite_pos (by omega), ite_pos h2]
      exact congrArg (bandBStreamBit block) (by dsimp [dw, c]; omega)
    · rw [ite_neg (by omega), ite_neg h2]

/-- Carry step when `(46 * n) % 64 + 46 = 64` (emits `bandBStreamDword block dw`, resets logical
carry to `0`). Note: at `n = 31` (end of phase 3), the emitted dword is `bandBStreamDword block 22`
and the subsequent phase 0 overwrites `a1` via `streamCarry_one`. -/
theorem streamCarry_step_eq (block : Nat → RecordFields) (n : Nat)
    (heq : (46 * n) % 64 + 46 = 64) :
    (streamCarry block n ||| (bandBTailWord46 block n <<< ((46 * n) % 64)) =
      bandBStreamDword block ((46 * n) / 64)) ∧
    streamCarry block (n + 1) = 0 := by
  set c := (46 * n) % 64
  set dw := (46 * n) / 64
  constructor
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, bandBStreamDword_getLsbD _ _ _ hi]
    unfold streamCarry
    rw [wordOfBits_getLsbD _ i hi]
    by_cases h1 : i < c
    · have h1' : i < 46 * n % 64 := h1
      simp only [h1, h1', hi, ite_true, decide_true, Bool.not_true, Bool.and_false, Bool.false_and,
        Bool.or_false]
      rfl
    · have h1' : ¬ (i < 46 * n % 64) := h1
      simp only [h1, h1', hi, ite_false, decide_true, decide_false, Bool.not_false, Bool.true_and,
        Bool.false_or]
      rw [bandBTailWord46_getLsbD block n (i - c) (by omega), ite_pos (by omega)]
      exact congrArg (bandBStreamBit block) (by dsimp [dw, c]; omega)
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hc1 : (46 * (n + 1)) % 64 = 0 := by dsimp [c] at heq; omega
    unfold streamCarry
    rw [wordOfBits_getLsbD _ i hi]
    simp [hc1]

/-- Carry step when `(46 * n) % 64 + 46 > 64` (emits `bandBStreamDword block dw`, new carry is
`t6 >>> (64 - c)`). -/
theorem streamCarry_step_gt (block : Nat → RecordFields) (n : Nat)
    (hgt : 64 < (46 * n) % 64 + 46) :
    (streamCarry block n ||| (bandBTailWord46 block n <<< ((46 * n) % 64)) =
      bandBStreamDword block ((46 * n) / 64)) ∧
    (bandBTailWord46 block n >>> (64 - (46 * n) % 64) = streamCarry block (n + 1)) := by
  set c := (46 * n) % 64
  set dw := (46 * n) / 64
  have hc_lt : c < 64 := Nat.mod_lt _ (by decide)
  have hdw1 : (46 * (n + 1)) / 64 = dw + 1 := by dsimp [dw, c] at hgt ⊢; omega
  have hc1 : (46 * (n + 1)) % 64 = c + 46 - 64 := by dsimp [c] at hgt ⊢; omega
  constructor
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, bandBStreamDword_getLsbD _ _ _ hi]
    unfold streamCarry
    rw [wordOfBits_getLsbD _ i hi]
    by_cases h1 : i < c
    · have h1' : i < 46 * n % 64 := h1
      simp only [h1, h1', hi, ite_true, decide_true, Bool.not_true, Bool.and_false, Bool.false_and,
        Bool.or_false]
      rfl
    · have h1' : ¬ (i < 46 * n % 64) := h1
      simp only [h1, h1', hi, ite_false, decide_true, decide_false, Bool.not_false, Bool.true_and,
        Bool.false_or]
      rw [bandBTailWord46_getLsbD block n (i - c) (by omega), ite_pos (by omega)]
      exact congrArg (bandBStreamBit block) (by dsimp [dw, c]; omega)
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_ushiftRight]
    unfold streamCarry
    rw [wordOfBits_getLsbD _ i hi]
    simp only [hdw1, hc1]
    by_cases h1 : i < c + 46 - 64
    · rw [ite_pos h1, bandBTailWord46_getLsbD block n (64 - c + i) (by omega), ite_pos (by omega)]
      exact congrArg (bandBStreamBit block) (by dsimp [dw, c]; omega)
    · rw [ite_neg h1]
      by_cases h64 : 64 - c + i < 64
      · rw [bandBTailWord46_getLsbD block n (64 - c + i) h64, ite_neg (by omega)]
      · exact BitVec.getLsbD_of_ge _ _ (by omega)

/-- Partial-block exit flush for `r = 1` (`6` bytes at offset `528` from `streamCarry block 8`). -/
theorem streamCarry_flush_r1 (block : Nat → RecordFields) :
    (wordBytes (streamCarry block 8)).take 6 = newPartialFlush 1 block := by
  unfold newPartialFlush
  rw [ite_pos rfl]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  have hi : i < 6 := by simp at h1; omega
  simp only [List.getElem_take, wordBytes, leBytes, List.getElem_ofFn]
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb',
    bandBStreamDword_getLsbD _ _ _ (by omega)]
  unfold streamCarry
  rw [wordOfBits_getLsbD _ (8 * i + b) (by omega)]
  simp [hb, show 8 * i + b < 48 by omega]

/-- Partial-block exit flush for `r = 2` (`4` bytes at offset `1064` from `streamCarry block 16`). -/
theorem streamCarry_flush_r2 (block : Nat → RecordFields) :
    (wordBytes (streamCarry block 16)).take 4 = newPartialFlush 2 block := by
  unfold newPartialFlush
  rw [ite_neg (by decide), ite_pos rfl]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  have hi : i < 4 := by simp at h1; omega
  simp only [List.getElem_take, wordBytes, leBytes, List.getElem_ofFn]
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb',
    bandBStreamDword_getLsbD _ _ _ (by omega)]
  unfold streamCarry
  rw [wordOfBits_getLsbD _ (8 * i + b) (by omega)]
  simp [hb, show 8 * i + b < 32 by omega]

/-- Partial-block exit flush for `r = 3` (`2` bytes at offset `1600` from `streamCarry block 24`). -/
theorem streamCarry_flush_r3 (block : Nat → RecordFields) :
    (wordBytes (streamCarry block 24)).take 2 = newPartialFlush 3 block := by
  unfold newPartialFlush
  rw [ite_neg (by decide), ite_neg (by decide), ite_pos rfl]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  have hi : i < 2 := by simp at h1; omega
  simp only [List.getElem_take, wordBytes, leBytes, List.getElem_ofFn]
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb',
    bandBStreamDword_getLsbD _ _ _ (by omega)]
  unfold streamCarry
  rw [wordOfBits_getLsbD _ (8 * i + b) (by omega)]
  simp [hb, show 8 * i + b < 16 by omega]

end CommitGolfCandidate.Layout2
