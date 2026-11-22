import CommitGolfCandidate.Layout2Phase

/-! Layout 2 opener, byte level of the phase writer's output: the bytes of a `dwordOf` dword, a word from its
bytes, and `writerByte` by region of the block (straight copies of source bytes, the band-A tail words, the
stream dwords). Pure; imports only the shared phase module. -/
namespace TwoPermutationPrototype.GroupedOpening.Layout2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open CommitGolfCandidate.Layout2Phase (dwordOf writerDwords writerByte bandATails streamRun tailA tailB)
set_option maxRecDepth 16000

theorem ext_append_hi {m n : Nat} (x : BitVec n) (y : BitVec m) (o w : Nat) (h : m ≤ o) :
    (x ++ y).extractLsb' o w=x.extractLsb' (o-m) w := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  have a : ¬ o+j<m := by omega
  simp [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hj, a, show o+j-m=o-m+j by omega]

theorem ext_append_lo {m n : Nat} (x : BitVec n) (y : BitVec m) (o w : Nat) (h : o+w ≤ m) :
    (x ++ y).extractLsb' o w=y.extractLsb' o w := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  have a : o+j<m := by omega
  simp [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hj, a]

theorem ext_full (y : Byte) : y.extractLsb' 0 8=y := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [BitVec.getLsbD_extractLsb', hj]

theorem ext_ext {w : Nat} (v : BitVec w) (o n i m : Nat) (h : i+m ≤ n) :
    (v.extractLsb' o n).extractLsb' i m=v.extractLsb' (o+i) m := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [BitVec.getLsbD_extractLsb', hj, show i+j<n by omega, Nat.add_assoc]

/-- Byte `i` of a source dword is source byte `k+i`. -/
theorem dword_byte (src : Nat → Byte) (k i : Nat) (hi : i<8) :
    (dwordOf src k).extractLsb' (8*i) 8=src (k+i) := by
  unfold dwordOf
  interval_cases i <;> simp (disch := decide) only [ext_append_hi, ext_append_lo, ext_full, Nat.mul_zero,
    Nat.add_zero, Nat.reduceMul, Nat.reduceSub]

/-- A word is determined by its eight bytes. -/
theorem word_ext (x y : Word) (h : ∀ i<8, x.extractLsb' (8*i) 8=y.extractLsb' (8*i) 8) : x=y := by
  apply BitVec.eq_of_getLsbD_eq; intro n hn
  have e := congrArg (fun v : Byte => v.getLsbD (n%8)) (h (n/8) (by omega))
  simp only [BitVec.getLsbD_extractLsb', show n%8<8 by omega, decide_true, Bool.true_and,
    show 8*(n/8)+n%8=n by omega] at e
  exact e

/-- A source dword whose bytes are consecutive bytes of `v`. -/
theorem dword_slice {w : Nat} (src : Nat → Byte) (v : BitVec w) (k o : Nat)
    (h : ∀ i<8, src (k+i)=v.extractLsb' (o+8*i) 8) : dwordOf src k=v.extractLsb' o 64 := by
  apply word_ext; intro i hi
  rw [dword_byte src k i hi, h i hi, ext_ext v o 64 (8*i) 8 (by omega)]

/-! ### `writerDwords` by index -/

private theorem gd_left {l1 l2 : List Word} {i : Nat} (h : i<l1.length) : (l1++l2).getD i 0=l1.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

private theorem gd_right {l1 l2 : List Word} {i : Nat} (h : l1.length ≤ i) :
    (l1++l2).getD i 0=l2.getD (i-l1.length) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

private theorem gd_map (n : Nat) (f : Nat → Word) (i : Nat) (h : i<n) : ((List.range n).map f).getD i 0=f i := by
  simp [List.getD_eq_getElem?_getD, h]

theorem writer_dword (p : Nat) (src : Nat → Byte) (c : Word) (i : Nat) :
    (writerDwords p src c).getD i 0 =
      if i<22 then dwordOf src (8*i)
      else if i<34 then dwordOf src (176+32*((i-22)/3)+8*((i-22)%3))
      else if i<37 then (bandATails src).getD (i-34) 0
      else if i<61 then dwordOf src (304+32*((i-37)/3)+8*((i-37)%3))
      else (streamRun p src c).2.2.getD (i-61) 0 := by
  have bl : (bandATails src).length=3 := rfl
  unfold writerDwords
  by_cases h22 : i<22
  · rw [if_pos h22]
    rw [gd_left (by simp [bl]; omega), gd_left (by simp [bl]; omega), gd_left (by simp [bl]; omega), gd_left (by simp [bl]; omega)]
    by_cases h18 : i<18
    · rw [gd_left (by simp [bl]; omega)]
      by_cases h14 : i<14
      · rw [gd_left (by simp [bl]; omega)]
        by_cases h2 : i<2
        · rw [gd_left (by simp [bl]; omega)]
          interval_cases i <;> rfl
        · rw [gd_right (by simp [bl]; omega), gd_map _ _ _ (by simp [bl]; omega)]
          simp only [List.length_cons, List.length_nil]
          congr 1; omega
      · rw [gd_right (by simp [bl]; omega), gd_map _ _ _ (by simp [bl]; omega)]
        simp only [List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil, bl]
        congr 1; omega
    · rw [gd_right (by simp [bl]; omega), gd_map _ _ _ (by simp [bl]; omega)]
      simp only [List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil, bl]
      congr 1; omega
  · rw [if_neg h22]
    by_cases h34 : i<34
    · rw [if_pos h34]
      rw [gd_left (by simp [bl]; omega), gd_left (by simp [bl]; omega), gd_left (by simp [bl]; omega),
        gd_right (by simp [bl]; omega), gd_map _ _ _ (by simp [bl]; omega)]
      simp only [List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil, bl]
    · rw [if_neg h34]
      by_cases h37 : i<37
      · rw [if_pos h37]
        rw [gd_left (by simp [bl]; omega), gd_left (by simp [bl]; omega), gd_right (by simp [bl]; omega)]
        simp only [List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil, bl]
      · rw [if_neg h37]
        by_cases h61 : i<61
        · rw [if_pos h61]
          rw [gd_left (by simp [bl]; omega), gd_right (by simp [bl]; omega), gd_map _ _ _ (by simp [bl]; omega)]
          simp only [List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil, bl]
        · rw [if_neg h61]
          rw [gd_right (by simp [bl]; omega)]
          simp only [List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil, bl]

/-! ### `writerByte` by region of the block -/

/-- Salt, mates, level-0 and level-1 siblings: straight copies (`b < 176`). -/
theorem writer_copy (p : Nat) (src : Nat → Byte) (c : Word) (b : Nat) (hb : b<176) :
    writerByte p src c b=src b := by
  unfold writerByte
  rw [writer_dword, if_pos (by omega), dword_byte src _ _ (by omega)]
  congr 1; omega

/-- Band-A bodies (`176 ≤ b < 272`): 24 of the 32 digest bytes of each level. -/
theorem writer_bandA (p : Nat) (src : Nat → Byte) (c : Word) (b : Nat) (lo : 176 ≤ b) (hi : b<272) :
    writerByte p src c b=src (176+32*((b-176)/24)+(b-176)%24) := by
  unfold writerByte
  rw [writer_dword, if_neg (by omega), if_pos (by omega), dword_byte src _ _ (by omega)]
  congr 1; omega

/-- The three band-A tail words (`272 ≤ b < 296`). -/
theorem writer_tails (p : Nat) (src : Nat → Byte) (c : Word) (b : Nat) (lo : 272 ≤ b) (hi : b<296) :
    writerByte p src c b=((bandATails src).getD ((b-272)/8) 0).extractLsb' (8*(b%8)) 8 := by
  unfold writerByte
  rw [writer_dword, if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 2; omega

/-- Band-B bodies (`296 ≤ b < 488`). -/
theorem writer_bandB (p : Nat) (src : Nat → Byte) (c : Word) (b : Nat) (lo : 296 ≤ b) (hi : b<488) :
    writerByte p src c b=src (304+32*((b-296)/24)+(b-296)%24) := by
  unfold writerByte
  rw [writer_dword, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
    dword_byte src _ _ (by omega)]
  congr 1; omega

/-- The stream dwords (`488 ≤ b`). -/
theorem writer_stream (p : Nat) (src : Nat → Byte) (c : Word) (b : Nat) (lo : 488 ≤ b) :
    writerByte p src c b=((streamRun p src c).2.2.getD ((b-488)/8) 0).extractLsb' (8*((b-488)%8)) 8 := by
  unfold writerByte
  rw [writer_dword, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    show b/8-61=(b-488)/8 by omega, show 8*(b%8)=8*((b-488)%8) by omega]

end TwoPermutationPrototype.GroupedOpening.Layout2
