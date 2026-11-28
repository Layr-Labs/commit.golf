import CommitGolfCandidate.HybWrapKit

/-! Copy and clear blocks of the hybrid wrapper as action lists, with their effects. -/

namespace TwoPermutationPrototype.HybWrap
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Checker TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.CheckActions

set_option maxHeartbeats 1500000

/-- `n` doubleword copies from words `S + m` to words `D + m` through `x31`. -/
def copyActs (src dst : Reg) (a b S D n : Nat) : List Action :=
  (List.range n).flatMap fun m =>
    [.load .x31 src (BitVec.ofNat 12 (a+8*m)) (S+m), .store dst .x31 (BitVec.ofNat 12 (b+8*m)) (D+m)]

theorem copy_acts_op (src dst : Reg) (a b S D n : Nat) :
    (copyActs src dst a b S D n).map Action.op = copyPairs src dst a b n := by
  simp [copyActs, copyPairs, List.map_flatMap, Action.op]

theorem copy_acts_succ (src dst : Reg) (a b S D n : Nat) :
    copyActs src dst a b S D (n+1) = copyActs src dst a b S D n ++
      [.load .x31 src (BitVec.ofNat 12 (a+8*n)) (S+n), .store dst .x31 (BitVec.ofNat 12 (b+8*n)) (D+n)] := by
  unfold copyActs
  rw [List.range_succ, List.flatMap_append]
  simp

theorem copy_acts_length (src dst : Reg) (a b S D n : Nat) : (copyActs src dst a b S D n).length = 2*n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [copy_acts_succ, List.length_append, ih]; simp; ring

theorem copy_run (o : Oracle) (s : MachineState) (src dst : Reg) (hs : src ≠ .x31) (hd : dst ≠ .x31)
    (a b S D n Sb Db : Nat) (srcv : s.getReg src = BitVec.ofNat 64 Sb) (dstv : s.getReg dst = BitVec.ofNat 64 Db)
    (sa : Sb + a = 8*S) (db : Db + b = 8*D) (ra : a + 8*n ≤ 2048) (rb : b + 8*n ≤ 2048)
    (bs : S + n ≤ 2^33) (bd : D + n ≤ 2^33) (disj : S + n ≤ D ∨ D + n ≤ S) :
    validFixed o (copyActs src dst a b S D n) s ∧
      (∀ r, r ≠ .x31 → (fixedOps o (copyActs src dst a b S D n) s).getReg r = s.getReg r) ∧
      (∀ w < 2^33, memoryView (fixedOps o (copyActs src dst a b S D n) s) w =
        if D ≤ w ∧ w < D+n then memoryView s (S+(w-D)) else memoryView s w) := by
  suffices h : ∀ m ≤ n, validFixed o (copyActs src dst a b S D m) s ∧
      (∀ r, r ≠ .x31 → (fixedOps o (copyActs src dst a b S D m) s).getReg r = s.getReg r) ∧
      (∀ w < 2^33, memoryView (fixedOps o (copyActs src dst a b S D m) s) w =
        if D ≤ w ∧ w < D+m then memoryView s (S+(w-D)) else memoryView s w) from h n le_rfl
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨trivial, fun r _ => rfl, fun w _ => ?_⟩
    rw [if_neg (by omega)]; rfl
  | succ m ih =>
    intro hm
    obtain ⟨ok, regs, mem⟩ := ih (by omega)
    rw [copy_acts_succ, validFixed_append, fixedOps_append]
    generalize ht : fixedOps o (copyActs src dst a b S D m) s = t at ok regs mem
    have tsrc : t.getReg src = BitVec.ofNat 64 Sb := (regs src hs).trans srcv
    have tdst : t.getReg dst = BitVec.ofNat 64 Db := (regs dst hd).trans dstv
    have loadAt : t.getReg src + signExtend12 (BitVec.ofNat 12 (a+8*m)) = wordAddress (S+m) := by
      rw [tsrc, add_small _ _ (by omega) (by omega)]
      unfold wordAddress; congr 1; omega
    let u := fixedStep o t (.load .x31 src (BitVec.ofNat 12 (a+8*m)) (S+m))
    have uu : u = putReg t .x31 (memoryView t (S+m)) := rfl
    have udst : u.getReg dst = BitVec.ofNat 64 Db := by
      rw [uu, put_reg_reg, if_neg (by intro h; exact hd h.1.symm), tdst]
    have u31 : u.getReg .x31 = memoryView t (S+m) := by
      rw [uu, put_reg_reg, if_pos ⟨rfl, by decide⟩]
    have storeAt : u.getReg dst + signExtend12 (BitVec.ofNat 12 (b+8*m)) = wordAddress (D+m) := by
      rw [udst, add_small _ _ (by omega) (by omega)]
      unfold wordAddress; congr 1; omega
    refine ⟨⟨ok, ⟨loadAt, by omega⟩, ⟨storeAt, by omega⟩, trivial⟩, ?_, ?_⟩
    · intro r hr
      change (fixedStep o u (.store dst .x31 (BitVec.ofNat 12 (b+8*m)) (D+m))).getReg r = _
      change (putWord u (D+m) (u.getReg .x31)).getReg r = _
      rw [put_word_reg, uu, put_reg_reg, if_neg (by intro h; exact hr h.1.symm)]
      exact regs r hr
    · intro w hw
      change memoryView (putWord u (D+m) (u.getReg .x31)) w = _
      rw [put_word_view _ _ _ _ (by omega) (by omega), u31, uu, put_reg_view]
      by_cases at_ : w = D+m
      · rw [if_pos at_, if_pos (by omega), mem _ (by omega), if_neg (by omega)]
        congr 1; omega
      · rw [if_neg at_, mem w hw]
        by_cases inside : D ≤ w ∧ w < D+m
        · rw [if_pos inside, if_pos (by omega)]
        · rw [if_neg inside, if_neg (by omega)]

/-- `n` doubleword clears of words `D + m`. -/
def zeroActs (base : Reg) (D n : Nat) : List Action :=
  (List.range n).map fun m => .store base .x0 (BitVec.ofNat 12 (8*m)) (D+m)

theorem zero_acts_op (base : Reg) (D n : Nat) : (zeroActs base D n).map Action.op = zeroStores base n := by
  simp [zeroActs, zeroStores, Action.op]

theorem zero_acts_length (base : Reg) (D n : Nat) : (zeroActs base D n).length = n := by
  simp [zeroActs]

theorem zero_run (o : Oracle) (s : MachineState) (base : Reg) (D n : Nat)
    (basev : s.getReg base = BitVec.ofNat 64 (8*D)) (rn : 8*n ≤ 2048) (bd : D + n ≤ 2^33) :
    validFixed o (zeroActs base D n) s ∧
      (∀ r, (fixedOps o (zeroActs base D n) s).getReg r = s.getReg r) ∧
      (∀ w < 2^33, memoryView (fixedOps o (zeroActs base D n) s) w =
        if D ≤ w ∧ w < D+n then 0 else memoryView s w) := by
  suffices h : ∀ m ≤ n, validFixed o (zeroActs base D m) s ∧
      (∀ r, (fixedOps o (zeroActs base D m) s).getReg r = s.getReg r) ∧
      (∀ w < 2^33, memoryView (fixedOps o (zeroActs base D m) s) w =
        if D ≤ w ∧ w < D+m then 0 else memoryView s w) from h n le_rfl
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨trivial, fun r => rfl, fun w _ => ?_⟩
    rw [if_neg (by omega)]; rfl
  | succ m ih =>
    intro hm
    obtain ⟨ok, regs, mem⟩ := ih (by omega)
    rw [show zeroActs base D (m+1) = zeroActs base D m ++ [.store base .x0 (BitVec.ofNat 12 (8*m)) (D+m)] by
      unfold zeroActs; rw [List.range_succ, List.map_append]; rfl, validFixed_append, fixedOps_append]
    generalize ht : fixedOps o (zeroActs base D m) s = t at ok regs mem
    have storeAt : t.getReg base + signExtend12 (BitVec.ofNat 12 (8*m)) = wordAddress (D+m) := by
      rw [regs, basev, add_small _ _ (by omega) (by omega)]
      unfold wordAddress; congr 1; omega
    refine ⟨⟨ok, ⟨storeAt, by omega⟩, trivial⟩, ?_, ?_⟩
    · intro r
      change (putWord t (D+m) (t.getReg .x0)).getReg r = _
      rw [put_word_reg, regs]
    · intro w hw
      change memoryView (putWord t (D+m) (t.getReg .x0)) w = _
      rw [put_word_view _ _ _ _ (by omega) (by omega), reg_zero]
      by_cases at_ : w = D+m
      · rw [if_pos at_, if_pos (by omega)]; rfl
      · rw [if_neg at_, mem w hw]
        by_cases inside : D ≤ w ∧ w < D+m
        · rw [if_pos inside, if_pos (by omega)]
        · rw [if_neg inside, if_neg (by omega)]

theorem copy_free (src dst : Reg) (a b S D n : Nat) : PermFree (copyActs src dst a b S D n) := by
  intro x hx
  simp only [copyActs, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hx
  obtain ⟨m, _, h | h⟩ := hx <;> subst h <;> rfl

theorem zero_free (base : Reg) (D n : Nat) : PermFree (zeroActs base D n) := by
  intro x hx
  simp only [zeroActs, List.mem_map, List.mem_range] at hx
  obtain ⟨m, _, h⟩ := hx; subst h; rfl

end TwoPermutationPrototype.HybWrap
