import CommitGolfCandidate.GroupOpenSiblingRun

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open PackedOpening (ByteCopy)

attribute [local simp] MachineState.getReg_setPC Opening.getReg_setReg

@[local simp] private theorem mem_set_register (state : MachineState) (reg : Reg) (word : Word) :
    (state.setReg reg word).mem = state.mem := by cases reg <;> rfl

@[local simp] private theorem mem_set_pc (state : MachineState) (pc : Word) :
    (state.setPC pc).mem = state.mem := rfl

/-! ### The T238 fold (record F and cap WS)

Iteration `j < 7`, at word `start+5j`: `lhu x28,o_j(x21); slli x29,x31,14; or x28,x28,x29; sh x28,o_j(x21)`,
then `srli x31,x31,2` unless `j = 6`. With `x21` the base `B` of a group's eighth slot, `o_j = -182+30j` is the
halfword at byte 28 of slot `j`. -/

def foldIterRows (start j : Nat) : List (Nat × Instr) :=
  [(start+5*j, .LHU .x28 .x21 (foldOffset j)), (start+5*j+1, .SLLI .x29 .x31 14),
   (start+5*j+2, .OR .x28 .x28 .x29), (start+5*j+3, .SH .x21 .x28 (foldOffset j))] ++
  (if j < 6 then [(start+5*j+4, .SRLI .x31 .x31 2)] else [])

def foldIterLen (j : Nat) : Nat := if j < 6 then 5 else 4

theorem fold_iter_length (start j : Nat) : (foldIterRows start j).length = foldIterLen j := by
  unfold foldIterRows foldIterLen; split <;> rfl

theorem fold_iter_code : ∀ j : Fin 7,
    RowsCode (foldIterRows foldStart j.val) ∧ RowsCode (foldIterRows (wsStart+1) j.val) := by
  decide +kernel

theorem fold_offset_value : ∀ j : Fin 7,
    signExtend12 (foldOffset j.val) = -(BitVec.ofNat 64 (182-30*j.val)) := by
  decide

/-- The halfword address of slot `j`, from the base `B` of the eighth slot. -/
def foldAddress (base j : Nat) : Nat := base-182+30*j

theorem fold_address (base j : Nat) (inside : j < 7) (low : 182 ≤ base) (fit : base < 2^64) :
    BitVec.ofNat 64 base + signExtend12 (foldOffset j) = BitVec.ofNat 64 (foldAddress base j) := by
  rw [fold_offset_value ⟨j, inside⟩, ← BitVec.sub_eq_add_neg,
    BitVec.ofNat_sub_ofNat_of_le (w := 64) base (182-30*j) (by omega) (by omega)]
  unfold foldAddress
  congr 1
  omega

/-- What `lhu; slli; or; sh` leaves: the old halfword OR'd with the shifted top bits. -/
def foldValue (half : BitVec 16) (top : Word) : BitVec 16 := ((half.zeroExtend 64 ||| (top <<< 14)).truncate 16)

theorem fold_iter_post (start j : Nat) (t : MachineState) :
    let u := rowsState t (foldIterRows start j) (foldIterLen j)
    u.mem = (t.setHalfword (t.getReg .x21 + signExtend12 (foldOffset j))
      (foldValue (t.getHalfword (t.getReg .x21 + signExtend12 (foldOffset j))) (t.getReg .x31))).mem ∧
    u.getReg .x21 = t.getReg .x21 ∧
    u.getReg .x31 = (if j < 6 then t.getReg .x31 >>> 2 else t.getReg .x31) ∧
    ∀ reg, reg ≠ .x28 → reg ≠ .x29 → reg ≠ .x31 → u.getReg reg = t.getReg reg := by
  by_cases last : j < 6
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simp [rowsState, foldIterRows, foldIterLen, last, execInstrBr, foldValue]
      apply half_mem_congr
      simp
    · simp [rowsState, foldIterRows, foldIterLen, last, execInstrBr]
    · simp [rowsState, foldIterRows, foldIterLen, last, execInstrBr]
    · intro reg a b c
      simp [rowsState, foldIterRows, foldIterLen, last, execInstrBr,
        Ne.symm a, Ne.symm b, Ne.symm c]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simp [rowsState, foldIterRows, foldIterLen, last, execInstrBr, foldValue]
      apply half_mem_congr
      simp
    · simp [rowsState, foldIterRows, foldIterLen, last, execInstrBr]
    · simp [rowsState, foldIterRows, foldIterLen, last, execInstrBr]
    · intro reg a b c
      simp [rowsState, foldIterRows, foldIterLen, last, execInstrBr,
        Ne.symm a, Ne.symm b, Ne.symm c]

theorem fold_iter_run (start j : Nat) (t : MachineState) (code : RowsCode (foldIterRows start j))
    (inside : j < 7) (base : Nat) (low : 182 ≤ base) (fit : base+2 ≤ MEMORY_BYTES) (even : base % 2 = 0)
    (pc : t.pc = BitVec.ofNat 64 (4096+4*(start+5*j)))
    (pointer : t.getReg .x21 = BitVec.ofNat 64 base) :
    RunsOpeningBlock t (rowsState t (foldIterRows start j) (foldIterLen j)) (foldIterLen j) ∧
    (rowsState t (foldIterRows start j) (foldIterLen j)).pc =
      BitVec.ofNat 64 (4096+4*(start+5*j+foldIterLen j)) := by
  have ram : MEMORY_BYTES < 2^64 := by decide
  have addr := fold_address base j inside low (by omega)
  have slotEven : foldAddress base j % 2 = 0 := by unfold foldAddress; omega
  have slotFit : foldAddress base j+2 ≤ MEMORY_BYTES := by unfold foldAddress; omega
  have start0 : ∀ h : 0 < (foldIterRows start j).length,
      t.pc = BitVec.ofNat 64 (4096+4*(foldIterRows start j)[0].1) := fun _ => pc
  have lengthEq := fold_iter_length start j
  constructor
  · intro fuel coins
    have run := execute_rows t (foldIterRows start j) code start0 ?_ fuel coins
    · rw [lengthEq] at run
      exact run
    · intro i h
      rw [lengthEq] at h
      have small : i < 5 := by unfold foldIterLen at h; split at h <;> omega
      interval_cases i
      · change accessValid (t.getReg .x21 + signExtend12 (foldOffset j)) 2 = true
        rw [pointer, addr]; exact half_access _ slotEven slotFit
      · rfl
      · rfl
      · have r : (rowsState t (foldIterRows start j) 3).getReg .x21 = t.getReg .x21 := by
          simp [rowsState, foldIterRows, execInstrBr]
        change accessValid ((rowsState t (foldIterRows start j) 3).getReg .x21 + signExtend12 (foldOffset j)) 2 = true
        rw [r, pointer, addr]; exact half_access _ slotEven slotFit
      · have six : j < 6 := by unfold foldIterLen at h; split at h <;> omega
        simp only [foldIterRows, if_pos six]
        rfl
  · by_cases six : j < 6
    · have len : foldIterLen j = 5 := by simp [foldIterLen, six]
      have final := rows_after_pc t (foldIterRows start j) code start0 4 (by rw [lengthEq, len])
      rw [len, final]
      simp only [foldIterRows, if_pos six, List.cons_append, List.nil_append, List.getElem_cons_succ,
        List.getElem_cons_zero, rowNext]
    · have len : foldIterLen j = 4 := by simp [foldIterLen, six]
      have final := rows_after_pc t (foldIterRows start j) code start0 3 (by rw [lengthEq, len])
      rw [len, final]
      simp only [foldIterRows, if_neg six, List.append_nil, List.getElem_cons_succ,
        List.getElem_cons_zero, rowNext]

/-- Iterations `0 .. k-1` of the fold. -/
def foldUpTo (start : Nat) : Nat → MachineState → MachineState
  | 0, t => t
  | k+1, t => rowsState (foldUpTo start k t) (foldIterRows start k) (foldIterLen k)

def foldWords (k : Nat) : Nat := if k ≤ 6 then 5*k else 34

private theorem fold_words_next (k : Nat) (inside : k < 7) : foldWords (k+1) = foldWords k + foldIterLen k := by
  unfold foldWords foldIterLen; split <;> split <;> (try split) <;> omega

private theorem aligned_apart (a b : Nat) (apart : a+8 ≤ b) (fit : b+8 ≤ 2^64) :
    alignToDword (BitVec.ofNat 64 a) ≠ alignToDword (BitVec.ofNat 64 b) := by
  intro same
  have values := congrArg BitVec.toNat same
  rw [align_nat a (by omega), align_nat b fit] at values
  omega

/-- The fold, iteration by iteration: run, pointer and top register, and the memory (word view): the slot
words are the halfword updates, every other word unchanged. -/
theorem fold_up_to (start : Nat) (code : ∀ j < 7, RowsCode (foldIterRows start j)) (t : MachineState)
    (base : Nat) (x : BitVec 16) (low : 182 ≤ base) (fit : base+2 ≤ MEMORY_BYTES) (even : base % 2 = 0)
    (pc : t.pc = BitVec.ofNat 64 (4096+4*start)) (pointer : t.getReg .x21 = BitVec.ofNat 64 base)
    (top : t.getReg .x31 = x.zeroExtend 64) :
    ∀ k, k ≤ 7 →
      RunsOpeningBlock t (foldUpTo start k t) (foldWords k) ∧
      (foldUpTo start k t).pc = BitVec.ofNat 64 (4096+4*(start+foldWords k)) ∧
      (foldUpTo start k t).getReg .x21 = BitVec.ofNat 64 base ∧
      (k ≤ 6 → (foldUpTo start k t).getReg .x31 = x.zeroExtend 64 >>> (2*k)) ∧
      (∀ reg, reg ≠ .x28 → reg ≠ .x29 → reg ≠ .x31 → (foldUpTo start k t).getReg reg = t.getReg reg) ∧
      (∀ w, (∀ j < k, w ≠ alignToDword (BitVec.ofNat 64 (foldAddress base j))) →
        (foldUpTo start k t).getMem w = t.getMem w) ∧
      (∀ j < k, (foldUpTo start k t).getMem (alignToDword (BitVec.ofNat 64 (foldAddress base j))) =
        (t.setHalfword (BitVec.ofNat 64 (foldAddress base j))
          (foldValue (t.getHalfword (BitVec.ofNat 64 (foldAddress base j))) (x.zeroExtend 64 >>> (2*j)))).getMem
          (alignToDword (BitVec.ofNat 64 (foldAddress base j)))) := by
  have ram : MEMORY_BYTES < 2^64 := by decide
  have ramv : MEMORY_BYTES = 68719476736 := rfl
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨fun fuel coins => by simp [foldUpTo, foldWords, Execution.charge], ?_, pointer, ?_, fun _ _ _ _ => rfl,
      fun _ _ => rfl, fun j hj => (by omega : False).elim⟩
    · simpa [foldUpTo, foldWords] using pc
    · intro _; simpa [foldUpTo] using top
  | succ k ih =>
    intro bound
    obtain ⟨run, atPC, ptr, topReg, keep, frame, slots⟩ := ih (by omega)
    let u := foldUpTo start k t
    have post := fold_iter_post start k u
    have iterPC : u.pc = BitVec.ofNat 64 (4096+4*(start+5*k)) := by
      rw [atPC]; unfold foldWords; rw [if_pos (by omega)]
    obtain ⟨iterRun, iterEnd⟩ := fold_iter_run start k u (code k (by omega)) (by omega) base low fit even iterPC ptr
    have addr := fold_address base k (by omega) low (by omega)
    have uTop : u.getReg .x31 = x.zeroExtend 64 >>> (2*k) := topReg (by omega)
    have memNext : (foldUpTo start (k+1) t).mem = (u.setHalfword (BitVec.ofNat 64 (foldAddress base k))
        (foldValue (u.getHalfword (BitVec.ofNat 64 (foldAddress base k))) (x.zeroExtend 64 >>> (2*k)))).mem := by
      have m := post.1
      rw [ptr, addr, uTop] at m
      exact m
    have slotOthers (j : Nat) (hj : j < k) :
        alignToDword (BitVec.ofNat 64 (foldAddress base j)) ≠ alignToDword (BitVec.ofNat 64 (foldAddress base k)) :=
      aligned_apart _ _ (by unfold foldAddress; omega) (by unfold foldAddress; omega)
    have uHalf : u.getHalfword (BitVec.ofNat 64 (foldAddress base k)) = t.getHalfword (BitVec.ofNat 64 (foldAddress base k)) := by
      unfold MachineState.getHalfword
      rw [frame _ (fun j hj => (slotOthers j hj).symm)]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [fold_words_next k (by omega)]
      exact run.next iterRun
    · change (rowsState u (foldIterRows start k) (foldIterLen k)).pc = _
      rw [iterEnd, fold_words_next k (by omega)]
      congr 2
      unfold foldWords; rw [if_pos (by omega)]; omega
    · exact post.2.1.trans ptr
    · intro six
      change (rowsState u (foldIterRows start k) (foldIterLen k)).getReg .x31 = _
      rw [post.2.2.1, if_pos (by omega), uTop]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight, ← Nat.shiftRight_add]
      congr 1
    · intro reg a b c
      exact (post.2.2.2 reg a b c).trans (keep reg a b c)
    · intro w away
      change (foldUpTo start (k+1) t).mem w = t.mem w
      rw [memNext]
      change (u.setHalfword _ _).getMem w = t.getMem w
      rw [set_half_eq, MachineState.getMem_setMem_ne (away k (by omega))]
      exact frame w (fun j hj => away j (by omega))
    · intro j hj
      change (foldUpTo start (k+1) t).mem _ = _
      rw [memNext]
      by_cases now : j = k
      · subst now
        change (u.setHalfword _ _).getMem _ = _
        rw [set_half_eq, set_half_eq, MachineState.getMem_setMem_eq, MachineState.getMem_setMem_eq, uHalf,
          frame _ (fun i hi => (slotOthers i hi).symm)]
      · change (u.setHalfword _ _).getMem _ = _
        rw [set_half_eq, MachineState.getMem_setMem_ne (slotOthers j (by omega))]
        exact slots j (by omega)


theorem fold_slot_bytes (start : Nat) (code : ∀ j < 7, RowsCode (foldIterRows start j)) (t : MachineState)
    (base : Nat) (x : BitVec 16) (low : 182 ≤ base) (fit : base+8 ≤ MEMORY_BYTES) (even : base % 2 = 0)
    (pc : t.pc = BitVec.ofNat 64 (4096+4*start)) (pointer : t.getReg .x21 = BitVec.ofNat 64 base)
    (top : t.getReg .x31 = x.zeroExtend 64) (j b : Nat) (inside : j < 7) (small : b < 2) :
    (foldUpTo start 7 t).getByte (BitVec.ofNat 64 (foldAddress base j+b)) =
      (foldValue (t.getHalfword (BitVec.ofNat 64 (foldAddress base j))) (x.zeroExtend 64 >>> (2*j))).extractLsb' (8*b) 8 := by
  have ram : MEMORY_BYTES < 2^64 := by decide
  have ramv : MEMORY_BYTES = 68719476736 := rfl
  have slots := (fold_up_to start code t base x low (by omega) even pc pointer top 7 (by omega)).2.2.2.2.2.2 j inside
  have slotEven : foldAddress base j % 2 = 0 := by unfold foldAddress; omega
  have slotFit : foldAddress base j+16 ≤ 2^64 := by unfold foldAddress; omega
  have align : alignToDword (BitVec.ofNat 64 (foldAddress base j+b)) = alignToDword (BitVec.ofNat 64 (foldAddress base j)) :=
    same_dword _ _ (by omega) (by omega) (by omega)
  rw [byte_of_dword _ ((t.setHalfword (BitVec.ofNat 64 (foldAddress base j))
    (foldValue (t.getHalfword (BitVec.ofNat 64 (foldAddress base j))) (x.zeroExtend 64 >>> (2*j))))) _ (by rw [align]; exact slots)]
  exact byte_after_halfword _ _ _ _ slotEven slotFit small

theorem fold_frame_bytes (start : Nat) (code : ∀ j < 7, RowsCode (foldIterRows start j)) (t : MachineState)
    (base : Nat) (x : BitVec 16) (low : 182 ≤ base) (fit : base+8 ≤ MEMORY_BYTES) (even : base % 2 = 0)
    (pc : t.pc = BitVec.ofNat 64 (4096+4*start)) (pointer : t.getReg .x21 = BitVec.ofNat 64 base)
    (top : t.getReg .x31 = x.zeroExtend 64) (q : Nat) (qfit : q+8 ≤ 2^64)
    (away : ∀ j < 7, q ≠ foldAddress base j ∧ q ≠ foldAddress base j+1) :
    (foldUpTo start 7 t).getByte (BitVec.ofNat 64 q) = t.getByte (BitVec.ofNat 64 q) := by
  have ram : MEMORY_BYTES < 2^64 := by decide
  have ramv : MEMORY_BYTES = 68719476736 := rfl
  obtain ⟨-, -, -, -, -, frame, slots⟩ := fold_up_to start code t base x low (by omega) even pc pointer top 7 (by omega)
  by_cases hit : ∃ j < 7, alignToDword (BitVec.ofNat 64 q) = alignToDword (BitVec.ofNat 64 (foldAddress base j))
  · obtain ⟨j, inside, same⟩ := hit
    have slotEven : foldAddress base j % 2 = 0 := by unfold foldAddress; omega
    rw [byte_of_dword _ ((t.setHalfword (BitVec.ofNat 64 (foldAddress base j))
      (foldValue (t.getHalfword (BitVec.ofNat 64 (foldAddress base j))) (x.zeroExtend 64 >>> (2*j))))) _
      (by rw [same]; exact slots j inside)]
    apply ProjectedHalfword.store_outside _ _ _ _ (even_word _ slotEven (by unfold foldAddress; omega))
    refine ⟨fun e => (away j inside).1 (Opening.nat_address_injective (by omega) (by unfold foldAddress; omega) e), ?_⟩
    intro e
    rw [← word_succ] at e
    exact (away j inside).2 (Opening.nat_address_injective (by omega) (by unfold foldAddress; omega) e)
  · push_neg at hit
    exact byte_of_dword _ _ _ (frame _ hit)


end TwoPermutationPrototype.GroupedOpening
