import CommitGolfCandidate.NonceChainExec

/-! The salt-mask pass. After the expansion, a 50-instruction loop runs 2^20 times and clears
bits 57..63 of the high word of every one of the 2^24 salts, leaving 121 uniform bits per salt.
It occupies code words 233324..233379 and then jumps to word 16, where the expansion used to return. -/
namespace TwoPermutationPrototype.RV64.Chain
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def maskSetupOps : List Instr :=
  [.ADDI .x25 .x0 (-1),.SRLI .x25 .x25 7,.ADDI .x23 .x22 8,.LUI .x24 65536,.ADD .x24 .x24 .x23]

def maskGroupOps (u : Nat) : List Instr :=
  [.LD .x26 .x23 (BitVec.ofNat 12 (16*u)),.AND .x26 .x26 .x25,.SD .x23 .x26 (BitVec.ofNat 12 (16*u))]

def maskTailOps : List Instr := [.ADDI .x23 .x23 256,.BNE .x23 .x24 7996]

abbrev maskWord : Word := BitVec.ofNat 64 (2^57-1)
abbrev maskCursor (j : Nat) : Nat := nonceChainBase + 8 + 256*j


/-- The high salt words already masked after `c` salts. -/
def MaskedSalt (c : Nat) (b : Word) : Prop :=
  nonceChainBase + 8 ≤ b.toNat ∧ b.toNat < nonceChainBase + 8 + 16*c ∧
    (b.toNat - (nonceChainBase + 8)) % 16 = 0

instance (c : Nat) (b : Word) : Decidable (MaskedSalt c b) := by unfold MaskedSalt; infer_instance

/-- Memory after masking the first `c` salts of `orig`. -/
def MaskedUpTo (orig : MachineState) (c : Nat) (s : MachineState) : Prop :=
  ∀ b : Word, s.getMem b = if MaskedSalt c b then orig.getMem b &&& maskWord else orig.getMem b

private theorem mask_setup_decoded : ∀ i : Fin 5,
    Manifest.decodeBase (packed_wideCodeWord (233324+i.val)) = some ((maskSetupOps[i.val]?).getD .EBREAK) := by
  decide +kernel

private theorem mask_group_decoded : ∀ u : Fin 16, ∀ k : Fin 3,
    Manifest.decodeBase (packed_wideCodeWord (233329+3*u.val+k.val)) =
      some (((maskGroupOps u.val)[k.val]?).getD .EBREAK) := by
  decide +kernel

private theorem mask_tail_decoded : ∀ i : Fin 2,
    Manifest.decodeBase (packed_wideCodeWord (233377+i.val)) = some ((maskTailOps[i.val]?).getD .EBREAK) := by
  decide +kernel

private theorem mask_exit_decoded :
    Manifest.decodeBase (packed_wideCodeWord 233379) = some (.JAL .x0 1163700) := by
  decide +kernel

private theorem group_offsets : ∀ u : Fin 16,
    signExtend12 (BitVec.ofNat 12 (16*u.val)) = BitVec.ofNat 64 (16*u.val) := by
  decide

private theorem pc_add (a k : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 k = BitVec.ofNat 64 (a+k) :=
  (BitVec.ofNat_add a k).symm

theorem mask_cursor_valid (j u : Nat) (hj : j < 1048576) (hu : u < 16) :
    accessValid (BitVec.ofNat 64 (maskCursor j) + BitVec.ofNat 64 (16*u)) 8 = true := by
  rw [pc_add]
  unfold accessValid rangeValid MEMORY_BYTES
  have small : maskCursor j + 16*u < 2^64 := by unfold maskCursor nonceChainBase; omega
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small, Bool.and_eq_true, decide_eq_true_eq]
  unfold maskCursor nonceChainBase
  omega

@[local simp] private theorem get_x0 (s : MachineState) : s.getReg .x0 = 0 := rfl
@[local simp] private theorem set_x0 (s : MachineState) (v : Word) : s.setReg .x0 v = s := rfl
@[local simp] theorem set_reg_pc (s : MachineState) (r : Reg) (v : Word) : (s.setReg r v).pc = s.pc := by
  cases r <;> rfl
@[local simp] private theorem set_reg_mem (s : MachineState) (r : Reg) (v : Word) : (s.setReg r v).mem = s.mem := by
  cases r <;> rfl
@[local simp] theorem set_pc_pc (s : MachineState) (v : Word) : (s.setPC v).pc = v := rfl
@[local simp] private theorem set_pc_mem (s : MachineState) (v : Word) : (s.setPC v).mem = s.mem := rfl
@[local simp] private theorem set_pc_get_mem (s : MachineState) (v b : Word) : (s.setPC v).getMem b = s.getMem b := rfl
@[local simp] private theorem set_mem_pc (s : MachineState) (a v : Word) : (s.setMem a v).pc = s.pc := rfl
@[local simp] private theorem set_mem_reg (s : MachineState) (a v : Word) (r : Reg) :
    (s.setMem a v).getReg r = s.getReg r := by cases r <;> rfl
private theorem set_mem_get (s : MachineState) (a v b : Word) :
    (s.setMem a v).getMem b = if b = a then v else s.getMem b := by
  by_cases h : b = a
  · subst h; simp
  · simp [h]
@[local simp] private theorem reg_set_ne (s : MachineState) (r r' : Reg) (v : Word) (h : r ≠ r') :
    (s.setReg r v).getReg r' = s.getReg r' := MachineState.getReg_setReg_ne s r r' v h
@[local simp] private theorem reg_set_eq (s : MachineState) (r : Reg) (v : Word) (h : r ≠ .x0) :
    (s.setReg r v).getReg r = v := MachineState.getReg_setReg_eq h

private theorem bne_step (s : MachineState) (a b : Reg) (off : BitVec 13) :
    execInstrBr s (.BNE a b off) =
      if s.getReg a = s.getReg b then s.setPC (s.pc + 4) else s.setPC (s.pc + signExtend13 off) := by
  by_cases h : s.getReg a = s.getReg b <;> simp [execInstrBr, h]



/-! ### One group: mask one salt -/

def maskGroup (s : MachineState) (u : Nat) : MachineState := (maskGroupOps u).foldl execInstrBr s

private theorem group_prefix_pc (s : MachineState) (u i : Nat) (hi : i < 3) :
    (((maskGroupOps u).take i).foldl execInstrBr s).pc = s.pc + BitVec.ofNat 64 (4*i) := by
  interval_cases i <;> simp [maskGroupOps, execInstrBr, BitVec.add_assoc] <;> rfl

private theorem group_prefix_x23 (s : MachineState) (u i : Nat) (hi : i < 3) :
    (((maskGroupOps u).take i).foldl execInstrBr s).getReg .x23 = s.getReg .x23 := by
  interval_cases i <;> simp [maskGroupOps, execInstrBr]

theorem mask_group_run (s : MachineState) (u : Nat) (hu : u < 16)
    (pc : s.pc = BitVec.ofNat 64 (4096+4*(233329+3*u)))
    (valid : accessValid (s.getReg .x23 + BitVec.ofNat 64 (16*u)) 8 = true) (fuel : Nat) :
    execute packedWideCommitImage (3+fuel) s true =
      (do let r ← execute packedWideCommitImage fuel (maskGroup s u) true
          return r.charge 3 0) := by
  have off := group_offsets ⟨u,hu⟩
  apply execute_unit_steps (states := fun i => ((maskGroupOps u).take i).foldl execInstrBr s)
  intro i hi
  refine ⟨.base (((maskGroupOps u)[i]?).getD .EBREAK),?_,?_,?_⟩
  · apply packed_wide_fetch_decoded _ (233329+3*u+i) (by omega)
    · rw [group_prefix_pc s u i hi, pc, pc_add]
      congr 1
      omega
    · exact mask_group_decoded ⟨u,hu⟩ ⟨i,hi⟩
  · have x23 := group_prefix_x23 s u i hi
    interval_cases i
    · simp [ordinaryStep, memoryArgumentsValid, memAccess, maskGroupOps, off, valid]
    · simp [ordinaryStep, memoryArgumentsValid, memAccess, maskGroupOps]
    · simp only [List.take, maskGroupOps, List.foldl] at x23 ⊢
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, ordinaryStep,
        memoryArgumentsValid, memAccess, x23, off, valid, if_true]
  · interval_cases i <;> rfl

theorem mask_group_pc (s : MachineState) (u : Nat) : (maskGroup s u).pc = s.pc + 12 := by
  simp [maskGroup, maskGroupOps, execInstrBr, BitVec.add_assoc]

theorem mask_group_reg (s : MachineState) (u : Nat) (r : Reg) (h : r ≠ .x26) :
    (maskGroup s u).getReg r = s.getReg r := by
  simp [maskGroup, maskGroupOps, execInstrBr, Ne.symm h]

theorem mask_group_mem (s : MachineState) (u : Nat) (hu : u < 16) (b : Word) :
    (maskGroup s u).getMem b =
      if b = s.getReg .x23 + BitVec.ofNat 64 (16*u) then s.getMem b &&& s.getReg .x25 else s.getMem b := by
  have off := group_offsets ⟨u,hu⟩
  simp only [maskGroup, maskGroupOps, List.foldl, execInstrBr, set_pc_get_mem, set_mem_get, set_pc_mem,
    MachineState.getReg_setPC, reg_set_ne _ _ _ _ (by decide : Reg.x26 ≠ .x23),
    reg_set_ne _ _ _ _ (by decide : Reg.x26 ≠ .x25), reg_set_eq _ _ _ (by decide : Reg.x26 ≠ .x0),
    MachineState.getMem_setReg, off]
  by_cases hb : b = s.getReg .x23 + BitVec.ofNat 64 (16*u)
  · rw [if_pos hb, if_pos hb, hb]
  · rw [if_neg hb, if_neg hb]

/-- Masking the salt at the cursor extends the masked prefix by one salt. -/
theorem mask_group_masked (orig s : MachineState) (u c : Nat) (hu : u < 16)
    (before : MaskedUpTo orig c s)
    (cursor : (s.getReg .x23 + BitVec.ofNat 64 (16*u)).toNat = nonceChainBase + 8 + 16*c)
    (mask : s.getReg .x25 = maskWord) :
    MaskedUpTo orig (c+1) (maskGroup s u) := by
  intro b
  rw [mask_group_mem s u hu b, mask]
  by_cases hb : b = s.getReg .x23 + BitVec.ofNat 64 (16*u)
  · have bn : b.toNat = nonceChainBase + 8 + 16*c := by rw [hb, cursor]
    have old : ¬ MaskedSalt c b := by unfold MaskedSalt; omega
    have new : MaskedSalt (c+1) b := by unfold MaskedSalt; omega
    rw [if_pos hb, before b, if_neg old, if_pos new]
  · have bn : b.toNat ≠ nonceChainBase + 8 + 16*c := by
      intro same
      exact hb (BitVec.eq_of_toNat_eq (same.trans cursor.symm))
    have iff : MaskedSalt (c+1) b ↔ MaskedSalt c b := by unfold MaskedSalt; omega
    rw [if_neg hb, before b]
    by_cases m : MaskedSalt c b
    · rw [if_pos m, if_pos (iff.mpr m)]
    · rw [if_neg m, if_neg (fun h => m (iff.mp h))]

attribute [local irreducible] maskGroup

/-! ### Sixteen groups -/

def maskGroups (s : MachineState) : Nat → MachineState
  | 0 => s
  | n+1 => maskGroup (maskGroups s n) n

theorem mask_groups_pc (s : MachineState) (n : Nat) : (maskGroups s n).pc = s.pc + BitVec.ofNat 64 (12*n) := by
  induction n with
  | zero => simp [maskGroups]
  | succ n ih =>
    rw [maskGroups, mask_group_pc, ih, BitVec.add_assoc, show (12 : Word) = BitVec.ofNat 64 12 from rfl, pc_add]
    congr 2

theorem mask_groups_reg (s : MachineState) (n : Nat) (r : Reg) (h : r ≠ .x26) :
    (maskGroups s n).getReg r = s.getReg r := by
  induction n with
  | zero => rfl
  | succ n ih => rw [maskGroups, mask_group_reg _ _ _ h, ih]

theorem mask_groups_run (s : MachineState) (n : Nat) (hn : n ≤ 16)
    (pc : s.pc = BitVec.ofNat 64 (4096+4*233329))
    (valid : ∀ u < 16, accessValid (s.getReg .x23 + BitVec.ofNat 64 (16*u)) 8 = true) (fuel : Nat) :
    execute packedWideCommitImage (3*n+fuel) s true =
      (do let r ← execute packedWideCommitImage fuel (maskGroups s n) true
          return r.charge (3*n) 0) := by
  induction n generalizing fuel with
  | zero => simp [maskGroups, Execution.charge]
  | succ n ih =>
    rw [show 3*(n+1)+fuel = 3*n+(3+fuel) by omega, ih (by omega) (3+fuel)]
    have gpc : (maskGroups s n).pc = BitVec.ofNat 64 (4096+4*(233329+3*n)) := by
      rw [mask_groups_pc, pc, pc_add]
      congr 1
      omega
    have gvalid := valid n (by omega)
    rw [← mask_groups_reg s n .x23 (by decide)] at gvalid
    rw [mask_group_run _ n (by omega) gpc gvalid fuel]
    simp only [maskGroups, bind_assoc, pure_bind, Execution.charge]
    apply bind_congr
    intro r
    congr 2 <;> omega

theorem mask_groups_masked (orig s : MachineState) (j n : Nat) (hn : n ≤ 16)
    (before : MaskedUpTo orig (16*j) s)
    (cursor : s.getReg .x23 = BitVec.ofNat 64 (maskCursor j)) (hj : j < 1048576)
    (mask : s.getReg .x25 = maskWord) :
    MaskedUpTo orig (16*j+n) (maskGroups s n) := by
  induction n with
  | zero => simpa [maskGroups] using before
  | succ n ih =>
    simp only [maskGroups]
    apply mask_group_masked orig _ n (16*j+n) (by omega) (ih (by omega))
    · rw [mask_groups_reg s n .x23 (by decide), cursor, pc_add]
      have small : maskCursor j + 16*n < 2^64 := by unfold maskCursor nonceChainBase; omega
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
      unfold maskCursor
      omega
    · rw [mask_groups_reg s n .x25 (by decide), mask]

attribute [local irreducible] maskGroups

/-! ### One iteration -/

def maskIter (s : MachineState) : MachineState := maskTailOps.foldl execInstrBr (maskGroups s 16)

structure MaskFrame (s : MachineState) (j : Nat) : Prop where
  pc : s.pc = BitVec.ofNat 64 (4096+4*233329)
  cursor : s.getReg .x23 = BitVec.ofNat 64 (maskCursor j)
  stop : s.getReg .x24 = BitVec.ofNat 64 (maskCursor 1048576)
  mask : s.getReg .x25 = maskWord

/-- The tail: advance the cursor, then branch back unless the cursor reached the end. -/
private theorem iter_eq (s : MachineState) :
    let g := maskGroups s 16
    let t := (g.setReg .x23 (g.getReg .x23 + signExtend12 256)).setPC (g.pc + 4)
    maskIter s = if t.getReg .x23 = t.getReg .x24 then t.setPC (t.pc + 4) else t.setPC (t.pc + signExtend13 7996) := by
  simp only [maskIter, maskTailOps, List.foldl]
  rw [bne_step]
  rfl

theorem mask_iter_cursor (s : MachineState) (j : Nat) (h : MaskFrame s j) :
    (maskIter s).getReg .x23 = BitVec.ofNat 64 (maskCursor (j+1)) := by
  have base := mask_groups_reg s 16 .x23 (by decide)
  have next : (maskGroups s 16).getReg .x23 + signExtend12 256 = BitVec.ofNat 64 (maskCursor (j+1)) := by
    rw [base, h.cursor, show signExtend12 256 = BitVec.ofNat 64 256 from rfl, pc_add]
    congr 1
  rw [iter_eq]
  split <;> simp <;> exact next

theorem mask_iter_reg (s : MachineState) (r : Reg) (a : r ≠ .x23) (b : r ≠ .x26) :
    (maskIter s).getReg r = s.getReg r := by
  have base := mask_groups_reg s 16 r b
  rw [iter_eq]
  split <;> simp [Ne.symm a, base]

theorem mask_iter_mem (s : MachineState) (b : Word) : (maskIter s).getMem b = (maskGroups s 16).getMem b := by
  rw [iter_eq]
  split <;> simp

private theorem cursor_ne (j : Nat) (hj : j+1 < 1048576) :
    BitVec.ofNat 64 (maskCursor (j+1)) ≠ BitVec.ofNat 64 (maskCursor 1048576) := by
  intro same
  have small : maskCursor (j+1) < 2^64 := by unfold maskCursor nonceChainBase; omega
  have big : maskCursor 1048576 < 2^64 := by unfold maskCursor nonceChainBase; omega
  have := congrArg BitVec.toNat same
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt big] at this
  unfold maskCursor at this
  omega

theorem mask_iter_pc (s : MachineState) (j : Nat) (h : MaskFrame s j) (hj : j < 1048576) :
    (maskIter s).pc = if j+1 < 1048576 then BitVec.ofNat 64 (4096+4*233329)
      else BitVec.ofNat 64 (4096+4*233379) := by
  have x24 := mask_groups_reg s 16 .x24 (by decide)
  have gpc := mask_groups_pc s 16
  rw [h.pc, pc_add] at gpc
  have cur := mask_iter_cursor s j h
  have next : (maskGroups s 16).getReg .x23 + signExtend12 256 = BitVec.ofNat 64 (maskCursor (j+1)) := by
    rw [mask_groups_reg s 16 .x23 (by decide), h.cursor, show signExtend12 256 = BitVec.ofNat 64 256 from rfl, pc_add]
    congr 1
  rw [iter_eq]
  simp only [MachineState.getReg_setPC, reg_set_eq _ _ _ (by decide : Reg.x23 ≠ .x0),
    reg_set_ne _ _ _ _ (by decide : Reg.x23 ≠ .x24), next, x24, h.stop, set_pc_pc, gpc]
  by_cases more : j+1 < 1048576
  · rw [if_neg (cursor_ne j more), if_pos more]
    simp only [set_pc_pc]
    decide
  · have eq : j+1 = 1048576 := by omega
    rw [eq, if_pos rfl, if_neg (by decide)]
    simp only [set_pc_pc]
    decide

theorem mask_iter_run (s : MachineState) (j : Nat) (h : MaskFrame s j) (hj : j < 1048576) (fuel : Nat) :
    execute packedWideCommitImage (50+fuel) s true =
      (do let r ← execute packedWideCommitImage fuel (maskIter s) true
          return r.charge 50 0) := by
  have valid (u : Nat) (hu : u < 16) : accessValid (s.getReg .x23 + BitVec.ofNat 64 (16*u)) 8 = true := by
    rw [h.cursor]
    exact mask_cursor_valid j u hj hu
  have gpc : (maskGroups s 16).pc = BitVec.ofNat 64 (4096+4*233377) := by
    rw [mask_groups_pc, h.pc, pc_add]
  have tail : ∀ g : MachineState, g.pc = BitVec.ofNat 64 (4096+4*233377) →
      execute packedWideCommitImage (2+fuel) g true =
      (do let r ← execute packedWideCommitImage fuel (maskTailOps.foldl execInstrBr g) true
          return r.charge 2 0) := by
    intro g gpc
    apply execute_unit_steps (states := fun i => (maskTailOps.take i).foldl execInstrBr g)
    intro i hi
    refine ⟨.base ((maskTailOps[i]?).getD .EBREAK),?_,?_,?_⟩
    · apply packed_wide_fetch_decoded _ (233377+i) (by omega)
      · interval_cases i
        · simp only [List.take, List.foldl]
          exact gpc
        · simp only [maskTailOps, List.take, List.foldl, execInstrBr, set_pc_pc, gpc]
          decide
      · exact mask_tail_decoded ⟨i,hi⟩
    · interval_cases i
      · simp only [maskTailOps, List.take, List.foldl, List.getElem?_cons_zero, Option.getD_some, ordinaryStep,
          memoryArgumentsValid, memAccess, if_true]
      · simp only [maskTailOps, List.take, List.foldl, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.getD_some, ordinaryStep, memoryArgumentsValid, memAccess, if_true]
    · interval_cases i
      · rfl
      · rfl
  rw [show 50+fuel = 3*16+(2+fuel) by omega, mask_groups_run s 16 (by omega) h.pc valid, tail _ gpc]
  change _ = (do let r ← execute packedWideCommitImage fuel (maskTailOps.foldl execInstrBr (maskGroups s 16)) true
                 return r.charge 50 0)
  simp only [bind_assoc, pure_bind, Execution.charge]
  apply bind_congr
  intro r
  congr 2 <;> omega

theorem mask_iter_frame (s : MachineState) (j : Nat) (h : MaskFrame s j) (more : j+1 < 1048576) :
    MaskFrame (maskIter s) (j+1) := by
  refine ⟨?_, mask_iter_cursor s j h, ?_, ?_⟩
  · rw [mask_iter_pc s j h (by omega), if_pos more]
  · rw [mask_iter_reg s .x24 (by decide) (by decide), h.stop]
  · rw [mask_iter_reg s .x25 (by decide) (by decide), h.mask]

theorem mask_iter_masked (orig s : MachineState) (j : Nat) (h : MaskFrame s j) (hj : j < 1048576)
    (before : MaskedUpTo orig (16*j) s) : MaskedUpTo orig (16*(j+1)) (maskIter s) := by
  have groups := mask_groups_masked orig s j 16 (by omega) before h.cursor hj h.mask
  intro b
  rw [mask_iter_mem, groups b, show 16*j+16 = 16*(j+1) by omega]

/-! ### The loop -/

def maskLoop (s : MachineState) : Nat → MachineState
  | 0 => s
  | n+1 => maskLoop (maskIter s) n

theorem mask_loop_run (s : MachineState) (j n : Nat) (h : MaskFrame s j) (bound : j+n ≤ 1048576)
    (fuel : Nat) :
    execute packedWideCommitImage (50*n+fuel) s true =
      (do let r ← execute packedWideCommitImage fuel (maskLoop s n) true
          return r.charge (50*n) 0) := by
  induction n generalizing s j fuel with
  | zero => simp [maskLoop, Execution.charge]
  | succ n ih =>
    rw [show 50*(n+1)+fuel = 50+(50*n+fuel) by omega, mask_iter_run s j h (by omega)]
    by_cases last : n = 0
    · subst last
      simp [maskLoop, Execution.charge]
    · rw [ih (maskIter s) (j+1) (mask_iter_frame s j h (by omega)) (by omega)]
      simp only [maskLoop, bind_assoc, pure_bind, Execution.charge]
      apply bind_congr
      intro r
      congr 2 <;> omega

theorem mask_loop_facts (orig s : MachineState) (j n : Nat) (h : MaskFrame s j) (bound : j+n = 1048576)
    (before : MaskedUpTo orig (16*j) s) (positive : 0 < n) :
    MaskedUpTo orig (16*1048576) (maskLoop s n) ∧
    (maskLoop s n).pc = BitVec.ofNat 64 (4096+4*233379) ∧
    ∀ r, r ≠ .x23 → r ≠ .x26 → (maskLoop s n).getReg r = s.getReg r := by
  induction n generalizing s j with
  | zero => omega
  | succ n ih =>
    simp only [maskLoop]
    by_cases last : n = 0
    · subst last
      have jl : j+1 = 1048576 := by omega
      refine ⟨?_, ?_, fun r a b => ?_⟩
      · have m := mask_iter_masked orig s j h (by omega) before
        rw [jl] at m
        simpa [maskLoop] using m
      · simp only [maskLoop]
        rw [mask_iter_pc s j h (by omega), if_neg (by omega)]
      · exact mask_iter_reg s r a b
    · obtain ⟨m, p, r⟩ := ih (maskIter s) (j+1) (mask_iter_frame s j h (by omega)) (by omega)
        (mask_iter_masked orig s j h (by omega) before) (by omega)
      exact ⟨m, p, fun reg a b => (r reg a b).trans (mask_iter_reg s reg a b)⟩

attribute [local irreducible] maskLoop maskIter

/-! ### The whole pass -/

def maskPass (s : MachineState) : MachineState :=
  execInstrBr (maskLoop (maskSetupOps.foldl execInstrBr s) 1048576) (.JAL .x0 1163700)

private theorem setup_frame (s : MachineState) (salts : s.getReg .x22 = BitVec.ofNat 64 nonceChainBase)
    (pc : s.pc = BitVec.ofNat 64 (4096+4*233324)) : MaskFrame (maskSetupOps.foldl execInstrBr s) 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [maskSetupOps, List.foldl, execInstrBr, set_pc_pc, set_reg_pc, pc]
    decide
  · simp [maskSetupOps, execInstrBr, salts]
    decide
  · simp [maskSetupOps, execInstrBr, salts]
    decide
  · simp [maskSetupOps, execInstrBr]
    decide

private theorem setup_mem (s : MachineState) (b : Word) : (maskSetupOps.foldl execInstrBr s).getMem b = s.getMem b := by
  simp [maskSetupOps, execInstrBr]

private theorem setup_masked (s : MachineState) : MaskedUpTo s (16*0) (maskSetupOps.foldl execInstrBr s) := by
  intro b
  have no : ¬ MaskedSalt (16*0) b := by unfold MaskedSalt; omega
  rw [if_neg no, setup_mem]

theorem mask_pass_run (s : MachineState) (pc : s.pc = BitVec.ofNat 64 (4096+4*233324))
    (salts : s.getReg .x22 = BitVec.ofNat 64 nonceChainBase) (fuel : Nat) :
    execute packedWideCommitImage (52428806+fuel) s true =
      (do let r ← execute packedWideCommitImage fuel (maskPass s) true
          return r.charge 52428806 0) := by
  have frame := setup_frame s salts pc
  have setup : execute packedWideCommitImage (5+(50*1048576+(1+fuel))) s true =
      (do let r ← execute packedWideCommitImage (50*1048576+(1+fuel)) (maskSetupOps.foldl execInstrBr s) true
          return r.charge 5 0) := by
    apply execute_unit_steps (states := fun i => (maskSetupOps.take i).foldl execInstrBr s)
    intro i hi
    refine ⟨.base ((maskSetupOps[i]?).getD .EBREAK),?_,?_,?_⟩
    · apply packed_wide_fetch_decoded _ (233324+i) (by omega)
      · interval_cases i <;> simp [maskSetupOps, execInstrBr, pc] <;> rfl
      · exact mask_setup_decoded ⟨i,hi⟩
    · interval_cases i <;> rfl
    · interval_cases i <;> rfl
  have facts := mask_loop_facts s _ 0 1048576 frame (by omega) (setup_masked s) (by decide)
  rw [show 52428806+fuel = 5+(50*1048576+(1+fuel)) by omega, setup,
    mask_loop_run _ 0 1048576 frame (by omega)]
  have jump := execute_ordinary_step packedWideCommitImage (.base (.JAL .x0 1163700))
    (maskLoop (maskSetupOps.foldl execInstrBr s) 1048576) (maskPass s) fuel true
    (packed_wide_fetch_decoded _ 233379 (by omega) facts.2.1 _ mask_exit_decoded) rfl
  rw [Nat.add_comm 1 fuel, jump]
  simp only [bind_assoc, pure_bind, Execution.charge, instructionCycles]
  apply bind_congr
  intro r
  congr 2 <;> omega

theorem mask_pass_pc (s : MachineState) (pc : s.pc = BitVec.ofNat 64 (4096+4*233324))
    (salts : s.getReg .x22 = BitVec.ofNat 64 nonceChainBase) :
    (maskPass s).pc = 4160 := by
  have facts := mask_loop_facts s _ 0 1048576 (setup_frame s salts pc) (by omega) (setup_masked s) (by decide)
  simp only [maskPass, execInstrBr, set_pc_pc, facts.2.1]
  decide

theorem mask_pass_reg (s : MachineState) (pc : s.pc = BitVec.ofNat 64 (4096+4*233324))
    (salts : s.getReg .x22 = BitVec.ofNat 64 nonceChainBase) (r : Reg)
    (a : r ≠ .x23) (b : r ≠ .x24) (c : r ≠ .x25) (d : r ≠ .x26) :
    (maskPass s).getReg r = s.getReg r := by
  have facts := mask_loop_facts s _ 0 1048576 (setup_frame s salts pc) (by omega) (setup_masked s) (by decide)
  have jal : ∀ t : MachineState, (execInstrBr t (.JAL .x0 1163700)).getReg r = t.getReg r := by
    intro t
    show ((t.setReg .x0 (t.pc + 4)).setPC (t.pc + signExtend21 1163700)).getReg r = t.getReg r
    rw [MachineState.getReg_setPC, set_x0]
  rw [maskPass, jal, facts.2.2 r a d]
  simp [maskSetupOps, execInstrBr, Ne.symm a, Ne.symm b, Ne.symm c]

theorem mask_pass_mem (s : MachineState) (pc : s.pc = BitVec.ofNat 64 (4096+4*233324))
    (salts : s.getReg .x22 = BitVec.ofNat 64 nonceChainBase) :
    MaskedUpTo s (16*1048576) (maskPass s) := by
  have facts := mask_loop_facts s _ 0 1048576 (setup_frame s salts pc) (by omega) (setup_masked s) (by decide)
  intro b
  have jal : ∀ t : MachineState, (execInstrBr t (.JAL .x0 1163700)).getMem b = t.getMem b := by
    intro t
    show ((t.setReg .x0 (t.pc + 4)).setPC (t.pc + signExtend21 1163700)).getMem b = t.getMem b
    rw [set_pc_get_mem, set_x0]
  rw [maskPass, jal]
  exact facts.1 b

end TwoPermutationPrototype.RV64.Chain
