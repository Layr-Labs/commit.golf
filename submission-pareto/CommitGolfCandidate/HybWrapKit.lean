import CommitGolfCandidate.HybWrapCode
import CommitGolfCandidate.QOpeningBlocks

/-! Execution kit for the hybrid wrapper: observed runs (`Obs`) under a fixed oracle, composed
sequentially; straight-line blocks through `CheckActions`; branch and jump steps; and the copy and
clear blocks with their register and memory effects. -/

namespace TwoPermutationPrototype.HybWrap
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Checker TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.CheckActions

set_option maxHeartbeats 1500000

/-! ### Observed runs -/

/-- From `s`, `steps` machine steps reach `t`, charging `cycles` cycles and `calls` oracle calls and
recording `rows` first. -/
def Obs (o : Oracle) (img : Image) (s t : MachineState) (steps cycles calls : Nat) (rows : List PublicRow) : Prop :=
  ∀ fuel, checkEvaluation o (recordRows (execute img (steps+fuel) s false)) =
    (((checkEvaluation o (recordRows (execute img fuel t false))).1.1.charge cycles calls,
      rows ++ (checkEvaluation o (recordRows (execute img fuel t false))).1.2),
     calls + (checkEvaluation o (recordRows (execute img fuel t false))).2)

theorem Obs.refl (o : Oracle) (img : Image) (s : MachineState) : Obs o img s s 0 0 0 [] := by
  intro fuel
  rw [Nat.zero_add]
  generalize checkEvaluation o (recordRows (execute img fuel s false)) = tl
  obtain ⟨⟨⟨e, st, cy, ca⟩, rows⟩, n⟩ := tl
  simp [Execution.charge]

theorem Obs.trans {o : Oracle} {img : Image} {s t u : MachineState} {a b c d q q' : Nat} {R R' : List PublicRow}
    (first : Obs o img s t a c q R) (last : Obs o img t u b d q' R') :
    Obs o img s u (a+b) (c+d) (q+q') (R++R') := by
  intro fuel
  rw [Nat.add_assoc, first (b+fuel), last fuel]
  generalize checkEvaluation o (recordRows (execute img fuel u false)) = tl
  obtain ⟨⟨⟨e, st, cy, ca⟩, rows⟩, n⟩ := tl
  simp only [Execution.charge, List.append_assoc, Prod.mk.injEq, Execution.mk.injEq, true_and, and_true]
  refine ⟨⟨by omega, by omega⟩, by omega⟩

theorem Obs.cast {o : Oracle} {img : Image} {s t : MachineState} {a c q a' c' q' : Nat} {R R' : List PublicRow}
    (h : Obs o img s t a c q R) (ha : a = a') (hc : c = c') (hq : q = q') (hR : R = R') : Obs o img s t a' c' q' R' := by
  subst ha hc hq hR; exact h

/-- A straight-line action block. -/
theorem Obs.ops (o : Oracle) (img : Image) (ops : List Action) (index : Nat) (s : MachineState)
    (pc : s.pc = BitVec.ofNat 64 (4096 + 4 * index)) (cells : fetchOps img index ops) (ok : validFixed o ops s) :
    Obs o img s (fixedOps o ops s) ops.length (opCycles ops) (opCalls ops) (opsRows o ops s) := by
  intro fuel
  rw [observe_ops o img ops index fuel s pc cells ok]

/-- One ordinary step (a branch or jump). -/
theorem Obs.step (o : Oracle) (img : Image) (s t : MachineState) (instr : Instr)
    (cell : fetch img s = some (.base instr)) (stepped : ordinaryStep s (.base instr) = some t) :
    Obs o img s t 1 (instructionCycles (.base instr)) 0 [] := by
  intro fuel
  rw [Nat.add_comm 1 fuel, execute_ordinary_step img (.base instr) s t fuel false cell stepped, bind_pure_comp,
    check_recorded_map]
  simp

/-- A deterministic stretch (no oracle call) is observed with no calls and no rows. -/
theorem Obs.of_runs (o : Oracle) (img : Image) (s t : MachineState) (steps cycles : Nat)
    (runs : ∀ fuel, execute img (steps+fuel) s false = (do let r ← execute img fuel t false; return r.charge cycles 0)) :
    Obs o img s t steps cycles 0 [] := by
  intro fuel
  rw [runs fuel, bind_pure_comp, check_recorded_map]
  simp

/-! ### Fetching wrapper words -/

/-- `code` sits at wrapper offset `off` (absolute word `464 + off`). -/
def WrapAt (off : Nat) (code : List Instr) : Prop := ∀ i < code.length, wrapCode[off+i]? = code[i]?

instance (off : Nat) (code : List Instr) : Decidable (WrapAt off code) := by unfold WrapAt; infer_instance

theorem wrap_fetch {img : Image} (wrap : WrapImage img) (state : MachineState) (i : Nat)
    (instruction : Instr) (code : wrapCode[i]? = some instruction)
    (pc : state.pc = BitVec.ofNat 64 (4096+4*(464+i))) :
    fetch img state = some (.base instruction) := by
  have bounded : i < 2957 := by
    rw [← wrap_code_length]
    exact (List.getElem?_eq_some_iff.mp code).1
  have decoded := wrap.words i bounded
  rw [code] at decoded
  have numeric : state.pc.toNat = 4096+4*(464+i) := by
    rw [pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  rw [fetch, numeric, ite_eq_left (by omega), show (4096+4*(464+i)-4096)/4 = 464+i by omega]
  cases entry : img.code[464+i]? with
  | none => simp [entry] at decoded
  | some word => simpa only [entry, Option.bind_some, Option.map_some] using decoded

theorem wrap_at_fetch {img : Image} (wrap : WrapImage img) {off : Nat} {code : List Instr} (at_ : WrapAt off code)
    (i : Nat) (hi : i < code.length) (state : MachineState) (pc : state.pc = BitVec.ofNat 64 (4096+4*(464+(off+i)))) :
    fetch img state = some (.base code[i]) :=
  wrap_fetch wrap state (off+i) _ (by rw [at_ i hi, List.getElem?_eq_getElem hi]) pc

theorem wrap_fetch_ops {img : Image} (wrap : WrapImage img) {off : Nat} {code : List Instr} (at_ : WrapAt off code)
    (ops : List Action) (same : ops.map Action.op = code) : fetchOps img (464+off) ops := by
  intro i s pc
  have hi : i.val < code.length := by rw [← same, List.length_map]; exact i.isLt
  have e : ops[i].op = code[i.val] := by
    have := congrArg (fun l => l[i.val]?) same
    simp only [List.getElem?_map, List.getElem?_eq_getElem i.isLt, List.getElem?_eq_getElem hi, Option.map_some,
      Option.some.injEq] at this
    exact this
  rw [e]
  exact wrap_at_fetch wrap at_ i.val hi s (by rw [pc, Nat.add_assoc])

theorem wrap_at_split {off : Nat} {a b : List Instr} (at_ : WrapAt off (a ++ b)) : WrapAt off a ∧ WrapAt (off+a.length) b := by
  constructor
  · intro i hi
    rw [at_ i (by simp; omega), List.getElem?_append_left hi]
  · intro i hi
    rw [Nat.add_assoc, at_ (a.length+i) (by simp; omega), List.getElem?_append_right (by omega),
      Nat.add_sub_cancel_left]

/-! ### Single actions -/

@[simp] theorem reg_zero (s : MachineState) : s.getReg .x0 = 0#64 := rfl

theorem put_reg_reg (s : MachineState) (rd r : Reg) (v : Word) :
    (putReg s rd v).getReg r = if rd = r ∧ rd ≠ .x0 then v else s.getReg r := by
  unfold putReg
  rw [MachineState.getReg_setPC, QOpening.getReg_setReg]

theorem put_word_reg (s : MachineState) (a : Nat) (v : Word) (r : Reg) : (putWord s a v).getReg r = s.getReg r := by
  unfold putWord
  rw [MachineState.getReg_setPC, QOpening.getReg_setMem]

theorem set_reg_mem (state : MachineState) (reg : Reg) (value : Word) :
    (state.setReg reg value).mem = state.mem := by cases reg <;> rfl

theorem put_reg_view (s : MachineState) (rd : Reg) (v : Word) : memoryView (putReg s rd v) = memoryView s := by
  funext w
  unfold putReg memoryView
  change (s.setReg rd v).mem _ = s.mem _
  rw [set_reg_mem]

theorem put_word_view (s : MachineState) (a w : Nat) (v : Word) (ha : a < 2^61) (hw : w < 2^61) :
    memoryView (putWord s a v) w = if w = a then v else memoryView s w := by
  unfold putWord
  rw [memory_view_set_pc', memory_at_store ha hw]
  unfold writeWord
  rfl
where memory_view_set_pc' (t : MachineState) (p : Word) : memoryView (t.setPC p) = memoryView t := rfl

theorem perm_view (o : Oracle) (s : MachineState) (src dst w : Nat) (hd : dst + 25 ≤ 2^33) (hw : w < 2^33) :
    memoryView (fixedStep o s (.perm src dst)) w =
      writeWindow (memoryView s) dst (replyWords (o.permutation (packBuffer (window (memoryView s) src)))) w :=
  permutation_write_memory s dst w _ hd hw

theorem perm_reg (o : Oracle) (s : MachineState) (src dst : Nat) (r : Reg) :
    (fixedStep o s (.perm src dst)).getReg r = s.getReg r := writeBits_register _ _ _ _

theorem validFixed_append (o : Oracle) (a b : List Action) (s : MachineState) :
    validFixed o (a ++ b) s ↔ validFixed o a s ∧ validFixed o b (fixedOps o a s) := by
  induction a generalizing s with
  | nil => simp [validFixed, fixedOps]
  | cons x rest ih =>
    simp only [List.cons_append, validFixed, ih, fixedOps, List.foldl_cons, and_assoc]

theorem fixedOps_append (o : Oracle) (a b : List Action) (s : MachineState) :
    fixedOps o (a ++ b) s = fixedOps o b (fixedOps o a s) := by
  unfold fixedOps; rw [List.foldl_append]

theorem fixed_ops_pc (o : Oracle) (ops : List Action) (s : MachineState) :
    (fixedOps o ops s).pc = s.pc + BitVec.ofNat 64 (4*ops.length) := by
  induction ops generalizing s with
  | nil => simp [fixedOps]
  | cons a rest ih =>
    simp only [fixedOps, List.foldl_cons] at ih ⊢
    rw [ih, fixed_pc, BitVec.add_assoc]
    congr 1
    rw [show (4 : Word) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_add]
    congr 1
    simp; omega

theorem pc_after (s : MachineState) (index n : Nat) (pc : s.pc = BitVec.ofNat 64 (4096+4*index)) :
    s.pc + BitVec.ofNat 64 (4*n) = BitVec.ofNat 64 (4096+4*(index+n)) := by
  rw [pc, ← BitVec.ofNat_add]; congr 1; omega

/-! ### Immediates and arithmetic -/

theorem sext_small (x : Nat) (small : x < 2048) : signExtend12 (BitVec.ofNat 12 x) = BitVec.ofNat 64 x := by
  unfold signExtend12
  rw [BitVec.signExtend_eq_setWidth_of_msb_false (by
      rw [BitVec.msb_eq_false_iff_two_mul_lt,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)];omega),
    BitVec.setWidth_ofNat_of_le_of_lt (by decide) (by omega)]

theorem add_small (a x : Nat) (hx : x < 2048) (ha : a + x < 2^64) :
    BitVec.ofNat 64 a + signExtend12 (BitVec.ofNat 12 x) = BitVec.ofNat 64 (a+x) := by
  rw [sext_small x hx, ← BitVec.ofNat_add]

theorem add_neg (a x : Nat) (hs : signExtend12 (BitVec.ofNat 12 x) = BitVec.ofNat 64 (2^64 - (4096 - x)))
    (h2 : x < 4096) (ha : 4096 - x ≤ a) (hb : a < 2^64) :
    BitVec.ofNat 64 a + signExtend12 (BitVec.ofNat 12 x) = BitVec.ofNat 64 (a-(4096-x)) := by
  rw [hs, ← BitVec.ofNat_add]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega

theorem word_add (a b : Nat) (h : a + b < 2^64) : BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a+b) := by
  rw [← BitVec.ofNat_add]

theorem word_sub (a b : Nat) (h : b ≤ a) (ha : a < 2^64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a-b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : b < 2^64), Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (by omega : a - b < 2^64)]
  omega

theorem word_mul (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) :
    BitVec.ofNat 64 a * BitVec.ofNat 64 b = BitVec.ofNat 64 (a*b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

/-! ### Blocks without oracle calls -/

def PermFree (ops : List Action) : Prop := ∀ a ∈ ops, a.calls = 0

theorem perm_free_rows (o : Oracle) : ∀ (ops : List Action) (s : MachineState), PermFree ops → opsRows o ops s = []
  | [], _, _ => rfl
  | a :: rest, s, free => by
    have ha := free a (by simp)
    have tail := perm_free_rows o rest (fixedStep o s a) (fun b hb => free b (by simp [hb]))
    simp only [opsRows, tail, List.append_nil]
    cases a <;> simp_all [stepRows, Action.calls]

theorem perm_free_calls : ∀ (ops : List Action), PermFree ops → opCalls ops = 0
  | [], _ => rfl
  | a :: rest, free => by
    have ha := free a (by simp)
    have tail := perm_free_calls rest (fun b hb => free b (by simp [hb]))
    simp only [opCalls, List.map_cons, List.sum_cons] at tail ⊢
    rw [ha, tail]

theorem perm_free_append {a b : List Action} (ha : PermFree a) (hb : PermFree b) : PermFree (a ++ b) := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact ha x h
  · exact hb x h

/-- A straight-line block without oracle calls. -/
theorem Obs.free (o : Oracle) (img : Image) (ops : List Action) (index : Nat) (s : MachineState)
    (pc : s.pc = BitVec.ofNat 64 (4096 + 4 * index)) (cells : fetchOps img index ops) (ok : validFixed o ops s)
    (free : PermFree ops) :
    Obs o img s (fixedOps o ops s) ops.length (opCycles ops) 0 [] :=
  (Obs.ops o img ops index s pc cells ok).cast rfl rfl (perm_free_calls ops free) (perm_free_rows o ops s free)

/-! ### Register-only actions -/

theorem alu_add (s : MachineState) (rd a b : Reg) (result : Word) (h : s.getReg a + s.getReg b = result) :
    (Action.alu (.ADD rd a b) rd result).valid s := by subst h; rfl
theorem alu_sub (s : MachineState) (rd a b : Reg) (result : Word) (h : s.getReg a - s.getReg b = result) :
    (Action.alu (.SUB rd a b) rd result).valid s := by subst h; rfl
theorem alu_mul (s : MachineState) (rd a b : Reg) (result : Word) (h : s.getReg a * s.getReg b = result) :
    (Action.alu (.MUL rd a b) rd result).valid s := by subst h; rfl
theorem alu_divu (s : MachineState) (rd a b : Reg) (result : Word) (h : rv64_divu (s.getReg a) (s.getReg b) = result) :
    (Action.alu (.DIVU rd a b) rd result).valid s := by subst h; rfl
theorem alu_remu (s : MachineState) (rd a b : Reg) (result : Word) (h : rv64_remu (s.getReg a) (s.getReg b) = result) :
    (Action.alu (.REMU rd a b) rd result).valid s := by subst h; rfl
theorem alu_andi (s : MachineState) (rd a : Reg) (imm : BitVec 12) (result : Word)
    (h : s.getReg a &&& signExtend12 imm = result) : (Action.alu (.ANDI rd a imm) rd result).valid s := by subst h; rfl
theorem alu_srli (s : MachineState) (rd a : Reg) (sh : BitVec 6) (result : Word)
    (h : s.getReg a >>> sh.toNat = result) : (Action.alu (.SRLI rd a sh) rd result).valid s := by subst h; rfl
theorem alu_slli (s : MachineState) (rd a : Reg) (sh : BitVec 6) (result : Word)
    (h : s.getReg a <<< sh.toNat = result) : (Action.alu (.SLLI rd a sh) rd result).valid s := by subst h; rfl

theorem word_divu (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) (pos : 0 < b) :
    rv64_divu (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = BitVec.ofNat 64 (a/b) := by
  unfold rv64_divu
  have nz : BitVec.ofNat 64 b ≠ 0#64 := by
    intro h; have := congrArg BitVec.toNat h; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb] at this
    simp at this; omega
  simp only [beq_iff_eq]
  rw [if_neg nz]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_udiv]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) ha)]

theorem word_remu (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) (pos : 0 < b) :
    rv64_remu (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = BitVec.ofNat 64 (a%b) := by
  unfold rv64_remu
  have nz : BitVec.ofNat 64 b ≠ 0#64 := by
    intro h; have := congrArg BitVec.toNat h; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb] at this
    simp at this; omega
  simp only [beq_iff_eq]
  rw [if_neg nz]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.mod_le _ _) ha)]

theorem word_and_one (a : Nat) (ha : a < 2^64) :
    BitVec.ofNat 64 a &&& signExtend12 (BitVec.ofNat 12 1) = BitVec.ofNat 64 (a%2) := by
  rw [sext_small 1 (by decide)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    show 1 % 2^64 = 1 from rfl, Nat.and_one_is_mod, Nat.mod_eq_of_lt (by omega : a % 2 < 2^64)]

theorem word_shr (a n : Nat) (ha : a < 2^64) : BitVec.ofNat 64 a >>> n = BitVec.ofNat 64 (a/2^n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) ha)]

theorem word_shl (a n : Nat) (h : a*2^n < 2^64) : BitVec.ofNat 64 a <<< n = BitVec.ofNat 64 (a*2^n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft]
  have ha : a < 2^64 := lt_of_le_of_lt (Nat.le_mul_of_pos_right a (Nat.two_pow_pos n)) h
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.shiftLeft_eq, Nat.mod_eq_of_lt h]

/-! ### Two-instruction constants -/

def LiOK (v : Nat) : Prop :=
  ((hi20 v).zeroExtend 32 <<< 12).signExtend 64 + signExtend12 (lo12 v) = BitVec.ofNat 64 v

instance (v : Nat) : Decidable (LiOK v) := by unfold LiOK; infer_instance

def liActs (rd : Reg) (v : Nat) : List Action :=
  [.lui rd (hi20 v) (((hi20 v).zeroExtend 32 <<< 12).signExtend 64), .offset rd rd (lo12 v) (BitVec.ofNat 64 v)]

theorem li_acts_op (rd : Reg) (v : Nat) : (liActs rd v).map Action.op = liCode rd v := rfl

theorem li_free (rd : Reg) (v : Nat) : PermFree (liActs rd v) := by
  intro x hx; simp [liActs] at hx; rcases hx with h | h <;> subst h <;> rfl

theorem li_run (o : Oracle) (s : MachineState) (rd : Reg) (v : Nat) (ok : LiOK v) (nz : rd ≠ .x0) :
    validFixed o (liActs rd v) s ∧ (fixedOps o (liActs rd v) s).getReg rd = BitVec.ofNat 64 v ∧
      (∀ r, r ≠ rd → (fixedOps o (liActs rd v) s).getReg r = s.getReg r) ∧
      memoryView (fixedOps o (liActs rd v) s) = memoryView s := by
  refine ⟨⟨rfl, ?_, trivial⟩, ?_, ?_, ?_⟩
  · show (putReg s rd _).getReg rd + _ = _
    rw [put_reg_reg, if_pos ⟨rfl, nz⟩]; exact ok
  · show (putReg (putReg s rd _) rd _).getReg rd = _
    rw [put_reg_reg, if_pos ⟨rfl, nz⟩]
  · intro r hr
    show (putReg (putReg s rd _) rd _).getReg r = _
    rw [put_reg_reg, if_neg (fun h => hr h.1.symm), put_reg_reg, if_neg (fun h => hr h.1.symm)]
  · show memoryView (putReg (putReg s rd _) rd _) = _
    rw [put_reg_view, put_reg_view]

end TwoPermutationPrototype.HybWrap
