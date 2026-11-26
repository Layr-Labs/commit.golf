import CommitGolfCandidate.PairImage
import CommitGolfCandidate.Check
import CommitGolfCandidate.PairStatic

namespace CommitGolfCandidate.PairCap
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 20000
private abbrev baseCheck := CommitGolfCandidate.submission.image .check

/-- Normal-mode code starts after the one changed branch. All return addresses
from its JAL instructions are aligned addresses in the inherited code. -/
private def pcOK (pc : Word) : Bool :=
  pc == 0 || (decide (4124 ≤ pc.toNat ∧ pc.toNat < 4984 ∧ pc.toNat % 4 = 0))

private structure Protected (s : MachineState) : Prop where
  pc : pcOK s.pc
  ra : pcOK (s.getReg .x1)
  t6 : pcOK (s.getReg .x31)

private def keep (rd : Reg) := rd != .x1 && rd != .x31

private def permitted (pc : Word) : Instruction → Bool
  | .base op =>
    match op with
    | .ADDI d .. | .SLLI d .. | .XORI d .. | .SRLI d .. | .ANDI d ..
    | .ADD d .. | .MUL d .. | .LD d .. => keep d && pcOK (pc+4)
    | .SD .. | .ECALL => pcOK (pc+4)
    | .BEQ _ _ off | .BNE _ _ off => pcOK (pc+4) && pcOK (pc+signExtend13 off)
    | .JAL _ off => pcOK (pc+4) && pcOK (pc+signExtend21 off)
    | .JALR d r off => decide (d = .x0 ∧ (r = .x1 ∨ r = .x31) ∧ off = 0)
    | _ => false
  | _ => false

private def validWord (word : BitVec 32) (i : Nat) : Bool :=
  if i < 7 then true
  else ((decodeInstruction word).map (permitted (BitVec.ofNat 64 (4096+4*i)))).getD false

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
private theorem wholeTable : baseCheck.code.zipIdx.all (fun (w,i) => validWord w i) = true := by decide

private theorem between (s : MachineState) (h : Protected s) (nz : s.pc ≠ 0) :
    4124 ≤ s.pc.toNat ∧ s.pc.toNat < 4984 ∧ s.pc.toNat % 4 = 0 := by
  have both : s.pc = 0#64 ∨ 4124 ≤ s.pc.toNat ∧ s.pc.toNat < 4984 ∧ s.pc.toNat % 4 = 0 := by simpa [pcOK] using h.pc
  exact both.resolve_left nz

private theorem fetchSame (s : MachineState) (h : Protected s) :
    fetch (submission.image .check) s = fetch baseCheck s := by
  by_cases hz : s.pc = 0
  · simp [fetch,hz]
  have b := between s h hz
  let i := (s.pc.toNat-4096)/4
  have lo : 7 ≤ i := by dsimp [i]; omega
  have hi : i < baseCheck.code.length := by change i < 222; dsimp [i]; omega
  have eqn : (submission.image .check).code[i]? = baseCheck.code[i]? := by
    change (baseCheck.code.set 6 _ ++ _)[i]? = _
    rw [List.getElem?_append_left (by simpa using hi), List.getElem?_set_ne (by omega)]
  unfold fetch
  rw [if_pos (by omega),if_pos (by omega)]; rw [eqn]

private theorem fetchPermitted (s : MachineState) (h : Protected s) {ins : Instruction}
    (found : fetch baseCheck s = some ins) : permitted s.pc ins := by
  by_cases hz : s.pc = 0
  · simp [fetch,hz] at found
  have b := between s h hz
  let i := (s.pc.toNat-4096)/4
  have lo : 7 ≤ i := by dsimp [i]; omega
  have hi : i < baseCheck.code.length := by change i < 222; dsimp [i]; omega
  have pc : BitVec.ofNat 64 (4096+4*i) = s.pc := by
    have r : 4096+4*i = s.pc.toNat := by dsimp [i]; omega
    simp [r]
  let word : BitVec 32 := baseCheck.code[i]
  have get : baseCheck.code[i]? = some word := List.getElem?_eq_getElem hi
  have mem : (word,i) ∈ baseCheck.code.zipIdx := List.mem_zipIdx_iff_getElem?.mpr get
  have safe := List.all_eq_true.mp wholeTable (word,i) mem
  unfold fetch at found
  rw [if_pos (by omega), get] at found
  simpa [validWord, show ¬ i < 7 by omega, found, pc] using safe

private theorem keepStep (s : MachineState) (h : Protected s) (d : Reg) (v : Word)
    (safe : keep d && pcOK (s.pc+4)) : Protected ((s.setReg d v).setPC (s.pc+4)) := by
  simp only [keep, Bool.and_eq_true, bne_iff_ne] at safe
  refine ⟨safe.2,?_,?_⟩
  · simpa only [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ safe.1.1] using h.ra
  · simpa only [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ safe.1.2] using h.t6

private theorem strip (w : Word) (ok : pcOK w) : w &&& ~~~1#64 = w := by
  by_cases zero : w = 0
  · subst w; decide
  have b : 4124 ≤ w.toNat ∧ w.toNat < 4984 ∧ w.toNat % 4 = 0 := by
    have both : w = 0#64 ∨ 4124 ≤ w.toNat ∧ w.toNat < 4984 ∧ w.toNat % 4 = 0 := by simpa [pcOK] using ok
    exact both.resolve_left zero
  have low : w &&& 1#64 = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    change w.toNat &&& (2^1-1) = 0
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  calc
    _ = (w &&& 1#64) ||| (w &&& ~~~1#64) := by rw [low, BitVec.zero_or]
    _ = w := by rw [← BitVec.and_or_distrib_left, BitVec.or_not_self, BitVec.and_allOnes]

private theorem controlStep (s : MachineState) (h : Protected s) {op : Instr}
    (permit : permitted s.pc (.base op)) : Protected (execInstrBr s op) := by
  cases op <;> simp only [permitted, Bool.false_eq_true] at permit
  all_goals try contradiction
  all_goals try exact keepStep s h _ _ permit
  all_goals try exact ⟨permit, h.ra, h.t6⟩
  all_goals try
    simp only [Bool.and_eq_true] at permit
    dsimp only [execInstrBr]
    split
    · exact ⟨permit.2,h.ra,h.t6⟩
    · exact ⟨permit.1,h.ra,h.t6⟩
  case JAL d off =>
    simp only [Bool.and_eq_true] at permit
    refine ⟨permit.2,?_,?_⟩
    · by_cases e : d = .x1
      · subst d; exact permit.1
      · simpa [execInstrBr,MachineState.getReg_setReg_ne _ _ _ _ e] using h.ra
    · by_cases e : d = .x31
      · subst d; exact permit.1
      · simpa [execInstrBr,MachineState.getReg_setReg_ne _ _ _ _ e] using h.t6
  case JALR d r off =>
    rw [decide_eq_true_eq] at permit
    rcases permit with ⟨rfl, rfl | rfl, rfl⟩
    · exact ⟨by change pcOK ((s.getReg .x1 + 0#64) &&& ~~~1#64); rw [BitVec.add_zero, strip _ h.ra]; exact h.ra,h.ra,h.t6⟩
    · exact ⟨by change pcOK ((s.getReg .x31 + 0#64) &&& ~~~1#64); rw [BitVec.add_zero, strip _ h.t6]; exact h.t6,h.ra,h.t6⟩

private theorem ordinaryProtected (s : MachineState) (h : Protected s) {ins : Instruction} {next : MachineState}
    (permit : permitted s.pc ins) (step : ordinaryStep s ins = some next) : Protected next := by
  cases ins with
  | word | sraiw => contradiction
  | base op =>
    have p := controlStep s h permit
    cases op <;> simp only [ordinaryStep, reduceCtorEq] at step
    all_goals first | contradiction | split at step <;> simp_all

private theorem oracleProtected (s : MachineState) (h : Protected s) (pc : pcOK (s.pc+4))
    (q : PublicSpec.Domain) (v : PublicSpec.Range q) :
    Protected (writeOracleAnswer s (s.getReg .x12) q v) := by
  rcases q with a|b|c <;> exact ⟨pc, (writeBits_register _ _ _ _).symm ▸ h.ra,
    (writeBits_register _ _ _ _).symm ▸ h.t6⟩

private theorem normalTail (n : Nat) (s : MachineState) (safe : Protected s) :
    execute (submission.image .check) n s false = execute baseCheck n s false := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [execute, fetchSame s safe, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    split
    · rfl
    · rename_i found
      split
      · split
        · rfl
        · apply bind_congr; intro reply
          rw [ih _ (oracleProtected s safe (fetchPermitted s safe found) _ reply)]
      · rfl
    · rename_i found
      split
      · rfl
      · rename_i step
        rw [ih _ (ordinaryProtected s safe (fetchPermitted s safe found) step)]

theorem patchedFetch (state : MachineState) (index : Nat) (instruction : Instr)
    (indexBound : index < 409) (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * index))
    (decoded : ((submission.image .check).code[index]?).bind decodeInstruction =
      some (.base instruction)) :
    fetch (submission.image .check) state = some (.base instruction) := by
  have pcNat : state.pc.toNat = 4096 + 4 * index := by
    rw [pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  rw [fetch, pcNat, if_pos (by omega)]
  have quotient : (4096 + 4 * index - 4096) / 4 = index := by omega
  rw [quotient]
  cases h : (submission.image .check).code[index]? with
  | none => simp [h] at decoded
  | some word => simpa [h] using decoded

/-! ### Entry dispatch (`k = 128` vs `k ≠ 128`) -/

def dispatchOps : List Instr :=
  [.ADDI .x26 .x11 0, .ADDI .x24 .x13 0, .ADDI .x8 .x14 0,
   .ADDI .x25 .x15 0, .ADDI .x27 .x16 0, .ADDI .x6 .x0 128]

def dispatchPrefix (state : MachineState) (count : Nat) : MachineState :=
  (dispatchOps.take count).foldl execInstrBr state

private theorem dispatchRun (state : MachineState) (pc : state.pc = 4096)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (6 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel
            (dispatchPrefix state 6) allowCoins
          return result.charge 6 0) := by
  apply execute_unit_steps (states := dispatchPrefix state)
  intro i hi
  refine ⟨.base ((dispatchOps[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply patchedFetch _ i _ (by omega)
    · interval_cases i <;>
        simp [dispatchPrefix, dispatchOps, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

/-- State after initial ABI register copy and dispatch on `x16 = 128` (`4984` for cap
mode, `4124` for normal mode). -/
def dispatched (state : MachineState) : MachineState :=
  (dispatchPrefix state 6).setPC (if state.getReg .x16 = 128 then 4984 else 4124)

theorem patchedDispatch (state : MachineState) (pc : state.pc = 4096)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (7 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel
            (dispatched state) allowCoins
          return result.charge 7 0) := by
  let ready := dispatchPrefix state 6
  have readyPC : ready.pc = 4120 := by
    simp [ready, dispatchPrefix, dispatchOps, execInstrBr, pc, MachineState.setPC]
  have ready27 : ready.getReg .x27 = state.getReg .x16 := by
    simp [ready, dispatchPrefix, dispatchOps, execInstrBr, signExtend12,
      MachineState.getReg, MachineState.setReg, MachineState.setPC]
  have ready6 : ready.getReg .x6 = 128 := by
    dsimp only [ready, dispatchPrefix, dispatchOps, List.take, List.foldl,
      execInstrBr, signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    simp
  have fetched : fetch (submission.image .check) ready = some (.base (.BEQ .x27 .x6 864)) := by
    apply patchedFetch ready 6 _ (by decide) readyPC; rfl
  have stepped : ordinaryStep ready (.base (.BEQ .x27 .x6 864)) = some (dispatched state) := by
    dsimp only [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr]
    rw [ready27, ready6, readyPC]
    simp [dispatched, ready, signExtend13]
    split <;> simp_all
  rw [show 7 + fuel = 6 + (fuel + 1) by omega, dispatchRun state pc]
  rw [execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  simp [instructionCycles, Execution.charge, ← Nat.add_assoc]


theorem check_normal_run (input : CheckInput) (normal : input.positions.card ≠ BATCH) :
    submission.run .check input = CommitGolfCandidate.submission.run .check input := by
  unfold Submission.run
  change (if decide (input.proof.length ≤ submission.sizes.proof) then _ else _) = _
  split
  next accepted =>
    have accepted' : decide (input.proof.length ≤ CommitGolfCandidate.submission.sizes.proof) = true := accepted
    simp only [accepted', ↓reduceIte]
    let initial := submission.initialState .check input
    have n : initial.getReg .x16 ≠ 128 := by
      intro eqn; apply normal
      change BitVec.ofNat 64 input.positions.card = 128 at eqn
      have b : input.positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
      have b' : input.positions.card < 2^64 := by change input.positions.card ≤ 16777216 at b; omega
      have h := congrArg BitVec.toNat eqn
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt b'] at h
      exact h.trans (by decide)
    have same : dispatched initial = checkDispatchState initial := by
      unfold dispatched checkDispatchState
      rw [if_neg n, if_neg n]; rfl
    have dispatchSafe : Protected (checkDispatchState initial) := by
      constructor
      · change pcOK (if initial.getReg .x16 = 128 then 4444 else 4124)
        rw [if_neg n]; decide
      · rfl
      · rfl
    change execute (submission.image .check) (7+214748365817) initial false =
      execute baseCheck (7+214748365817) initial false
    rw [patchedDispatch initial rfl, check_dispatch initial rfl, same, normalTail _ _ dispatchSafe]
  next rejected =>
    have h : ¬ decide (input.proof.length ≤ CommitGolfCandidate.submission.sizes.proof) = true := rejected
    change pure _ = if decide (input.proof.length ≤ CommitGolfCandidate.submission.sizes.proof) then _ else _
    rw [if_neg h]

end CommitGolfCandidate.PairCap
