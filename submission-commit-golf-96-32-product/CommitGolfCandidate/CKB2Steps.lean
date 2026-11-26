import CommitGolfCandidate.PairRegion
import CommitGolfCandidate.PairFinish
import CommitGolfCandidate.CKB2Half
import CommitGolfCandidate.CKB2Trunc

/-! (CKB2) Execution facts for the A96 batch pair loop at check words 699..813:
30-byte pair slots copied by halfwords, and the height-17 pair hash truncated by `sh x0,30(x24)`. -/
namespace CommitGolfCandidate.PairCap.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 12000
set_option maxHeartbeats 400000

theorem ckb2Fetch (state : MachineState) (index : Nat) (instruction : Instr)
    (indexBound : index < 814) (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * index))
    (decoded : (Late.Check.Normal.checkerImage.code[index]?).bind decodeInstruction =
      some (.base instruction)) :
    fetch Late.Check.Normal.checkerImage state = some (.base instruction) := by
  have pcNat : state.pc.toNat = 4096 + 4 * index := by
    rw [pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  rw [fetch, pcNat, if_pos (by omega)]
  have quotient : (4096 + 4 * index - 4096) / 4 = index := by omega
  rw [quotient]
  cases h : Late.Check.Normal.checkerImage.code[index]? with
  | none => simp [h] at decoded
  | some word => simpa [h] using decoded

private theorem ckb2SimpleStep (s : MachineState) (op : Instr) (isSimple : simple op)
    (mem : memoryArgumentsValid s op) :
    ordinaryStep s (.base op) = some (execInstrBr s op) ∧
      (execInstrBr s op).pc = s.pc + 4 ∧ instructionCycles (.base op) = 1 := by
  cases op <;> simp [simple] at isSimple <;> simp [ordinaryStep,mem,execInstrBr,instructionCycles,MachineState.setPC]

private theorem ckb2SimplePC (s : MachineState) (op : Instr) (isSimple : simple op) :
    (execInstrBr s op).pc = s.pc + 4 := by
  cases op <;> simp [simple] at isSimple <;> rfl

theorem ckb2Block (ops : List Instr) (start : Nat) (within : start+ops.length≤814)
    (plain : ∀ i : Fin ops.length, simple ops[i])
    (enc : ∀ i : Fin ops.length, (Late.Check.Normal.checkerImage.code[start+i.val]?).bind decodeInstruction =
      some (.base ops[i])) (s : MachineState) (pc : s.pc=BitVec.ofNat 64 (4096+4*start))
    (safe : safeSteps ops s) (fuel : Nat) (coins : Bool) :
    execute Late.Check.Normal.checkerImage (ops.length+fuel) s coins =
    (do let next ← execute Late.Check.Normal.checkerImage fuel (ops.foldl execInstrBr s) coins
        return next.charge ops.length 0) := by
  have succ (i : Nat) (hi : i<ops.length) : stepPrefix ops s (i+1) = execInstrBr (stepPrefix ops s i) ops[i] := by
    unfold stepPrefix; rw [List.take_succ_eq_append_getElem hi, List.foldl_append]; rfl
  have pcs (i : Nat) (bi : i ≤ ops.length) :
      (stepPrefix ops s i).pc = BitVec.ofNat 64 (4096+4*(start+i)) := by
    induction i with
    | zero => simpa [stepPrefix] using pc
    | succ i ih =>
      have pl : simple ops[i] := plain ⟨i,by omega⟩
      rw [succ i (by omega),ckb2SimplePC _ _ pl,ih (by omega),
        show 4096+4*(start+(i+1)) = (4096+4*(start+i))+4 by omega]
      exact (BitVec.ofNat_add (4096+4*(start+i)) 4).symm
  have run := execute_unit_steps Late.Check.Normal.checkerImage ops.length fuel (stepPrefix ops s) coins (by
    intro i hi
    refine ⟨.base ops[i],ckb2Fetch _ _ _ (by omega) (pcs i (by omega)) (enc ⟨i,hi⟩),?_,?_⟩
    · rw [succ i hi]; exact (ckb2SimpleStep _ _ (plain ⟨i,hi⟩) (safe ⟨i,hi⟩)).1
    · exact (ckb2SimpleStep _ _ (plain ⟨i,hi⟩) (safe ⟨i,hi⟩)).2.2)
  simpa only [stepPrefix,List.take_zero,List.foldl_nil,List.take_length] using run

/-- One instruction at word `n` with unit cost. -/
theorem ckb2One (o : Oracle) (s : MachineState) (n : Nat) (op : Instr) (hn : n<814)
    (pc : s.pc = BitVec.ofNat 64 (4096+4*n))
    (dec : (Late.Check.Normal.checkerImage.code[n]?).bind decodeInstruction = some (.base op))
    (step : ordinaryStep s (.base op) = some (execInstrBr s op)) (cyc : instructionCycles (.base op) = 1) :
    Runs o s (execInstrBr s op) 1 0 := by
  apply pureBlockRuns (cyc:=1)
  intro fuel
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ (ckb2Fetch s n op hn pc dec) step, cyc]

/-! ### Straight-line blocks -/

theorem ckb2MarksRun (s : MachineState) (pc : s.pc=6892) (safe : safeSteps marksOps s)
    (fuel : Nat) (coins : Bool) :
    execute Late.Check.Normal.checkerImage (2+fuel) s coins =
      (do let next ← execute Late.Check.Normal.checkerImage fuel (marksState s) coins
          return next.charge 2 0) :=
  ckb2Block marksOps 699 (by decide) (by decide) (by intro k; fin_cases k <;> rfl) s pc safe fuel coins

theorem ckb2HashSetupRun (s : MachineState) (pc : s.pc=7168) (fuel : Nat) (coins : Bool) :
    execute Late.Check.Normal.checkerImage (5+fuel) s coins =
      (do let next ← execute Late.Check.Normal.checkerImage fuel (hashSetupState s) coins
          return next.charge 5 0) :=
  ckb2Block hashSetupOps 768 (by decide) (by decide) (by intro k; fin_cases k <;> rfl) s pc
    (by intro k; fin_cases k <;> rfl) fuel coins

def ckb2NextOps : List Instr :=
  [.ADDI .x19 .x19 30, .ADDI .x22 .x22 2, .ADDI .x23 .x23 96, .ADDI .x24 .x24 32, .ADDI .x27 .x27 4095]

def ckb2NextState (s : MachineState) := ckb2NextOps.foldl execInstrBr s

theorem ckb2NextRun (s : MachineState) (pc : s.pc=7324) (fuel : Nat) (coins : Bool) :
    execute Late.Check.Normal.checkerImage (5+fuel) s coins =
      (do let next ← execute Late.Check.Normal.checkerImage fuel (ckb2NextState s) coins
          return next.charge 5 0) :=
  ckb2Block ckb2NextOps 807 (by decide) (by decide) (by intro k; fin_cases k <;> rfl) s pc
    (by intro k; fin_cases k <;> rfl) fuel coins

/-! ### Branches and jumps -/

theorem ckb2b701Yes (o : Oracle) (s : MachineState) (pc : s.pc=6900) (flag : s.getReg .x6 = 0#64) :
    Runs o s (s.setPC 7040) 1 0 := by
  have r := ckb2One o s 701 (.BEQ .x6 .x0 140) (by decide) pc (by rfl) (by rfl) (by rfl)
  have x0 : s.getReg .x0 = 0#64 := rfl
  have e : execInstrBr s (.BEQ .x6 .x0 140) = s.setPC 7040 := by
    simp only [execInstrBr,x0,beq_iff_eq,if_pos flag,pc]; rfl
  rwa [e] at r

theorem ckb2b701No (o : Oracle) (s : MachineState) (pc : s.pc=6900) (flag : s.getReg .x6 ≠ 0#64) :
    Runs o s (s.setPC 6904) 1 0 := by
  have r := ckb2One o s 701 (.BEQ .x6 .x0 140) (by decide) pc (by rfl) (by rfl) (by rfl)
  have x0 : s.getReg .x0 = 0#64 := rfl
  have e : execInstrBr s (.BEQ .x6 .x0 140) = s.setPC 6904 := by
    simp only [execInstrBr,x0,beq_iff_eq,if_neg flag,pc]; rfl
  rwa [e] at r

theorem ckb2b702Yes (o : Oracle) (s : MachineState) (pc : s.pc=6904) (flag : s.getReg .x7 = 0#64) :
    Runs o s (s.setPC 6912) 1 0 := by
  have r := ckb2One o s 702 (.BEQ .x7 .x0 8) (by decide) pc (by rfl) (by rfl) (by rfl)
  have x0 : s.getReg .x0 = 0#64 := rfl
  have e : execInstrBr s (.BEQ .x7 .x0 8) = s.setPC 6912 := by
    simp only [execInstrBr,x0,beq_iff_eq,if_pos flag,pc]; rfl
  rwa [e] at r

theorem ckb2b702No (o : Oracle) (s : MachineState) (pc : s.pc=6904) (flag : s.getReg .x7 ≠ 0#64) :
    Runs o s (s.setPC 6908) 1 0 := by
  have r := ckb2One o s 702 (.BEQ .x7 .x0 8) (by decide) pc (by rfl) (by rfl) (by rfl)
  have x0 : s.getReg .x0 = 0#64 := rfl
  have e : execInstrBr s (.BEQ .x7 .x0 8) = s.setPC 6908 := by
    simp only [execInstrBr,x0,beq_iff_eq,if_neg flag,pc]; rfl
  rwa [e] at r

theorem ckb2b736Yes (o : Oracle) (s : MachineState) (pc : s.pc=7040) (flag : s.getReg .x7 = 0#64) :
    Runs o s (s.setPC 7200) 1 0 := by
  have r := ckb2One o s 736 (.BEQ .x7 .x0 160) (by decide) pc (by rfl) (by rfl) (by rfl)
  have x0 : s.getReg .x0 = 0#64 := rfl
  have e : execInstrBr s (.BEQ .x7 .x0 160) = s.setPC 7200 := by
    simp only [execInstrBr,x0,beq_iff_eq,if_pos flag,pc]; rfl
  rwa [e] at r

theorem ckb2b736No (o : Oracle) (s : MachineState) (pc : s.pc=7040) (flag : s.getReg .x7 ≠ 0#64) :
    Runs o s (s.setPC 7044) 1 0 := by
  have r := ckb2One o s 736 (.BEQ .x7 .x0 160) (by decide) pc (by rfl) (by rfl) (by rfl)
  have x0 : s.getReg .x0 = 0#64 := rfl
  have e : execInstrBr s (.BEQ .x7 .x0 160) = s.setPC 7044 := by
    simp only [execInstrBr,x0,beq_iff_eq,if_neg flag,pc]; rfl
  rwa [e] at r

theorem ckb2j703 (o : Oracle) (s : MachineState) (pc : s.pc=6908) : Runs o s (s.setPC 7168) 1 0 := by
  have r := ckb2One o s 703 (.JAL .x0 260) (by decide) pc (by rfl) (by rfl) (by rfl)
  have e : execInstrBr s (.JAL .x0 260) = s.setPC 7168 := by
    simp only [execInstrBr,MachineState.setReg,pc]; rfl
  rwa [e] at r

theorem ckb2j735 (o : Oracle) (s : MachineState) (pc : s.pc=7036) : Runs o s (s.setPC 7168) 1 0 := by
  have r := ckb2One o s 735 (.JAL .x0 132) (by decide) pc (by rfl) (by rfl) (by rfl)
  have e : execInstrBr s (.JAL .x0 132) = s.setPC 7168 := by
    simp only [execInstrBr,MachineState.setReg,pc]; rfl
  rwa [e] at r

theorem ckb2j775 (o : Oracle) (s : MachineState) (pc : s.pc=7196) : Runs o s (s.setPC 7324) 1 0 := by
  have r := ckb2One o s 775 (.JAL .x0 128) (by decide) pc (by rfl) (by rfl) (by rfl)
  have e : execInstrBr s (.JAL .x0 128) = s.setPC 7324 := by
    simp only [execInstrBr,MachineState.setReg,pc]; rfl
  rwa [e] at r

theorem ckb2j813 (o : Oracle) (s : MachineState) (pc : s.pc=7348) : Runs o s (s.setPC 5492) 1 0 := by
  have r := ckb2One o s 813 (.JAL .x0 2095296) (by decide) pc (by rfl) (by rfl) (by rfl)
  have e : execInstrBr s (.JAL .x0 2095296) = s.setPC 5492 := by
    simp only [execInstrBr,MachineState.setReg,pc]; rfl
  rwa [e] at r

theorem ckb2j305 (o : Oracle) (s : MachineState) (pc : s.pc=5316) : Runs o s (s.setPC 6892) 1 0 := by
  have r := ckb2One o s 305 (.JAL .x0 1576) (by decide) pc (by rfl) (by rfl) (by rfl)
  have e : execInstrBr s (.JAL .x0 1576) = s.setPC 6892 := by
    simp only [execInstrBr,MachineState.setReg,pc]; rfl
  rwa [e] at r

theorem ckb2Edge812 (s : MachineState) (pc : s.pc=7344) (fuel : Nat) (coins : Bool) :
    execute Late.Check.Normal.checkerImage (fuel+1) s coins =
    (do let next ← execute Late.Check.Normal.checkerImage fuel (execInstrBr s (.BNE .x27 .x0 7740)) coins
        return next.charge 1 0) :=
  execute_ordinary_step _ _ _ _ _ _ (ckb2Fetch s 812 _ (by decide) pc (by rfl)) (by rfl)

/-! ### Zero halfword stores -/

theorem ckb2ShState (s : MachineState) (base : Reg) (off D : Nat) (reg : s.getReg base = BitVec.ofNat 64 D)
    (offB : off < 2048) :
    execInstrBr s (.SH base .x0 (BitVec.ofNat 12 off)) =
      (s.setHalfword (BitVec.ofNat 64 (D+off)) 0).setPC (s.pc+4) := by
  simp only [execInstrBr, reg, CKB2Half.half_offset off offB, ← BitVec.ofNat_add]
  rfl

theorem ckb2ShRuns (o : Oracle) (s : MachineState) (n : Nat) (base : Reg) (off D : Nat) (hn : n<814)
    (pc : s.pc = BitVec.ofNat 64 (4096+4*n))
    (dec : (Late.Check.Normal.checkerImage.code[n]?).bind decodeInstruction =
      some (.base (.SH base .x0 (BitVec.ofNat 12 off))))
    (reg : s.getReg base = BitVec.ofNat 64 D) (offB : off < 2048) (even : (D+off)%2=0)
    (bound : D+off+2 ≤ MEMORY_BYTES) :
    Runs o s (execInstrBr s (.SH base .x0 (BitVec.ofNat 12 off))) 1 0 := by
  apply ckb2One o s n _ hn pc dec _ rfl
  have valid := CKB2Half.half_access_valid D off even bound offB
  simp only [ordinaryStep, memoryArgumentsValid, memAccess, reg, valid, ↓reduceIte]

/-- The bytes of a zero halfword store at an even address `A`. -/
theorem ckb2ShByte (s : MachineState) (A q : Nat) (even : A%2=0) (hA : A<2^64) (hq : q<2^64) :
    (s.setHalfword (BitVec.ofNat 64 A) 0).getByte (BitVec.ofNat 64 q) =
      if q = A ∨ q = A+1 then 0 else s.getByte (BitVec.ofNat 64 q) := by
  rw [CKB2Half.set_halfword_get_byte s A q 0 even hA hq]
  by_cases h1 : q = A
  · simp [h1]
  · by_cases h2 : q = A+1
    · simp [h2]
    · simp [h1, h2]

theorem ckb2PCByte (s : MachineState) (v q : Word) : (s.setPC v).getByte q = s.getByte q := by
  simp only [MachineState.getByte, MachineState.getMem_setPC]

/-! ### 30-byte slot copies -/

/-- 15 halfword copies `[D+b+2j] ← [S+2j]` then `sh x0, b+30(dst)`. -/
def copy30 (src dst : Reg) (s : MachineState) (b : Nat) : MachineState :=
  execInstrBr (CKB2Half.halfRun src dst s 0 b 15) (.SH dst .x0 (BitVec.ofNat 12 (b+30)))

theorem ckb2CopyRuns (o : Oracle) (s : MachineState) (start : Nat) (src dst : Reg) (b S D : Nat)
    (srcNe : src ≠ .x6) (dstNe : dst ≠ .x6)
    (source : s.getReg src = BitVec.ofNat 64 S) (target : s.getReg dst = BitVec.ofNat 64 D)
    (bBound : b+32 ≤ 2048) (sourceEven : S%2=0) (targetEven : (D+b)%2=0)
    (sourceBound : S+30 ≤ MEMORY_BYTES) (targetBound : D+b+32 ≤ MEMORY_BYTES)
    (hs : start+31 ≤ 814) (pc : s.pc = BitVec.ofNat 64 (4096+4*start))
    (loads : ∀ j<15, (Late.Check.Normal.checkerImage.code[start+2*j]?).bind decodeInstruction =
      some (.base (.LHU .x6 src (BitVec.ofNat 12 (0+2*j)))))
    (stores : ∀ j<15, (Late.Check.Normal.checkerImage.code[start+2*j+1]?).bind decodeInstruction =
      some (.base (.SH dst .x6 (BitVec.ofNat 12 (b+2*j)))))
    (zero : (Late.Check.Normal.checkerImage.code[start+30]?).bind decodeInstruction =
      some (.base (.SH dst .x0 (BitVec.ofNat 12 (b+30))))) :
    Runs o s (copy30 src dst s b) 31 0 := by
  have copy : Runs o s (CKB2Half.halfRun src dst s 0 b 15) 30 0 := by
    apply pureBlockRuns (cyc:=30)
    intro fuel
    have h := CKB2Half.half_run_execute Late.Check.Normal.checkerImage src dst s 0 b S D 15 srcNe dstNe
      source target (by omega) (by omega) (by omega) targetEven (by omega) (by omega)
      (fun j hj t tpc => ckb2Fetch t (start+2*j) _ (by omega)
        (by rw [tpc, pc, ← BitVec.ofNat_add]; congr 1; omega) (loads j hj))
      (fun j hj t tpc => ckb2Fetch t (start+2*j+1) _ (by omega)
        (by rw [tpc, pc, ← BitVec.ofNat_add]; congr 1; omega) (stores j hj)) fuel false
    exact h
  have mid := CKB2Half.half_run_pc src dst s 0 b 15
  have tgt : (CKB2Half.halfRun src dst s 0 b 15).getReg dst = BitVec.ofNat 64 D :=
    (CKB2Half.half_run_register _ _ _ _ _ _ _ dstNe).trans target
  have z := ckb2ShRuns o (CKB2Half.halfRun src dst s 0 b 15) (start+30) dst (b+30) D (by omega)
    (by rw [mid, pc, ← BitVec.ofNat_add]; congr 1) zero tgt (by omega) (by omega) (by omega)
  exact runs_trans copy z

theorem copy30Register (src dst : Reg) (s : MachineState) (b : Nat) (r : Reg) (ne : r ≠ .x6) :
    (copy30 src dst s b).getReg r = s.getReg r := by
  unfold copy30
  simp only [execInstrBr, MachineState.getReg_setPC]
  rw [CKB2Trunc.ckb2t_set_halfword_reg, CKB2Half.half_run_register _ _ _ _ _ _ _ ne]

theorem copy30PC (src dst : Reg) (s : MachineState) (b : Nat) :
    (copy30 src dst s b).pc = s.pc + BitVec.ofNat 64 124 := by
  unfold copy30
  simp only [execInstrBr, MachineState.setPC]
  rw [CKB2Half.half_run_pc, BitVec.add_assoc]; rfl

attribute [local irreducible] CKB2Half.halfRun in
/-- The copy leaves the widened 30-byte source at `D+b` and no other byte changes. -/
theorem copy30Written (src dst : Reg) (s : MachineState) (b S D : Nat)
    (srcNe : src ≠ .x6) (dstNe : dst ≠ .x6)
    (source : s.getReg src = BitVec.ofNat 64 S) (target : s.getReg dst = BitVec.ofNat 64 D)
    (bBound : b+32 ≤ 2048) (sourceEven : S%2=0) (targetEven : (D+b)%2=0)
    (sourceBound : S+30 ≤ 2^64) (targetBound : D+b+32 ≤ 2^64)
    (separate : S+30 ≤ D+b ∨ D+b+32 ≤ S) :
    Written s (copy30 src dst s b) (D+b) (widen (readBuffer s S 30)) := by
  let h := CKB2Half.halfRun src dst s 0 b 15
  have tgt : h.getReg dst = BitVec.ofNat 64 D :=
    (CKB2Half.half_run_register _ _ _ _ _ _ _ dstNe).trans target
  have st : copy30 src dst s b = (h.setHalfword (BitVec.ofNat 64 (D+(b+30))) 0).setPC (h.pc+4) :=
    ckb2ShState h dst (b+30) D tgt (by omega)
  have byte (q : Nat) (hq : q<2^64) : (copy30 src dst s b).getByte (BitVec.ofNat 64 q) =
      if q = D+b+30 ∨ q = D+b+31 then 0 else h.getByte (BitVec.ofNat 64 q) := by
    rw [st, ckb2PCByte, ckb2ShByte h (D+(b+30)) q (by omega) (by omega) hq]
    simp only [show D+(b+30) = D+b+30 by omega, show D+b+30+1 = D+b+31 by omega]
  have outsideH (q : Nat) (hq : q<2^64) (out : q < D+b ∨ D+b+30 ≤ q) :
      h.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q) :=
    CKB2Half.half_run_byte_outside src dst s 0 b D 15 q dstNe target (by omega) targetEven (by omega) hq out
  constructor
  · unfold digestAt
    rw [CKB2Half.read_widen _ _ (by rw [byte _ (by omega), if_pos (Or.inl rfl)])
      (by rw [byte _ (by omega), if_pos (Or.inr rfl)])]
    apply congrArg widen
    have cp := CKB2Half.half_run_copy src dst s 0 b S D 15 srcNe dstNe source target (by omega) (by omega)
      (by omega) targetEven (by omega) (by omega) (by omega)
    have e30 : readBuffer (copy30 src dst s b) (D+b) 30 = readBuffer h (D+b) 30 := by
      apply CKB2Half.read_buffer_bytes_congr
      intro i hi
      rw [byte _ (by omega), if_neg (by omega)]
    rw [e30]
    simpa using cp
  · intro a ha sep
    unfold byteAt
    unfold Separate at sep
    rw [byte a ha, if_neg (by omega), outsideH a ha (by omega)]

/-! ### Decoded copy words (704..734, 737..767, 776..806) -/

set_option maxHeartbeats 4000000 in
theorem ckb2Loads (start : Nat) (h : start=704 ∨ start=737 ∨ start=776) :
    ∀ j<15, (Late.Check.Normal.checkerImage.code[start+2*j]?).bind decodeInstruction =
      some (.base (.LHU .x6 .x19 (BitVec.ofNat 12 (0+2*j)))) := by
  rcases h with rfl|rfl|rfl <;> (intro j hj;interval_cases j <;> rfl)

set_option maxHeartbeats 4000000 in
theorem ckb2StoresRight : ∀ j<15, (Late.Check.Normal.checkerImage.code[704+2*j+1]?).bind decodeInstruction =
    some (.base (.SH .x23 .x6 (BitVec.ofNat 12 (32+2*j)))) := by
  intro j hj;interval_cases j <;> rfl

set_option maxHeartbeats 4000000 in
theorem ckb2StoresLeft : ∀ j<15, (Late.Check.Normal.checkerImage.code[737+2*j+1]?).bind decodeInstruction =
    some (.base (.SH .x23 .x6 (BitVec.ofNat 12 (0+2*j)))) := by
  intro j hj;interval_cases j <;> rfl

set_option maxHeartbeats 4000000 in
theorem ckb2StoresParent : ∀ j<15, (Late.Check.Normal.checkerImage.code[776+2*j+1]?).bind decodeInstruction =
    some (.base (.SH .x24 .x6 (BitVec.ofNat 12 (0+2*j)))) := by
  intro j hj;interval_cases j <;> rfl

theorem ckb2ZeroRight : (Late.Check.Normal.checkerImage.code[704+30]?).bind decodeInstruction =
    some (.base (.SH .x23 .x0 (BitVec.ofNat 12 (32+30)))) := by rfl
theorem ckb2ZeroLeft : (Late.Check.Normal.checkerImage.code[737+30]?).bind decodeInstruction =
    some (.base (.SH .x23 .x0 (BitVec.ofNat 12 (0+30)))) := by rfl
theorem ckb2ZeroParent : (Late.Check.Normal.checkerImage.code[776+30]?).bind decodeInstruction =
    some (.base (.SH .x24 .x0 (BitVec.ofNat 12 (0+30)))) := by rfl

/-! ### The pair hash (words 768..773) -/

theorem ckb2HashRegisters (s : MachineState) (pc : s.pc = 7168) :
    let ready := hashSetupState s
    ready.pc=7188 ∧ ready.getReg .x5=0 ∧ ready.getReg .x11=96 ∧ ready.getReg .x13=0 ∧
    ready.getReg .x10=s.getReg .x23 ∧ ready.getReg .x12=s.getReg .x24 ∧ ready.mem=s.mem := by
  simp [hashSetupState,hashSetupOps,execInstrBr,pc,signExtend12,
    MachineState.getReg,MachineState.setPC,MachineState.setReg]

theorem ckb2HashRun (s : MachineState) (pc : s.pc = 7168)
    (sv : rangeValid (s.getReg .x23) 96 = true) (sa : (s.getReg .x23).toNat % 8=0)
    (dv : rangeValid (s.getReg .x24) 32 = true) (da : (s.getReg .x24).toNat % 8=0)
    (fuel : Nat) (coins : Bool) :
    execute Late.Check.Normal.checkerImage (6+fuel) s coins =
      (do let answer ← (liftM (World.query (.inr (.inl (readBuffer s (s.getReg .x23).toNat 96)))) :
                         OracleComp World Digest)
          let next ← execute Late.Check.Normal.checkerImage fuel (hashed s answer) coins
          return next.charge 13 1) := by
  let ready := hashSetupState s
  obtain ⟨endPC,r5,r11,r13,r10,r12,mem⟩ := ckb2HashRegisters s pc
  have ef : fetch Late.Check.Normal.checkerImage ready = some (.base .ECALL) := by
    apply ckb2Fetch _ 773 _ (by decide) endPC; rfl
  have arg : oracleInput ready = some (.inl (readBuffer s (s.getReg .x23).toNat 96)) := by
    simp [ready,oracleInput,r13,r10,r11,r12,sa,da,sv,dv,COMPRESSION_INPUT_LENGTH,COMPRESSION_OUTPUT_LENGTH,
      read_buffer_memory_congr _ _ mem]
    try rfl
  rw [show 6+fuel=5+(fuel+1) by omega,ckb2HashSetupRun s pc,execute,ef,if_pos r5,arg]
  simp only [writeOracleAnswer,r12,bind_assoc,pure_bind]
  apply congrArg (fun continuation => (liftM (World.query (.inr (.inl (readBuffer s (s.getReg .x23).toNat 96)))) :
      OracleComp World Digest) >>= continuation)
  funext answer
  simp [hashed,oracleCycles,COMPRESSION_CYCLES,Execution.charge,← Nat.add_assoc]
  congr

/-! ### Truncating the pair hash -/

theorem truncWritten (t m : MachineState) (D : Nat) (d : Digest) (w : Written t m D d)
    (aligned : D%8=0) (bound : D+32 ≤ 2^64) (pcv : Word) :
    Written t ((m.setHalfword (BitVec.ofNat 64 (D+30)) 0).setPC pcv) D (cut 17 d) := by
  constructor
  · unfold digestAt
    rw [read_buffer_memory_congr ((m.setHalfword (BitVec.ofNat 64 (D+30)) 0).setPC pcv)
        (m.setHalfword (BitVec.ofNat 64 (D+30)) 0) rfl,
      CKB2Trunc.ckb2t_trunc_store_digest m D aligned bound,
      show readBuffer m D 32 = d from w.atDst, cut_of_cut (by decide)]
  · intro a ha sep
    unfold byteAt
    have e := w.outside a ha sep
    unfold byteAt at e
    unfold Separate at sep
    rw [ckb2PCByte, ckb2ShByte m (D+30) a (by omega) (by omega) ha, if_neg (by omega), e]

end CommitGolfCandidate.PairCap.Batch
