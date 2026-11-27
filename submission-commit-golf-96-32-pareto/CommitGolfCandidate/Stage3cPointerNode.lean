import CommitGolfCandidate.Stage3cPointerSites
import CommitGolfCandidate.Stage3cHash
import CommitGolfCandidate.Stage3cMaskStep
import CommitGolfCandidate.Stage3cPlainBlock
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

theorem reply_read (s : MachineState) (a : Nat) (v : Output) :
    readBuffer (writeBits s (BitVec.ofNat 64 a) v) a 32 = v := by
  simpa only [Nat.add_zero, Nat.mul_zero, BitVec.extractLsb'_eq_self] using
    write_bits_digest s a 0 v (by decide) (by decide)

theorem hash_runs (o : Oracle) (s : MachineState) (src dst : Nat)
    (found : fetch (image .commit) s = some (.base .ECALL))
    (sel : s.getReg .x5 = 0) (len : s.getReg .x11 = 96) (kind : s.getReg .x13 = 0)
    (x : s.getReg .x10 = BitVec.ofNat 64 src) (y : s.getReg .x12 = BitVec.ofNat 64 dst)
    (rs : src + 96 ≤ MEMORY_BYTES) (asrc : src % 8 = 0)
    (rd : dst + 32 ≤ MEMORY_BYTES) (adst : dst % 8 = 0) :
    Runs .commit true o s (writeBits s (BitVec.ofNat 64 dst) (o.compression (readBuffer s src 96))) 1 8 1 := by
  intro fuel
  exact hash_fixed .commit true o s fuel src dst found sel len kind x y rs asrc rd adst

private theorem addi_go (s : MachineState) (rd : Reg) (imm : BitVec 12) :
    ordinaryStep s (.base (.ADDI rd rd imm)) =
      some ((s.setReg rd (s.getReg rd + signExtend12 imm)).setPC (s.pc + 4)) := by
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr]

private theorem bump_keep (s : MachineState) (rd r : Reg) (v : BitVec 64) (ne : rd ≠ r) :
    ((s.setReg rd v).setPC (s.pc + 4)).getReg r = s.getReg r := by
  simp [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ ne]

/-- One running-pointer parent: compression, an optional 240-bit clear, then the two pointer bumps.
Width 238 is not this lemma; the image under certification has no unchained 238-bit level. -/
theorem slot_run (d : Height) (o : Oracle) (s : MachineState) (n : Nat) (odd : Bool)
    (fit : n + 5 < 11543)
    (width : wireWidth d = 256 ∨ wireWidth d = 240)
    (code : PtrSlot n (wireWidth d) odd)
    (pc : s.pc = pcAt n)
    (sel : s.getReg .x5 = 0) (len : s.getReg .x11 = 96) (kind : s.getReg .x13 = 0)
    (src dst : Nat)
    (x : s.getReg .x10 = BitVec.ofNat 64 src) (y : s.getReg .x12 = BitVec.ofNat 64 dst)
    (rs : src + 96 ≤ MEMORY_BYTES) (asrc : src % 8 = 0)
    (rd : dst + 32 ≤ MEMORY_BYTES) (adst : dst % 8 = 0) :
    ∃ t, Runs .commit true o s t (laneWords d) (laneWords d + 7) 1 ∧
      t.getReg .x10 = BitVec.ofNat 64 src + signExtend12 96 ∧
      t.getReg .x12 = BitVec.ofNat 64 dst + signExtend12 (ptrDstImm odd) ∧
      t.pc = pcAt (n + laneWords d) ∧
      (∀ r, r ≠ .x10 → r ≠ .x12 → t.getReg r = s.getReg r) ∧
      t.mem = (writeBits s (BitVec.ofNat 64 dst) (storeReply d (o.compression (readBuffer s src 96)))).mem := by
  let answer : Output := o.compression (readBuffer s src 96)
  let t1 := writeBits s (BitVec.ofNat 64 dst) answer
  have fetched := decoded_site (by omega) code.1 s pc
  have ran := hash_runs o s src dst fetched sel len kind x y rs asrc rd adst
  have pc1 : t1.pc = pcAt (n + 1) := by
    have hpc : t1.pc = s.pc + 4 := by
      simpa [t1] using congrArg MachineState.pc (write_frame s (BitVec.ofNat 64 dst) answer)
    rw [hpc, pc, pc_succ]
  have a0₁ : t1.getReg .x10 = BitVec.ofNat 64 src := (writeBits_register s _ answer .x10).trans x
  have a2₁ : t1.getReg .x12 = BitVec.ofNat 64 dst := (writeBits_register s _ answer .x12).trans y
  have keep (r : Reg) : t1.getReg r = s.getReg r := writeBits_register s _ answer r
  rcases width with w256 | w240
  · have lw : laneWords d = 3 := by simp [laneWords, w256]
    obtain ⟨wA0, wA2⟩ := code.2.1 w256
    have fA := decoded_site (by omega) wA0 t1 pc1
    have stA := addi_go t1 .x10 96
    let t2 := (t1.setReg .x10 (t1.getReg .x10 + signExtend12 96)).setPC (t1.pc + 4)
    have runA := runs_step (coins := true) (o := o) fA stA
    have pc2 : t2.pc = pcAt (n + 2) := by change t1.pc + 4 = _; rw [pc1, pc_succ]
    have a0₂ : t2.getReg .x10 = BitVec.ofNat 64 src + signExtend12 96 := by
      simp [t2, MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : (.x10 : Reg) ≠ .x0), a0₁]
    have a2₂ : t2.getReg .x12 = BitVec.ofNat 64 dst := by
      simp [t2, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne t1 .x10 .x12 _ (by decide : (.x10 : Reg) ≠ .x12), a2₁]
    have fB := decoded_site (by omega) wA2 t2 pc2
    have stB := addi_go t2 .x12 (ptrDstImm odd)
    let t3 := (t2.setReg .x12 (t2.getReg .x12 + signExtend12 (ptrDstImm odd))).setPC (t2.pc + 4)
    have runB := runs_step (coins := true) (o := o) fB stB
    refine ⟨t3, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [lw, instructionCycles, t3] using runs_comp (runs_comp ran runA) runB
    · simp [t3, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne t2 .x12 .x10 _ (by decide : (.x12 : Reg) ≠ .x10), a0₂]
    · simp [t3, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide : (.x12 : Reg) ≠ .x0), a2₂]
    · unfold t3; change t2.pc + 4 = pcAt (n + laneWords d); rw [pc2, pc_succ, lw]
    · intro r hx10 hx12
      exact (bump_keep t2 .x12 r _ hx12.symm).trans ((bump_keep t1 .x10 r _ hx10.symm).trans (keep r))
    · have ident : storeReply d answer = answer := by
        simp only [storeReply, w256, Nat.mod_eq_of_lt answer.isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      have memT : t3.mem = (writeBits s (BitVec.ofNat 64 dst) answer).mem := by
        simp only [t3, t2, t1, MachineState.setReg, MachineState.setPC]
      rw [memT, ← ident]
  · have lw : laneWords d = 4 := by simp [laneWords, w240]
    obtain ⟨wSH, wA0, wA2⟩ := code.2.2.1 w240
    have address : t1.getReg .x12 + signExtend12 30 = BitVec.ofNat 64 (dst + 30) :=
      (congrArg (· + signExtend12 30) a2₁).trans (BitVec.ofNat_add dst 30).symm
    have okSH : memoryArgumentsValid t1 (.SH .x12 .x0 30) = true := by
      change accessValid (_ + _) 2 = true
      rw [address]
      change dst + 32 ≤ 2 ^ 36 at rd
      apply access_ok <;> first | omega | (change _ ≤ 2 ^ 36; omega)
    have shEval : execInstrBr t1 (.SH .x12 .x0 30) =
        (writeBits s (BitVec.ofNat 64 dst) (storeReply d answer)).setPC (s.pc + 8) := by
      have step := masked_reply_step d w240 s dst answer y adst
        (by change dst + 32 ≤ 2 ^ 36 at rd; omega)
      rw [y] at step
      simpa only [t1] using step
    have fSH := decoded_site (by omega) wSH t1 pc1
    have stSH : ordinaryStep t1 (.base (.SH .x12 .x0 30)) = some (execInstrBr t1 (.SH .x12 .x0 30)) := by
      simp only [ordinaryStep, okSH, ↓reduceIte]
    let tM := execInstrBr t1 (.SH .x12 .x0 30)
    have runSH := runs_step (coins := true) (o := o) fSH stSH
    have pcM : tM.pc = pcAt (n + 2) := by
      unfold tM
      rw [shEval, MachineState.setPC, pc]
      change BitVec.ofNat 64 (4096 + 4 * n) + BitVec.ofNat 64 8 = BitVec.ofNat 64 (4096 + 4 * (n + 2))
      rw [← BitVec.ofNat_add]
      congr 1
    have a0M : tM.getReg .x10 = BitVec.ofNat 64 src := by
      unfold tM
      rw [shEval, MachineState.getReg_setPC, writeBits_register, x]
    have a2M : tM.getReg .x12 = BitVec.ofNat 64 dst := by
      unfold tM
      rw [shEval, MachineState.getReg_setPC, writeBits_register, y]
    have keepM (r : Reg) : tM.getReg r = s.getReg r := by
      unfold tM
      rw [shEval, MachineState.getReg_setPC, writeBits_register]
    have fA := decoded_site (by omega) wA0 tM pcM
    have stA := addi_go tM .x10 96
    let t2 := (tM.setReg .x10 (tM.getReg .x10 + signExtend12 96)).setPC (tM.pc + 4)
    have runA := runs_step (coins := true) (o := o) fA stA
    have pc2 : t2.pc = pcAt (n + 3) := by change tM.pc + 4 = _; rw [pcM, pc_succ]
    have a0₂ : t2.getReg .x10 = BitVec.ofNat 64 src + signExtend12 96 := by
      simp [t2, MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : (.x10 : Reg) ≠ .x0), a0M]
    have a2₂ : t2.getReg .x12 = BitVec.ofNat 64 dst := by
      simp [t2, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne tM .x10 .x12 _ (by decide : (.x10 : Reg) ≠ .x12), a2M]
    have fB := decoded_site (by omega) wA2 t2 pc2
    have stB := addi_go t2 .x12 (ptrDstImm odd)
    let t3 := (t2.setReg .x12 (t2.getReg .x12 + signExtend12 (ptrDstImm odd))).setPC (t2.pc + 4)
    have runB := runs_step (coins := true) (o := o) fB stB
    refine ⟨t3, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [lw, instructionCycles, t3] using runs_comp (runs_comp (runs_comp ran runSH) runA) runB
    · simp [t3, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne t2 .x12 .x10 _ (by decide : (.x12 : Reg) ≠ .x10), a0₂]
    · simp [t3, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide : (.x12 : Reg) ≠ .x0), a2₂]
    · unfold t3; change t2.pc + 4 = pcAt (n + laneWords d); rw [pc2, pc_succ, lw]
    · intro r hx10 hx12
      exact (bump_keep t2 .x12 r _ hx12.symm).trans ((bump_keep tM .x10 r _ hx10.symm).trans (keepM r))
    · have memM : tM.mem = (writeBits s (BitVec.ofNat 64 dst) (storeReply d answer)).mem := by
        unfold tM
        rw [shEval, MachineState.setPC]
      have memT : t3.mem = tM.mem := by
        simp only [t3, t2, MachineState.setReg, MachineState.setPC]
      rw [memT, memM]

end CommitGolfCandidate.Chained.BinaryMachine
