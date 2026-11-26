import CommitGolfCandidate.PairPath
import CommitGolfCandidate.TruncGuardRun
import CommitGolfCandidate.TruncCheckPrep
import CommitGolfCandidate.TruncMask
namespace CommitGolfCandidate.Trunc.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate.PairCap
set_option maxRecDepth 14000
set_option maxHeartbeats 1500000

theorem restoredNext (state : MachineState) (pc : state.pc = loc 1015)
    (fuel : Nat) (allowCoins : Bool) :
    execute (Trunc.submission.image .check) (5 + fuel) state allowCoins =
      (do let result ← execute (Trunc.submission.image .check) fuel (rec_checkPathNextState state) allowCoins
          return result.charge 5 0) := by
  let advanced := (state.setReg .x25 (state.getReg .x25 + 32)).setPC 5208
  let atJump:=(state.setReg .x25 (state.getReg .x25+32)).setPC (loc 1016)
  let shifted := (advanced.setReg .x20 (state.getReg .x20 >>> 1)).setPC 5212
  let next := (shifted.setReg .x29 (state.getReg .x29 - 1)).setPC 5216
  have f0 : fetch (Trunc.submission.image .check) state = some (.base (.ADDI .x25 .x25 32)) := by
    apply fetchAt _ _ 1015 _ (by decide) pc; rfl
  have f1 : fetch (Trunc.submission.image .check) advanced = some (.base (.SRLI .x20 .x20 1)) := by
    apply sharedFetch _ 278 _ (by unfold untouched;decide) rfl; rfl
  have f2 : fetch (Trunc.submission.image .check) shifted = some (.base (.ADDI .x29 .x29 4095)) := by
    apply sharedFetch _ 279 _ (by unfold untouched;decide) rfl; rfl
  have f3 : fetch (Trunc.submission.image .check) next = some (.base (.BNE .x29 .x0 8048)) := by
    apply sharedFetch _ 280 _ (by unfold untouched;decide) rfl; rfl
  have s0 : ordinaryStep state (.base (.ADDI .x25 .x25 32)) = some atJump := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, atJump, pc,loc]
  have s1 : ordinaryStep advanced (.base (.SRLI .x20 .x20 1)) = some shifted := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, advanced, shifted,
      MachineState.getReg, MachineState.setReg, MachineState.setPC]
  have s2 : ordinaryStep shifted (.base (.ADDI .x29 .x29 4095)) = some next := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, advanced, shifted, next,
      MachineState.getReg, MachineState.setReg, MachineState.setPC, BitVec.sub_eq_add_neg]
  have s3 : ordinaryStep next (.base (.BNE .x29 .x0 8048)) = some (rec_checkPathNextState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13,
      advanced, shifted, next, rec_checkPathNextState, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    split <;> simp_all
  have j:=jumpAt (Trunc.submission.image .check) atJump 1016 278 2094200 (by decide) rfl (by rfl) (by decide)
  rw [show 5+fuel=(1+(3+fuel))+1 by omega,execute_ordinary_step _ _ _ _ _ _ f0 s0,j]
  change (do let z ← (do let r ← execute (Trunc.submission.image .check) (3+fuel) advanced allowCoins
                          return r.charge 1 0)
             return z.charge 1 0)=_
  rw [Nat.add_comm 3 fuel]
  simp only [execute,f1,s1,f2,s2,f3,s3,instructionCycles,bind_assoc,pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

theorem guardedNext (s : MachineState) (pc : s.pc=loc 277) (scratch : s.getReg .x21=256) (fuel : Nat) (coins : Bool) :
    execute (Trunc.submission.image .check) (15+fuel) s coins=
      (do let r← execute (Trunc.submission.image .check) fuel (PairCap.rec_checkPathNextState (if guardTest s then Guard.cleared s else s)) coins
          return r.charge 15 0) := by
  have g:=Guard.runGuard s pc scratch
  rw [show 15+fuel=10+(5+fuel) by omega,g,restoredNext _ rfl]
  have ignore (t : MachineState) : PairCap.rec_checkPathNextState (t.setPC (loc 1015))=PairCap.rec_checkPathNextState t := rfl
  simp only [ignore,bind_assoc,pure_bind];simp [Execution.charge,←Nat.add_assoc]

def adjusted (s : MachineState) (v : Digest) := if guardTest s then padLow v else v
def rec_checkPathStepState (s : MachineState) (v : Digest) := PairCap.rec_checkPathStepState s (adjusted s v)

theorem guardPrep (s : MachineState) (v : Digest) :
    guardTest (checkCompressionState (PairCap.rec_checkPathPreparedState s) v) ↔ guardTest s := by
  unfold guardTest
  rw [rec_path_compression_register s v .x29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      rec_path_compression_register s v .x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      rec_path_compression_register s v .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]

theorem clearPrep (s : MachineState) (v : Digest) (scratch : s.getReg .x21=256) :
    (if guardTest (checkCompressionState (PairCap.rec_checkPathPreparedState s) v)
       then Guard.cleared (checkCompressionState (PairCap.rec_checkPathPreparedState s) v)
       else checkCompressionState (PairCap.rec_checkPathPreparedState s) v)
    = checkCompressionState (PairCap.rec_checkPathPreparedState s) (adjusted s v) := by
  by_cases g : guardTest s
  · rw [if_pos ((guardPrep s v).mpr g),adjusted,if_pos g]
    have p:=(rec_path_compression_register s v .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans scratch
    unfold Guard.cleared;rw [p];exact clearedReply _ 256 v (by decide) (by decide)
  · rw [if_neg (fun h=>g ((guardPrep s v).mp h)),adjusted,if_neg g]

theorem rec_check_path_step (state : MachineState) (pc : state.pc = 5072)
    (scratch : state.getReg .x21 = 256)
    (sourceValid : ∀ word : Fin 4,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (Trunc.submission.image .check) (pathPreparationSteps (state.getReg .x20) + 37 + fuel) state allowCoins =
      (do let answer ← World.query (.inr (.inl (padInput (readBuffer (rec_checkPathPreparedState state) 256 64))))
          let result ← execute (Trunc.submission.image .check) fuel (rec_checkPathStepState state answer) allowCoins
          return result.charge (pathPreparationSteps (state.getReg .x20) + 44) 1) := by
  have preparedPC := rec_check_path_prepared_pc state
  have preparedScratch : (rec_checkPathPreparedState state).getReg .x21 = 256 :=
    (rec_check_path_prepared_register state .x21 (by decide) (by decide)).trans scratch
  have compressionPC (answer : BitVec 256) :
      (checkCompressionState (rec_checkPathPreparedState state) answer).pc = 5204 := by
    rw [check_compression_pc, preparedPC]
    rfl
  rw [show pathPreparationSteps (state.getReg .x20) + 37 + fuel =
      pathPreparationSteps (state.getReg .x20) + (22 + (15 + fuel)) by omega,
    rec_check_path_preparation state pc scratch sourceValid,
    rec_check_compression _ 54 rfl preparedPC preparedScratch]
  simp only [bind_assoc, pure_bind]
  apply congrArg (fun continuation =>
    (liftM (World.query (.inr (.inl (padInput (readBuffer (rec_checkPathPreparedState state) 256 64))))) :
      OracleComp World (BitVec 256)) >>= continuation)
  funext answer
  have ptr:=(rec_path_compression_register state answer .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans scratch
  rw [guardedNext _ (compressionPC answer) ptr,clearPrep state answer scratch]
  simp [rec_checkPathStepState,PairCap.rec_checkPathStepState, Execution.charge, ← Nat.add_assoc]
end CommitGolfCandidate.Trunc.Check
