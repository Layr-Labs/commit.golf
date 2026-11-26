import CommitGolfCandidate.TruncBBlocks
import CommitGolfCandidate.TruncRecordExit
namespace CommitGolfCandidate.Trunc.Batch

open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 12000

def lengthOps : List Instr :=
  [.ADDI .x6 .x0 35, .SLLI .x6 .x6 11, .ADDI .x6 .x6 1024]

def lengthState (s : MachineState) := lengthOps.foldl execInstrBr s

theorem lengthRun (s : MachineState) (pc : s.pc=4884) 
    (fuel : Nat) (coins : Bool) :
    execute (Trunc.wireImage true) (3+fuel) s coins =
      (do let next ← execute (Trunc.wireImage true) fuel (lengthState s) coins
          return next.charge 3 0) :=
  plainBlock lengthOps 197 (by decide) (by decide) (by intro k; fin_cases k <;> rfl) s pc (by intro k; fin_cases k <;> rfl) fuel coins

def readyOps : List Instr :=
  [.ADDI .x6 .x0 33, .SLLI .x6 .x6 11, .ADDI .x6 .x6 1024, .ADD .x19 .x25 .x6, .ADDI .x21 .x0 256, .ADDI .x30 .x0 16]

def readyState (s : MachineState) := readyOps.foldl execInstrBr s

theorem readyRun (s : MachineState) (pc : s.pc=4900) 
    (fuel : Nat) (coins : Bool) :
    execute (Trunc.wireImage true) (6+fuel) s coins =
      (do let next ← execute (Trunc.wireImage true) fuel (readyState s) coins
          return next.charge 6 0) :=
  plainBlock readyOps 201 (by decide) (by decide) (by intro k; fin_cases k <;> rfl) s pc (by intro k; fin_cases k <;> rfl) fuel coins

def bucketOps : List Instr :=
  [.ADDI .x22 .x0 6, .SLLI .x22 .x22 11, .ADDI .x22 .x22 0, .ADD .x22 .x22 .x20, .LBU .x7 .x22 0, .SRLI .x6 .x20 1, .ADD .x6 .x20 .x6, .SLLI .x6 .x6 5, .ADDI .x23 .x0 8, .SLLI .x23 .x23 11, .ADDI .x23 .x23 0, .ADD .x23 .x23 .x6]

def bucketState (s : MachineState) := bucketOps.foldl execInstrBr s

private theorem tailSafe (op : Instr) (rest : List Instr) (s : MachineState) (safe : safeSteps (op::rest) s) :
    safeSteps rest (execInstrBr s op) := by
  intro j;exact safe ⟨j.val+1,by simpa using j.isLt⟩

private theorem foldTail (s : MachineState) (op : Instr) (xs rest : List Instr) (same : xs=op::rest) :
    rest.foldl execInstrBr (execInstrBr s op)=xs.foldl execInstrBr s := by rw [same];rfl

private theorem bucketFold (s : MachineState) : (bucketOps.drop 1).foldl execInstrBr (execInstrBr s (.ADDI .x22 .x0 6))=bucketState s :=
  foldTail s _ bucketOps (bucketOps.drop 1) (by rfl)

theorem bucketRun (s : MachineState) (pc : s.pc=5120) (mode : s.getReg .x19≠0) (safe : safeSteps bucketOps s)
    (fuel : Nat) (coins : Bool) :
    execute (Trunc.wireImage true) (15+fuel) s coins =
      (do let r←execute (Trunc.wireImage true) fuel (bucketState s) coins; return r.charge 15 0) := by
  let x:=execInstrBr s (.ADDI .x22 .x0 6)
  have p : x.pc=5124 := by change s.pc+4=_;rw [pc];rfl
  have tail:=plainBlock (bucketOps.drop 1) 257 (by decide) (by intro j;fin_cases j <;> rfl)
    (by intro j;fin_cases j <;> rfl) x p (tailSafe (.ADDI .x22 .x0 6) (bucketOps.drop 1) s safe)
  have tailLaw : Trunc.Runs (Trunc.wireImage true) x (bucketState s) 11 11 := by
    rw [←bucketFold s]
    exact tail
  exact chain (bucketEnter s pc mode) tailLaw fuel coins

def storeOps : List Instr :=
  [.ADDI .x7 .x0 1, .SB .x22 .x7 0, .LD .x6 .x21 0, .SD .x23 .x6 0, .LD .x6 .x21 8, .SD .x23 .x6 8, .LD .x6 .x21 16, .SD .x23 .x6 16, .LD .x6 .x21 24, .SD .x23 .x6 24]

def storeState (s : MachineState) := storeOps.foldl execInstrBr s

theorem storeRun (s : MachineState) (pc : s.pc=5224) (safe : safeSteps storeOps s)
    (fuel : Nat) (coins : Bool) :
    execute (Trunc.wireImage true) (10+fuel) s coins =
      (do let next ← execute (Trunc.wireImage true) fuel (storeState s) coins
          return next.charge 10 0) :=
  plainBlock storeOps 282 (by decide) (by decide) (by intro k; fin_cases k <;> rfl) s pc safe fuel coins

def recordNextOps : List Instr :=
  [.ADDI .x24 .x24 8, .ADDI .x27 .x27 4095]

def recordNextState (s : MachineState) := recordNextOps.foldl execInstrBr s

theorem recordNextRun (s : MachineState) (pc : s.pc=5264) 
    (fuel : Nat) (coins : Bool) :
    execute (Trunc.wireImage true) (2+fuel) s coins =
      (do let next ← execute (Trunc.wireImage true) fuel (recordNextState s) coins
          return next.charge 2 0) :=
  plainBlock recordNextOps 292 (by decide) (by decide) (by intro k; fin_cases k <;> rfl) s pc (by intro k; fin_cases k <;> rfl) fuel coins

def initPairsOps : List Instr :=
  [.ADDI .x22 .x0 6, .SLLI .x22 .x22 11, .ADDI .x22 .x22 0, .ADDI .x23 .x0 8, .SLLI .x23 .x23 11, .ADDI .x23 .x23 0, .ADDI .x24 .x0 2, .SLLI .x24 .x24 11, .ADDI .x24 .x24 512, .ADDI .x27 .x0 128]

def initPairsState (s : MachineState) := initPairsOps.foldl execInstrBr s

theorem initPairsRun (s : MachineState) (pc : s.pc=5276) 
    (fuel : Nat) (coins : Bool) :
    execute (Trunc.wireImage true) (10+fuel) s coins =
      (do let next ← execute (Trunc.wireImage true) fuel (initPairsState s) coins
          return next.charge 10 0) :=
  plainBlock initPairsOps 295 (by decide) (by decide) (by intro k; fin_cases k <;> rfl) s pc (by intro k; fin_cases k <;> rfl) fuel coins

def marksOps : List Instr :=
  [.LBU .x6 .x22 0, .LBU .x7 .x22 1]

def marksState (s : MachineState) := marksOps.foldl execInstrBr s

theorem marksRun (s : MachineState) (pc : s.pc=5316) (safe : safeSteps marksOps s)
    (fuel : Nat) (coins : Bool) :
    execute (Trunc.wireImage true) (2+fuel) s coins =
      (do let next ← execute (Trunc.wireImage true) fuel (marksState s) coins
          return next.charge 2 0) :=
  plainBlock marksOps 305 (by decide) (by decide) (by intro k; fin_cases k <;> rfl) s pc safe fuel coins

def fillRightOps : List Instr :=
  [.LD .x6 .x19 0, .SD .x23 .x6 32, .LD .x6 .x19 8, .SD .x23 .x6 40, .LD .x6 .x19 16, .SD .x23 .x6 48, .LD .x6 .x19 24, .SD .x23 .x6 56]

def fillRightState (s : MachineState) := fillRightOps.foldl execInstrBr s

theorem fillRightRun (s : MachineState) (pc : s.pc=5336) (safe : safeSteps fillRightOps s)
    (fuel : Nat) (coins : Bool) :
    execute (Trunc.wireImage true) (8+fuel) s coins =
      (do let next ← execute (Trunc.wireImage true) fuel (fillRightState s) coins
          return next.charge 8 0) :=
  plainBlock fillRightOps 310 (by decide) (by decide) (by intro k; fin_cases k <;> rfl) s pc safe fuel coins

def fillLeftOps : List Instr :=
  [.LD .x6 .x19 0, .SD .x23 .x6 0, .LD .x6 .x19 8, .SD .x23 .x6 8, .LD .x6 .x19 16, .SD .x23 .x6 16, .LD .x6 .x19 24, .SD .x23 .x6 24]

def fillLeftState (s : MachineState) := fillLeftOps.foldl execInstrBr s

theorem fillLeftRun (s : MachineState) (pc : s.pc=5376) (safe : safeSteps fillLeftOps s)
    (fuel : Nat) (coins : Bool) :
    execute (Trunc.wireImage true) (8+fuel) s coins =
      (do let next ← execute (Trunc.wireImage true) fuel (fillLeftState s) coins
          return next.charge 8 0) :=
  plainBlock fillLeftOps 320 (by decide) (by decide) (by intro k; fin_cases k <;> rfl) s pc safe fuel coins

def hashSetupOps : List Instr :=
  [.ADDI .x5 .x0 0, .ADDI .x10 .x23 0, .ADDI .x11 .x0 96, .ADDI .x12 .x24 0, .ADDI .x13 .x0 0]

def hashSetupState (s : MachineState) := hashSetupOps.foldl execInstrBr s

theorem hashSetupRun (s : MachineState) (pc : s.pc=5408) 
    (fuel : Nat) (coins : Bool) :
    execute (Trunc.wireImage true) (5+fuel) s coins =
      (do let next ← execute (Trunc.wireImage true) fuel (hashSetupState s) coins
          return next.charge 5 0) :=
  plainBlock hashSetupOps 328 (by decide) (by decide) (by intro k; fin_cases k <;> rfl) s pc (by intro k; fin_cases k <;> rfl) fuel coins

def useParentOps : List Instr :=
  [.LD .x6 .x19 0, .SD .x24 .x6 0, .LD .x6 .x19 8, .SD .x24 .x6 8, .LD .x6 .x19 16, .SD .x24 .x6 16, .LD .x6 .x19 24, .SD .x24 .x6 24]

def useParentState (s : MachineState) := useParentOps.foldl execInstrBr s

theorem useParentRun (s : MachineState) (pc : s.pc=5436) (safe : safeSteps useParentOps s)
    (fuel : Nat) (coins : Bool) :
    execute (Trunc.wireImage true) (8+fuel) s coins =
      (do let next ← execute (Trunc.wireImage true) fuel (useParentState s) coins
          return next.charge 8 0) :=
  plainBlock useParentOps 335 (by decide) (by decide) (by intro k; fin_cases k <;> rfl) s pc safe fuel coins

def pairNextOps : List Instr :=
  [.ADDI .x19 .x19 32, .ADDI .x22 .x22 2, .ADDI .x23 .x23 96, .ADDI .x24 .x24 32, .ADDI .x27 .x27 4095]

def pairNextState (s : MachineState) := pairNextOps.foldl execInstrBr s

theorem pairNextRun (s : MachineState) (pc : s.pc=5468) 
    (fuel : Nat) (coins : Bool) :
    execute (Trunc.wireImage true) (5+fuel) s coins =
      (do let next ← execute (Trunc.wireImage true) fuel (pairNextState s) coins
          return next.charge 5 0) :=
  plainBlock pairNextOps 343 (by decide) (by decide) (by intro k; fin_cases k <;> rfl) s pc (by intro k; fin_cases k <;> rfl) fuel coins

def initRootOps : List Instr :=
  [.ADDI .x22 .x0 512]

def initRootState (s : MachineState) := initRootOps.foldl execInstrBr s

theorem initRootRun (s : MachineState) (pc : s.pc=5492) 
    (fuel : Nat) (coins : Bool) :
    execute (Trunc.wireImage true) (1+fuel) s coins =
      (do let next ← execute (Trunc.wireImage true) fuel (initRootState s) coins
          return next.charge 1 0) :=
  plainBlock initRootOps 349 (by decide) (by decide) (by intro k; fin_cases k <;> rfl) s pc (by intro k; fin_cases k <;> rfl) fuel coins

theorem edge225 (s : MachineState) (pc : s.pc=4896) (fuel : Nat) (coins : Bool) :
    execute (Trunc.wireImage true) (fuel+1) s coins =
    (do let next ← execute (Trunc.wireImage true) fuel (execInstrBr s (.BNE .x6 .x17 7728)) coins
        return next.charge 1 0) :=
  execute_ordinary_step _ _ _ _ _ _ (fetchAt (Trunc.wireImage true) s 200 (.BNE .x6 .x17 7728) (by decide) pc (by rfl)) (by rfl)

theorem edge293 (s : MachineState) (pc : s.pc=5168) (fuel : Nat) (coins : Bool) :
    execute (Trunc.wireImage true) (fuel+1) s coins =
    (do let next ← execute (Trunc.wireImage true) fuel (execInstrBr s (.BEQ .x7 .x0 56)) coins
        return next.charge 1 0) :=
  execute_ordinary_step _ _ _ _ _ _ (fetchAt (Trunc.wireImage true) s 268 (.BEQ .x7 .x0 56) (by decide) pc (by rfl)) (by rfl)

theorem edge306 (s : MachineState) (pc : s.pc=5220) (fuel : Nat) (coins : Bool) :
    execute (Trunc.wireImage true) (fuel+1) s coins =
    (do let next ← execute (Trunc.wireImage true) fuel (execInstrBr s (.JAL .x0 44)) coins
        return next.charge 1 0) :=
  execute_ordinary_step _ _ _ _ _ _ (fetchAt (Trunc.wireImage true) s 281 (.JAL .x0 44) (by decide) pc (by rfl)) (by rfl)

theorem edge319 (s : MachineState) (pc : s.pc=5272) (fuel : Nat) (coins : Bool) :
    execute (Trunc.wireImage true) (fuel+1) s coins =
    (do let next ← execute (Trunc.wireImage true) fuel (execInstrBr s (.BNE .x27 .x0 7844)) coins
        return next.charge 1 0) :=
  execute_ordinary_step _ _ _ _ _ _ (fetchAt (Trunc.wireImage true) s 294 (.BNE .x27 .x0 7844) (by decide) pc (by rfl)) (by rfl)

theorem edge332 (s : MachineState) (pc : s.pc=5324) (fuel : Nat) (coins : Bool) :
    execute (Trunc.wireImage true) (fuel+1) s coins =
    (do let next ← execute (Trunc.wireImage true) fuel (execInstrBr s (.BEQ .x6 .x0 48)) coins
        return next.charge 1 0) :=
  execute_ordinary_step _ _ _ _ _ _ (fetchAt (Trunc.wireImage true) s 307 (.BEQ .x6 .x0 48) (by decide) pc (by rfl)) (by rfl)

theorem edge333 (s : MachineState) (pc : s.pc=5328) (fuel : Nat) (coins : Bool) :
    execute (Trunc.wireImage true) (fuel+1) s coins =
    (do let next ← execute (Trunc.wireImage true) fuel (execInstrBr s (.BEQ .x7 .x0 8)) coins
        return next.charge 1 0) :=
  execute_ordinary_step _ _ _ _ _ _ (fetchAt (Trunc.wireImage true) s 308 (.BEQ .x7 .x0 8) (by decide) pc (by rfl)) (by rfl)

theorem edge334 (s : MachineState) (pc : s.pc=5332) (fuel : Nat) (coins : Bool) :
    execute (Trunc.wireImage true) (fuel+1) s coins =
    (do let next ← execute (Trunc.wireImage true) fuel (execInstrBr s (.JAL .x0 76)) coins
        return next.charge 1 0) :=
  execute_ordinary_step _ _ _ _ _ _ (fetchAt (Trunc.wireImage true) s 309 (.JAL .x0 76) (by decide) pc (by rfl)) (by rfl)

theorem edge343 (s : MachineState) (pc : s.pc=5368) (fuel : Nat) (coins : Bool) :
    execute (Trunc.wireImage true) (fuel+1) s coins =
    (do let next ← execute (Trunc.wireImage true) fuel (execInstrBr s (.JAL .x0 40)) coins
        return next.charge 1 0) :=
  execute_ordinary_step _ _ _ _ _ _ (fetchAt (Trunc.wireImage true) s 318 (.JAL .x0 40) (by decide) pc (by rfl)) (by rfl)

theorem edge344 (s : MachineState) (pc : s.pc=5372) (fuel : Nat) (coins : Bool) :
    execute (Trunc.wireImage true) (fuel+1) s coins =
    (do let next ← execute (Trunc.wireImage true) fuel (execInstrBr s (.BEQ .x7 .x0 64)) coins
        return next.charge 1 0) :=
  execute_ordinary_step _ _ _ _ _ _ (fetchAt (Trunc.wireImage true) s 319 (.BEQ .x7 .x0 64) (by decide) pc (by rfl)) (by rfl)

theorem edge373 (s : MachineState) (pc : s.pc=5488) (fuel : Nat) (coins : Bool) :
    execute (Trunc.wireImage true) (fuel+1) s coins =
    (do let next ← execute (Trunc.wireImage true) fuel (execInstrBr s (.BNE .x27 .x0 8020)) coins
        return next.charge 1 0) :=
  execute_ordinary_step _ _ _ _ _ _ (fetchAt (Trunc.wireImage true) s 348 (.BNE .x27 .x0 8020) (by decide) pc (by rfl)) (by rfl)

end CommitGolfCandidate.Trunc.Batch
