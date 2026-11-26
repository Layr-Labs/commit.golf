import CommitGolfCandidate.PairBlocks

namespace CommitGolfCandidate.PairCap.Batch

open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 12000

def lengthOps : List Instr :=
  [.ADDI .x6 .x0 35, .SLLI .x6 .x6 11, .ADDI .x6 .x6 0]

def lengthState (s : MachineState) := lengthOps.foldl execInstrBr s

theorem lengthRun (s : MachineState) (pc : s.pc=4984) 
    (fuel : Nat) (coins : Bool) :
    execute (submission.image .check) (3+fuel) s coins =
      (do let next ← execute (submission.image .check) fuel (lengthState s) coins
          return next.charge 3 0) :=
  plainBlock lengthOps 222 (by decide) (by decide) (by intro k; fin_cases k <;> rfl) s pc (by intro k; fin_cases k <;> rfl) fuel coins

def readyOps : List Instr :=
  [.ADDI .x6 .x0 33, .SLLI .x6 .x6 11, .ADDI .x6 .x6 0, .ADD .x19 .x25 .x6, .ADDI .x21 .x0 256, .ADDI .x30 .x0 16]

def readyState (s : MachineState) := readyOps.foldl execInstrBr s

theorem readyRun (s : MachineState) (pc : s.pc=5000) 
    (fuel : Nat) (coins : Bool) :
    execute (submission.image .check) (6+fuel) s coins =
      (do let next ← execute (submission.image .check) fuel (readyState s) coins
          return next.charge 6 0) :=
  plainBlock readyOps 226 (by decide) (by decide) (by intro k; fin_cases k <;> rfl) s pc (by intro k; fin_cases k <;> rfl) fuel coins

def bucketOps : List Instr :=
  [.ADDI .x22 .x0 6, .SLLI .x22 .x22 11, .ADDI .x22 .x22 0, .ADD .x22 .x22 .x20, .LBU .x7 .x22 0, .SRLI .x6 .x20 1, .ADD .x6 .x20 .x6, .SLLI .x6 .x6 5, .ADDI .x23 .x0 8, .SLLI .x23 .x23 11, .ADDI .x23 .x23 0, .ADD .x23 .x23 .x6]

def bucketState (s : MachineState) := bucketOps.foldl execInstrBr s

theorem bucketRun (s : MachineState) (pc : s.pc=5220) (safe : safeSteps bucketOps s)
    (fuel : Nat) (coins : Bool) :
    execute (submission.image .check) (12+fuel) s coins =
      (do let next ← execute (submission.image .check) fuel (bucketState s) coins
          return next.charge 12 0) :=
  plainBlock bucketOps 281 (by decide) (by decide) (by intro k; fin_cases k <;> rfl) s pc safe fuel coins

def storeOps : List Instr :=
  [.ADDI .x7 .x0 1, .SB .x22 .x7 0, .LD .x6 .x21 0, .SD .x23 .x6 0, .LD .x6 .x21 8, .SD .x23 .x6 8, .LD .x6 .x21 16, .SD .x23 .x6 16, .LD .x6 .x21 24, .SD .x23 .x6 24]

def storeState (s : MachineState) := storeOps.foldl execInstrBr s

theorem storeRun (s : MachineState) (pc : s.pc=5324) (safe : safeSteps storeOps s)
    (fuel : Nat) (coins : Bool) :
    execute (submission.image .check) (10+fuel) s coins =
      (do let next ← execute (submission.image .check) fuel (storeState s) coins
          return next.charge 10 0) :=
  plainBlock storeOps 307 (by decide) (by decide) (by intro k; fin_cases k <;> rfl) s pc safe fuel coins

def recordNextOps : List Instr :=
  [.ADDI .x24 .x24 8, .ADDI .x27 .x27 4095]

def recordNextState (s : MachineState) := recordNextOps.foldl execInstrBr s

theorem recordNextRun (s : MachineState) (pc : s.pc=5364) 
    (fuel : Nat) (coins : Bool) :
    execute (submission.image .check) (2+fuel) s coins =
      (do let next ← execute (submission.image .check) fuel (recordNextState s) coins
          return next.charge 2 0) :=
  plainBlock recordNextOps 317 (by decide) (by decide) (by intro k; fin_cases k <;> rfl) s pc (by intro k; fin_cases k <;> rfl) fuel coins

def initPairsOps : List Instr :=
  [.ADDI .x22 .x0 6, .SLLI .x22 .x22 11, .ADDI .x22 .x22 0, .ADDI .x23 .x0 8, .SLLI .x23 .x23 11, .ADDI .x23 .x23 0, .ADDI .x24 .x0 2, .SLLI .x24 .x24 11, .ADDI .x24 .x24 512, .ADDI .x27 .x0 128]

def initPairsState (s : MachineState) := initPairsOps.foldl execInstrBr s

theorem initPairsRun (s : MachineState) (pc : s.pc=5376) 
    (fuel : Nat) (coins : Bool) :
    execute (submission.image .check) (10+fuel) s coins =
      (do let next ← execute (submission.image .check) fuel (initPairsState s) coins
          return next.charge 10 0) :=
  plainBlock initPairsOps 320 (by decide) (by decide) (by intro k; fin_cases k <;> rfl) s pc (by intro k; fin_cases k <;> rfl) fuel coins

def marksOps : List Instr :=
  [.LBU .x6 .x22 0, .LBU .x7 .x22 1]

def marksState (s : MachineState) := marksOps.foldl execInstrBr s

theorem marksRun (s : MachineState) (pc : s.pc=5416) (safe : safeSteps marksOps s)
    (fuel : Nat) (coins : Bool) :
    execute (submission.image .check) (2+fuel) s coins =
      (do let next ← execute (submission.image .check) fuel (marksState s) coins
          return next.charge 2 0) :=
  plainBlock marksOps 330 (by decide) (by decide) (by intro k; fin_cases k <;> rfl) s pc safe fuel coins

def fillRightOps : List Instr :=
  [.LD .x6 .x19 0, .SD .x23 .x6 32, .LD .x6 .x19 8, .SD .x23 .x6 40, .LD .x6 .x19 16, .SD .x23 .x6 48, .LD .x6 .x19 24, .SD .x23 .x6 56]

def fillRightState (s : MachineState) := fillRightOps.foldl execInstrBr s

theorem fillRightRun (s : MachineState) (pc : s.pc=5436) (safe : safeSteps fillRightOps s)
    (fuel : Nat) (coins : Bool) :
    execute (submission.image .check) (8+fuel) s coins =
      (do let next ← execute (submission.image .check) fuel (fillRightState s) coins
          return next.charge 8 0) :=
  plainBlock fillRightOps 335 (by decide) (by decide) (by intro k; fin_cases k <;> rfl) s pc safe fuel coins

def fillLeftOps : List Instr :=
  [.LD .x6 .x19 0, .SD .x23 .x6 0, .LD .x6 .x19 8, .SD .x23 .x6 8, .LD .x6 .x19 16, .SD .x23 .x6 16, .LD .x6 .x19 24, .SD .x23 .x6 24]

def fillLeftState (s : MachineState) := fillLeftOps.foldl execInstrBr s

theorem fillLeftRun (s : MachineState) (pc : s.pc=5476) (safe : safeSteps fillLeftOps s)
    (fuel : Nat) (coins : Bool) :
    execute (submission.image .check) (8+fuel) s coins =
      (do let next ← execute (submission.image .check) fuel (fillLeftState s) coins
          return next.charge 8 0) :=
  plainBlock fillLeftOps 345 (by decide) (by decide) (by intro k; fin_cases k <;> rfl) s pc safe fuel coins

def hashSetupOps : List Instr :=
  [.ADDI .x5 .x0 0, .ADDI .x10 .x23 0, .ADDI .x11 .x0 96, .ADDI .x12 .x24 0, .ADDI .x13 .x0 0]

def hashSetupState (s : MachineState) := hashSetupOps.foldl execInstrBr s

theorem hashSetupRun (s : MachineState) (pc : s.pc=5508) 
    (fuel : Nat) (coins : Bool) :
    execute (submission.image .check) (5+fuel) s coins =
      (do let next ← execute (submission.image .check) fuel (hashSetupState s) coins
          return next.charge 5 0) :=
  plainBlock hashSetupOps 353 (by decide) (by decide) (by intro k; fin_cases k <;> rfl) s pc (by intro k; fin_cases k <;> rfl) fuel coins

def useParentOps : List Instr :=
  [.LD .x6 .x19 0, .SD .x24 .x6 0, .LD .x6 .x19 8, .SD .x24 .x6 8, .LD .x6 .x19 16, .SD .x24 .x6 16, .LD .x6 .x19 24, .SD .x24 .x6 24]

def useParentState (s : MachineState) := useParentOps.foldl execInstrBr s

theorem useParentRun (s : MachineState) (pc : s.pc=5536) (safe : safeSteps useParentOps s)
    (fuel : Nat) (coins : Bool) :
    execute (submission.image .check) (8+fuel) s coins =
      (do let next ← execute (submission.image .check) fuel (useParentState s) coins
          return next.charge 8 0) :=
  plainBlock useParentOps 360 (by decide) (by decide) (by intro k; fin_cases k <;> rfl) s pc safe fuel coins

def pairNextOps : List Instr :=
  [.ADDI .x19 .x19 32, .ADDI .x22 .x22 2, .ADDI .x23 .x23 96, .ADDI .x24 .x24 32, .ADDI .x27 .x27 4095]

def pairNextState (s : MachineState) := pairNextOps.foldl execInstrBr s

theorem pairNextRun (s : MachineState) (pc : s.pc=5568) 
    (fuel : Nat) (coins : Bool) :
    execute (submission.image .check) (5+fuel) s coins =
      (do let next ← execute (submission.image .check) fuel (pairNextState s) coins
          return next.charge 5 0) :=
  plainBlock pairNextOps 368 (by decide) (by decide) (by intro k; fin_cases k <;> rfl) s pc (by intro k; fin_cases k <;> rfl) fuel coins

def initRootOps : List Instr :=
  [.ADDI .x22 .x0 512]

def initRootState (s : MachineState) := initRootOps.foldl execInstrBr s

theorem initRootRun (s : MachineState) (pc : s.pc=5592) 
    (fuel : Nat) (coins : Bool) :
    execute (submission.image .check) (1+fuel) s coins =
      (do let next ← execute (submission.image .check) fuel (initRootState s) coins
          return next.charge 1 0) :=
  plainBlock initRootOps 374 (by decide) (by decide) (by intro k; fin_cases k <;> rfl) s pc (by intro k; fin_cases k <;> rfl) fuel coins

theorem edge225 (s : MachineState) (pc : s.pc=4996) (fuel : Nat) (coins : Bool) :
    execute (submission.image .check) (fuel+1) s coins =
    (do let next ← execute (submission.image .check) fuel (execInstrBr s (.BNE .x6 .x17 7628)) coins
        return next.charge 1 0) :=
  execute_ordinary_step _ _ _ _ _ _ (patchedFetch s 225 _ (by decide) pc (by rfl)) (by rfl)

theorem edge293 (s : MachineState) (pc : s.pc=5268) (fuel : Nat) (coins : Bool) :
    execute (submission.image .check) (fuel+1) s coins =
    (do let next ← execute (submission.image .check) fuel (execInstrBr s (.BEQ .x7 .x0 56)) coins
        return next.charge 1 0) :=
  execute_ordinary_step _ _ _ _ _ _ (patchedFetch s 293 _ (by decide) pc (by rfl)) (by rfl)

theorem edge306 (s : MachineState) (pc : s.pc=5320) (fuel : Nat) (coins : Bool) :
    execute (submission.image .check) (fuel+1) s coins =
    (do let next ← execute (submission.image .check) fuel (execInstrBr s (.JAL .x0 44)) coins
        return next.charge 1 0) :=
  execute_ordinary_step _ _ _ _ _ _ (patchedFetch s 306 _ (by decide) pc (by rfl)) (by rfl)

theorem edge319 (s : MachineState) (pc : s.pc=5372) (fuel : Nat) (coins : Bool) :
    execute (submission.image .check) (fuel+1) s coins =
    (do let next ← execute (submission.image .check) fuel (execInstrBr s (.BNE .x27 .x0 7844)) coins
        return next.charge 1 0) :=
  execute_ordinary_step _ _ _ _ _ _ (patchedFetch s 319 _ (by decide) pc (by rfl)) (by rfl)

theorem edge332 (s : MachineState) (pc : s.pc=5424) (fuel : Nat) (coins : Bool) :
    execute (submission.image .check) (fuel+1) s coins =
    (do let next ← execute (submission.image .check) fuel (execInstrBr s (.BEQ .x6 .x0 48)) coins
        return next.charge 1 0) :=
  execute_ordinary_step _ _ _ _ _ _ (patchedFetch s 332 _ (by decide) pc (by rfl)) (by rfl)

theorem edge333 (s : MachineState) (pc : s.pc=5428) (fuel : Nat) (coins : Bool) :
    execute (submission.image .check) (fuel+1) s coins =
    (do let next ← execute (submission.image .check) fuel (execInstrBr s (.BEQ .x7 .x0 8)) coins
        return next.charge 1 0) :=
  execute_ordinary_step _ _ _ _ _ _ (patchedFetch s 333 _ (by decide) pc (by rfl)) (by rfl)

theorem edge334 (s : MachineState) (pc : s.pc=5432) (fuel : Nat) (coins : Bool) :
    execute (submission.image .check) (fuel+1) s coins =
    (do let next ← execute (submission.image .check) fuel (execInstrBr s (.JAL .x0 76)) coins
        return next.charge 1 0) :=
  execute_ordinary_step _ _ _ _ _ _ (patchedFetch s 334 _ (by decide) pc (by rfl)) (by rfl)

theorem edge343 (s : MachineState) (pc : s.pc=5468) (fuel : Nat) (coins : Bool) :
    execute (submission.image .check) (fuel+1) s coins =
    (do let next ← execute (submission.image .check) fuel (execInstrBr s (.JAL .x0 40)) coins
        return next.charge 1 0) :=
  execute_ordinary_step _ _ _ _ _ _ (patchedFetch s 343 _ (by decide) pc (by rfl)) (by rfl)

theorem edge344 (s : MachineState) (pc : s.pc=5472) (fuel : Nat) (coins : Bool) :
    execute (submission.image .check) (fuel+1) s coins =
    (do let next ← execute (submission.image .check) fuel (execInstrBr s (.BEQ .x7 .x0 64)) coins
        return next.charge 1 0) :=
  execute_ordinary_step _ _ _ _ _ _ (patchedFetch s 344 _ (by decide) pc (by rfl)) (by rfl)

theorem edge359 (s : MachineState) (pc : s.pc=5532) (fuel : Nat) (coins : Bool) :
    execute (submission.image .check) (fuel+1) s coins =
    (do let next ← execute (submission.image .check) fuel (execInstrBr s (.JAL .x0 36)) coins
        return next.charge 1 0) :=
  execute_ordinary_step _ _ _ _ _ _ (patchedFetch s 359 _ (by decide) pc (by rfl)) (by rfl)

theorem edge373 (s : MachineState) (pc : s.pc=5588) (fuel : Nat) (coins : Bool) :
    execute (submission.image .check) (fuel+1) s coins =
    (do let next ← execute (submission.image .check) fuel (execInstrBr s (.BNE .x27 .x0 8020)) coins
        return next.charge 1 0) :=
  execute_ordinary_step _ _ _ _ _ _ (patchedFetch s 373 _ (by decide) pc (by rfl)) (by rfl)

end CommitGolfCandidate.PairCap.Batch
