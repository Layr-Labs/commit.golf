import CommitGolfCandidate.TwoPermutationPackedCheckerSteps
import CommitGolfCandidate.TwoPermutationCheckerLowerCode
namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 1100000

private theorem hop_one (s t : MachineState) (i : Instr)
    (f : fetch packedImage s=some (.base i)) (step : ordinaryStep s (.base i)=some t)
    (cost : instructionCycles (.base i)=1) : GroupHop s t 1 := by
  intro fuel
  rw [Nat.add_comm 1 fuel,execute_ordinary_step _ _ _ _ _ _ f step,cost]

def width (leaf : Bool) : Nat := if leaf then 32 else 30
def dispatchStart (leaf even : Bool) : Nat :=
  if leaf then (if even then 192 else 151) else (if even then 108 else 68)

def dispatch (s : MachineState) (leaf even : Bool) : MachineState :=
  ((s.setReg .x30 (BitVec.ofNat 64 (width leaf))).setReg .x7 (s.getReg .x6 &&& 1)).setPC
    (BitVec.ofNat 64 (4096+4*dispatchStart leaf even))

private theorem dispatch_false_false (s : MachineState) (pc : s.pc=4348)
    (counter : BitVec.ult (s.getReg .x29) 13 = true)
    (parity : s.getReg .x6 &&& 1 ≠ 0) :
    GroupHop s (dispatch s false false) 5 := by
  let a := (s.setReg .x30 13).setPC 4352
  have h0 : GroupHop s a 1 := by
    apply hop_one _ _ (.ADDI .x30 .x0 13)
    · exact fetch_at s 63 _ (by decide) pc rfl
    · simp [a,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend12,signExtend13,
        MachineState.getReg,MachineState.setReg,MachineState.setPC,pc] at counter parity ⊢
      <;> simp_all
    · rfl
  let b := (a).setPC 4356
  have h1 : GroupHop a b 1 := by
    apply hop_one _ _ (.BGEU .x29 .x30 336)
    · exact fetch_at a 64 _ (by decide) rfl rfl
    · simp [a,b,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend12,signExtend13,
        MachineState.getReg,MachineState.setReg,MachineState.setPC,pc] at counter parity ⊢
      <;> simp_all
    · rfl
  let c := (b.setReg .x30 30).setPC 4360
  have h2 : GroupHop b c 1 := by
    apply hop_one _ _ (.ADDI .x30 .x0 30)
    · exact fetch_at b 65 _ (by decide) rfl rfl
    · simp [a,b,c,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend12,signExtend13,
        MachineState.getReg,MachineState.setReg,MachineState.setPC,pc] at counter parity ⊢
      <;> simp_all
    · rfl
  let d := (c.setReg .x7 (s.getReg .x6 &&& 1)).setPC 4364
  have h3 : GroupHop c d 1 := by
    apply hop_one _ _ (.ANDI .x7 .x6 1)
    · exact fetch_at c 66 _ (by decide) rfl rfl
    · simp [a,b,c,d,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend12,signExtend13,
        MachineState.getReg,MachineState.setReg,MachineState.setPC,pc] at counter parity ⊢
      <;> simp_all
    · rfl
  let e := (d).setPC 4368
  have h4 : GroupHop d e 1 := by
    apply hop_one _ _ (.BEQ .x7 .x0 164)
    · exact fetch_at d 67 _ (by decide) rfl rfl
    · simp [a,b,c,d,e,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend12,signExtend13,
        MachineState.getReg,MachineState.setReg,MachineState.setPC,pc] at counter parity ⊢
      <;> simp_all
    · rfl
  have run := (((GroupHop.thenDo h0 h1).thenDo h2).thenDo h3).thenDo h4
  have endState : e=dispatch s false false := by
    simp [a,b,c,d,e,dispatch,width,dispatchStart,MachineState.setReg,MachineState.setPC]
    funext r
    by_cases h : r=.x30 <;> simp [h]
  rw [endState] at run
  exact run

private theorem dispatch_false_true (s : MachineState) (pc : s.pc=4348)
    (counter : BitVec.ult (s.getReg .x29) 13 = true)
    (parity : s.getReg .x6 &&& 1 = 0) :
    GroupHop s (dispatch s false true) 5 := by
  let a := (s.setReg .x30 13).setPC 4352
  have h0 : GroupHop s a 1 := by
    apply hop_one _ _ (.ADDI .x30 .x0 13)
    · exact fetch_at s 63 _ (by decide) pc rfl
    · simp [a,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend12,signExtend13,
        MachineState.getReg,MachineState.setReg,MachineState.setPC,pc] at counter parity ⊢
      <;> simp_all
    · rfl
  let b := (a).setPC 4356
  have h1 : GroupHop a b 1 := by
    apply hop_one _ _ (.BGEU .x29 .x30 336)
    · exact fetch_at a 64 _ (by decide) rfl rfl
    · simp [a,b,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend12,signExtend13,
        MachineState.getReg,MachineState.setReg,MachineState.setPC,pc] at counter parity ⊢
      <;> simp_all
    · rfl
  let c := (b.setReg .x30 30).setPC 4360
  have h2 : GroupHop b c 1 := by
    apply hop_one _ _ (.ADDI .x30 .x0 30)
    · exact fetch_at b 65 _ (by decide) rfl rfl
    · simp [a,b,c,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend12,signExtend13,
        MachineState.getReg,MachineState.setReg,MachineState.setPC,pc] at counter parity ⊢
      <;> simp_all
    · rfl
  let d := (c.setReg .x7 (s.getReg .x6 &&& 1)).setPC 4364
  have h3 : GroupHop c d 1 := by
    apply hop_one _ _ (.ANDI .x7 .x6 1)
    · exact fetch_at c 66 _ (by decide) rfl rfl
    · simp [a,b,c,d,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend12,signExtend13,
        MachineState.getReg,MachineState.setReg,MachineState.setPC,pc] at counter parity ⊢
      <;> simp_all
    · rfl
  let e := (d).setPC 4528
  have h4 : GroupHop d e 1 := by
    apply hop_one _ _ (.BEQ .x7 .x0 164)
    · exact fetch_at d 67 _ (by decide) rfl rfl
    · simp [a,b,c,d,e,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend12,signExtend13,
        MachineState.getReg,MachineState.setReg,MachineState.setPC,pc] at counter parity ⊢
      <;> simp_all
    · rfl
  have run := (((GroupHop.thenDo h0 h1).thenDo h2).thenDo h3).thenDo h4
  have endState : e=dispatch s false true := by
    simp [a,b,c,d,e,dispatch,width,dispatchStart,MachineState.setReg,MachineState.setPC]
    funext r
    by_cases h : r=.x30 <;> simp [h]
  rw [endState] at run
  exact run

private theorem dispatch_true_false (s : MachineState) (pc : s.pc=4348)
    (counter : BitVec.ult (s.getReg .x29) 13 = false)
    (parity : s.getReg .x6 &&& 1 ≠ 0) :
    GroupHop s (dispatch s true false) 5 := by
  let a := (s.setReg .x30 13).setPC 4352
  have h0 : GroupHop s a 1 := by
    apply hop_one _ _ (.ADDI .x30 .x0 13)
    · exact fetch_at s 63 _ (by decide) pc rfl
    · simp [a,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend12,signExtend13,
        MachineState.getReg,MachineState.setReg,MachineState.setPC,pc] at counter parity ⊢
      <;> simp_all
    · rfl
  let b := (a).setPC 4688
  have h1 : GroupHop a b 1 := by
    apply hop_one _ _ (.BGEU .x29 .x30 336)
    · exact fetch_at a 64 _ (by decide) rfl rfl
    · simp [a,b,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend12,signExtend13,
        MachineState.getReg,MachineState.setReg,MachineState.setPC,pc] at counter parity ⊢
      <;> simp_all
    · rfl
  let c := (b.setReg .x30 32).setPC 4692
  have h2 : GroupHop b c 1 := by
    apply hop_one _ _ (.ADDI .x30 .x0 32)
    · exact fetch_at b 148 _ (by decide) rfl rfl
    · simp [a,b,c,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend12,signExtend13,
        MachineState.getReg,MachineState.setReg,MachineState.setPC,pc] at counter parity ⊢
      <;> simp_all
    · rfl
  let d := (c.setReg .x7 (s.getReg .x6 &&& 1)).setPC 4696
  have h3 : GroupHop c d 1 := by
    apply hop_one _ _ (.ANDI .x7 .x6 1)
    · exact fetch_at c 149 _ (by decide) rfl rfl
    · simp [a,b,c,d,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend12,signExtend13,
        MachineState.getReg,MachineState.setReg,MachineState.setPC,pc] at counter parity ⊢
      <;> simp_all
    · rfl
  let e := (d).setPC 4700
  have h4 : GroupHop d e 1 := by
    apply hop_one _ _ (.BEQ .x7 .x0 168)
    · exact fetch_at d 150 _ (by decide) rfl rfl
    · simp [a,b,c,d,e,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend12,signExtend13,
        MachineState.getReg,MachineState.setReg,MachineState.setPC,pc] at counter parity ⊢
      <;> simp_all
    · rfl
  have run := (((GroupHop.thenDo h0 h1).thenDo h2).thenDo h3).thenDo h4
  have endState : e=dispatch s true false := by
    simp [a,b,c,d,e,dispatch,width,dispatchStart,MachineState.setReg,MachineState.setPC]
    funext r
    by_cases h : r=.x30 <;> simp [h]
  rw [endState] at run
  exact run

private theorem dispatch_true_true (s : MachineState) (pc : s.pc=4348)
    (counter : BitVec.ult (s.getReg .x29) 13 = false)
    (parity : s.getReg .x6 &&& 1 = 0) :
    GroupHop s (dispatch s true true) 5 := by
  let a := (s.setReg .x30 13).setPC 4352
  have h0 : GroupHop s a 1 := by
    apply hop_one _ _ (.ADDI .x30 .x0 13)
    · exact fetch_at s 63 _ (by decide) pc rfl
    · simp [a,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend12,signExtend13,
        MachineState.getReg,MachineState.setReg,MachineState.setPC,pc] at counter parity ⊢
      <;> simp_all
    · rfl
  let b := (a).setPC 4688
  have h1 : GroupHop a b 1 := by
    apply hop_one _ _ (.BGEU .x29 .x30 336)
    · exact fetch_at a 64 _ (by decide) rfl rfl
    · simp [a,b,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend12,signExtend13,
        MachineState.getReg,MachineState.setReg,MachineState.setPC,pc] at counter parity ⊢
      <;> simp_all
    · rfl
  let c := (b.setReg .x30 32).setPC 4692
  have h2 : GroupHop b c 1 := by
    apply hop_one _ _ (.ADDI .x30 .x0 32)
    · exact fetch_at b 148 _ (by decide) rfl rfl
    · simp [a,b,c,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend12,signExtend13,
        MachineState.getReg,MachineState.setReg,MachineState.setPC,pc] at counter parity ⊢
      <;> simp_all
    · rfl
  let d := (c.setReg .x7 (s.getReg .x6 &&& 1)).setPC 4696
  have h3 : GroupHop c d 1 := by
    apply hop_one _ _ (.ANDI .x7 .x6 1)
    · exact fetch_at c 149 _ (by decide) rfl rfl
    · simp [a,b,c,d,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend12,signExtend13,
        MachineState.getReg,MachineState.setReg,MachineState.setPC,pc] at counter parity ⊢
      <;> simp_all
    · rfl
  let e := (d).setPC 4864
  have h4 : GroupHop d e 1 := by
    apply hop_one _ _ (.BEQ .x7 .x0 168)
    · exact fetch_at d 150 _ (by decide) rfl rfl
    · simp [a,b,c,d,e,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend12,signExtend13,
        MachineState.getReg,MachineState.setReg,MachineState.setPC,pc] at counter parity ⊢
      <;> simp_all
    · rfl
  have run := (((GroupHop.thenDo h0 h1).thenDo h2).thenDo h3).thenDo h4
  have endState : e=dispatch s true true := by
    simp [a,b,c,d,e,dispatch,width,dispatchStart,MachineState.setReg,MachineState.setPC]
    funext r
    by_cases h : r=.x30 <;> simp [h]
  rw [endState] at run
  exact run

/-- Words 63–67 (or 148–150): `addi x30,x0,13; bgeu x29,x30,+336` sends `x29 ≥ 13` (loop levels 0 and 1)
to the 32-byte sibling path, then the sibling width and the node parity pick one of four copy orders. -/
theorem execute_dispatch (s : MachineState) (leaf even : Bool) (pc : s.pc=4348)
    (counter : (leaf=true) ↔ BitVec.ult (s.getReg .x29) 13 = false) (parity : (even=true) ↔ s.getReg .x6 &&& 1=0) :
    GroupHop s (dispatch s leaf even) 5 := by
  have narrow (no : leaf = false) : BitVec.ult (s.getReg .x29) 13 = true := by
    cases h : BitVec.ult (s.getReg .x29) 13
    · exact absurd (counter.mpr h) (by rw [no]; decide)
    · rfl
  cases leaf <;> cases even
  · exact dispatch_false_false s pc (narrow rfl) (fun h => Bool.noConfusion (parity.mpr h))
  · exact dispatch_false_true s pc (narrow rfl) (parity.mp rfl)
  · exact dispatch_true_false s pc (counter.mp rfl) (fun h => Bool.noConfusion (parity.mpr h))
  · exact dispatch_true_true s pc (counter.mp rfl) (parity.mp rfl)

def latch (state : MachineState) : MachineState :=
  (((state.setReg .x21 (state.getReg .x21 + state.getReg .x30)).setReg .x6 (state.getReg .x6 >>> 1)).setReg
    .x29 (state.getReg .x29 - 1)).setPC (if state.getReg .x29 - 1 = 0 then 0x13c0 else 0x10fc)

theorem execute_latch (state : MachineState) (pc : state.pc = 0x13b0)
    (fuel : Nat) :
    execute packedImage (4 + fuel) state false =
      (do let result ← execute packedImage fuel (latch state) false
          return result.charge 4 0) := by
  let advanced := (state.setReg .x21 (state.getReg .x21 + state.getReg .x30)).setPC 0x13b4
  let shifted := (advanced.setReg .x6 (state.getReg .x6 >>> 1)).setPC 0x13b8
  let next := (shifted.setReg .x29 (state.getReg .x29 - 1)).setPC 0x13bc
  have f0 : fetch packedImage state = some (.base (.ADD .x21 .x21 .x30)) := by
    apply fetch_at _ 236 _ (by decide) pc; rfl
  have f1 : fetch packedImage advanced = some (.base (.SRLI .x6 .x6 1)) := by
    apply fetch_at _ 237 _ (by decide) rfl; rfl
  have f2 : fetch packedImage shifted = some (.base (.ADDI .x29 .x29 4095)) := by
    apply fetch_at _ 238 _ (by decide) rfl; rfl
  have f3 : fetch packedImage next = some (.base (.BNE .x29 .x0 7488)) := by
    apply fetch_at _ 239 _ (by decide) rfl; rfl
  have s0 : ordinaryStep state (.base (.ADD .x21 .x21 .x30)) = some advanced := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, advanced, pc]
  have s1 : ordinaryStep advanced (.base (.SRLI .x6 .x6 1)) = some shifted := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, advanced, shifted,
      MachineState.getReg, MachineState.setReg, MachineState.setPC]
  have s2 : ordinaryStep shifted (.base (.ADDI .x29 .x29 4095)) = some next := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, advanced, shifted, next,
      MachineState.getReg, MachineState.setReg, MachineState.setPC, BitVec.sub_eq_add_neg]
  have s3 : ordinaryStep next (.base (.BNE .x29 .x0 7488)) = some (latch state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13,
      advanced, shifted, next, latch, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    split <;> simp_all
  rw [Nat.add_comm 4 fuel]
  simp only [execute, f0, s0, f1, s1, f2, s2, f3, s3, instructionCycles, bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

/-- The state at word 234 for loop levels 0..4: word 232 jumps to 577 (`addi x10,x24,0; addi x7,x0,10;
bgeu x29,x7` back to 233), then 233 `addi x12,x23,0`. -/
def hashSetup (state : MachineState) : MachineState :=
  (((state.setReg .x10 (state.getReg .x24)).setReg .x7 10).setReg .x12 (state.getReg .x23)).setPC 0x13a8

theorem execute_hash_setup (state : MachineState) (pc : state.pc = 0x13a0)
    (counter : BitVec.ult (state.getReg .x29) 10 = false) (fuel : Nat) :
    execute packedImage (5+fuel) state false =
      (do let result ← execute packedImage fuel (hashSetup state) false
          return result.charge 5 0) := by
  let s1 := state.setPC (BitVec.ofNat 64 (4096+4*577))
  let s2 := (state.setReg .x10 (state.getReg .x24)).setPC (BitVec.ofNat 64 (4096+4*578))
  let s3 := ((state.setReg .x10 (state.getReg .x24)).setReg .x7 10).setPC (BitVec.ofNat 64 (4096+4*579))
  let s4 := ((state.setReg .x10 (state.getReg .x24)).setReg .x7 10).setPC (BitVec.ofNat 64 (4096+4*233))
  have j0 : GroupHop state s1 1 := by
    apply hop_one _ _ (.JAL .x0 1380)
    · exact fetch_at state 232 _ (by decide) pc rfl
    · show some (execInstrBr state (.JAL .x0 1380)) = some s1
      rw [show execInstrBr state (.JAL .x0 1380) = state.setPC (state.pc + signExtend21 1380) from rfl, pc]
      rfl
    · rfl
  have j1 : GroupHop s1 s2 1 := by
    apply hop_one _ _ (.ADDI .x10 .x24 0)
    · exact fetch_at s1 577 _ (by decide) rfl rfl
    · simp [s1, s2, ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
        MachineState.getReg_setPC]
      rfl
    · rfl
  have j2 : GroupHop s2 s3 1 := by
    apply hop_one _ _ (.ADDI .x7 .x0 10)
    · exact fetch_at s2 578 _ (by decide) rfl rfl
    · show some (execInstrBr s2 (.ADDI .x7 .x0 10)) = some s3
      rfl
    · rfl
  have x29 : s3.getReg .x29 = state.getReg .x29 := by
    simp only [s3, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x29),
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x29)]
  have x7 : s3.getReg .x7 = 10 := by
    simp only [s3, MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : Reg.x7 ≠ .x0)]
  have j3 : GroupHop s3 s4 1 := by
    apply hop_one _ _ (.BGEU .x29 .x7 0x1a98)
    · exact fetch_at s3 579 _ (by decide) rfl rfl
    · have taken : (¬ BitVec.ult (s3.getReg .x29) (s3.getReg .x7) = true) := by
        rw [x29, x7]
        show ¬ BitVec.ult (state.getReg .x29) 10 = true
        rw [counter]
        decide
      have s3pc : s3.pc = BitVec.ofNat 64 (4096+4*579) := rfl
      have landing : s3.pc + signExtend13 0x1a98 = BitVec.ofNat 64 (4096+4*233) := by rw [s3pc]; rfl
      show some (execInstrBr s3 (.BGEU .x29 .x7 0x1a98)) = some s4
      simp only [execInstrBr, taken, if_true, ite_true, not_false_eq_true, landing]
      rfl
    · rfl
  have j4 : GroupHop s4 (hashSetup state) 1 := by
    apply hop_one _ _ (.ADDI .x12 .x23 0)
    · exact fetch_at s4 233 _ (by decide) rfl rfl
    · simp [s4, ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, hashSetup,
        MachineState.getReg_setPC, Opening.getReg_setReg]
      rfl
    · rfl
  exact (((j0.thenDo j1).thenDo j2).thenDo j3).thenDo j4 fuel

end TwoPermutationPrototype.Packed.Checker
