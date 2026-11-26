import DepthPrototype.BatchMachine
import CommitGolf.Programs

/-! Actual-image/fuel regressions for the isolated instruction prototype.
The fixtures provide explicit initial RAM, rather than a whole submitted ABI or
an unpriced way for a solver to prepare descriptors. No private coins occur in
these programs, so the existing public-only handler supplies deterministic tests.
-/

namespace DepthPrototype.BatchMachineTests

open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open DepthPrototype.Batch DepthPrototype.BatchMachine

set_option exponentiation.threshold 2048
set_option maxRecDepth 20000

private def oracle : Oracle := ⟨fun _ => 7, Equiv.refl _⟩

private def tableMemory (malformed : Bool) (address : BitVec 64) : BitVec 64 :=
  match address.toNat with
  | 2064 => 64
  | 2072 => 512
  | 2096 => if malformed then 63 else 64
  | 2104 => 544
  | _ => 0

/-- Two compression descriptors at 2048; all inputs are initially zero. -/
private def fixture (count : Nat := 2) (malformed : Bool := false)
    (selector : Nat := 0) : MachineState :=
  { initialMachine with
    regs := fun reg =>
      match reg with
      | .x5 => BitVec.ofNat 64 selector
      | .x10 => 2048
      | .x11 => BitVec.ofNat 64 count
      | _ => 0
    mem := tableMemory malformed }

/-- Set t0=3, batch ECALL, then set the ordinary HALT selector/status and halt. -/
private def program : Image :=
  ⟨[0x00300293, 0x00000073, 0x00100293, 0x00000513, 0x00000073], []⟩

private def singleCall : Image := ⟨[0x00000073], []⟩

private def publicEvaluation {α : Type} (computation : OracleComp World α) : α × Nat :=
  oracle.eval (simulateQ checkHandler computation)

private def observe (mode : Mode) (image : Image) (steps : Nat) (state : MachineState) :
    Exit × Nat × Nat × Nat × Nat :=
  let (execution, counted) := publicEvaluation (BatchMachine.execute mode image steps state false)
  (execution.result.exit, execution.result.cycles, execution.result.oracleCalls,
    execution.oracleRounds, counted)

example : loadDescriptors (fixture 2) 2048 2 =
    some [⟨0, 0, 64, 512⟩, ⟨0, 0, 64, 544⟩] := by
  decide +kernel

-- 27 cycles for the two-call macro, plus four ordinary/setup/HALT instructions.
example : observe .batched program 5 (fixture 2) = (.success, 31, 2, 1, 2) := by
  decide +kernel

example :
    let final := (publicEvaluation (BatchMachine.execute .batched program 5 (fixture 2) false)).1.result.state
    final.getByte 512 = 7 ∧ final.getByte 544 = 7 := by
  decide +kernel

-- The first output destroys the second descriptor in RAM. Its original four words
-- and input bytes were already captured, so the second call still succeeds.
private def descriptorAlias : MachineState :=
  { fixture 2 with
    mem := fun address => if address.toNat = 2072 then 2080 else tableMemory false address }

example : observe .batched program 5 descriptorAlias = (.success, 31, 2, 1, 2) := by
  decide +kernel

example :
    let final := (publicEvaluation (BatchMachine.execute .batched program 5 descriptorAlias false)).1.result.state
    final.getByte 544 = 7 := by
  decide +kernel

-- A legacy image with the new selector fails; compatibility is not assumed.
example : observe .legacy program 5 (fixture 2) = (.failure, 2, 0, 0, 0) := by
  decide +kernel

-- Exhausting fuel after the batch preserves its actual work/call/round counters.
example : observe .batched singleCall 1 (fixture 2 false 3) =
    (.unfinished, 27, 2, 1, 2) := by
  decide +kernel

-- The entire descriptor list is checked before effects, including a bad second entry.
example : observe .batched program 5 (fixture 2 true) = (.failure, 12, 0, 0, 0) := by
  decide +kernel

-- Empty batches still advance PC and consume instruction fuel and the entry cycle.
example : observe .batched program 5 (fixture 0) = (.success, 5, 0, 0, 0) := by
  decide +kernel

-- The count cap is checked before any List.range allocation or descriptor read.
example : loadDescriptors (fixture 2) 2048 (MAX_BATCH + 1) = none :=
  loadDescriptors_too_large _ _ _ (Nat.lt_succ_self _)

example : observe .batched singleCall 1 (fixture (MAX_BATCH + 1) false 3) =
    (.failure, 1, 0, 0, 0) := by
  decide +kernel

-- Fuel zero is handled before parsing, including a deliberately oversized count.
example : observe .batched singleCall 0 (fixture (MAX_BATCH + 1) false 3) =
    (.unfinished, 0, 0, 0, 0) := by
  decide +kernel

-- Selector 3 alone does not dispatch a batch: the fetched instruction must be ECALL.
private def ordinary : Image := ⟨[0x00700313], []⟩

example : observe .batched ordinary 1 (fixture (MAX_BATCH + 1) false 3) =
    (.unfinished, 1, 0, 0, 0) := by
  decide +kernel

example :
    ((publicEvaluation (BatchMachine.execute .batched ordinary 1
      (fixture (MAX_BATCH + 1) false 3) false)).1.result.state.getReg .x6) = 7 := by
  decide +kernel

-- Pointer validation uses Nat addition and rejects an array crossing the memory ceiling.
example : loadDescriptors (fixture 2) (BitVec.ofNat 64 (MEMORY_BYTES - 32)) 2 = none := by
  decide +kernel

example : loadDescriptors (fixture 2) 2049 2 = none := by
  decide +kernel

end DepthPrototype.BatchMachineTests
