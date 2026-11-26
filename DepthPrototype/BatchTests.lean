import DepthPrototype.Batch

/-! Bounded kernel regressions for batch snapshots and resource accounting.
These are not secure submissions or a whole-program verification claim. -/

namespace DepthPrototype.BatchTests

open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 DepthPrototype.Batch

set_option exponentiation.threshold 2048
set_option maxRecDepth 10000

private def compression (source destination : Nat) : Descriptor :=
  ⟨0, BitVec.ofNat 64 source, 64, BitVec.ofNat 64 destination⟩

private def request (destination : Nat) : Request :=
  ⟨.inl 0, BitVec.ofNat 64 destination⟩

private def zeroOracle : Oracle := ⟨fun _ => 0, Equiv.refl _⟩

private def incrementOracle : Oracle :=
  ⟨fun input => BitVec.ofNat COMPRESSION_OUTPUT_LENGTH (input.toNat + 1), Equiv.refl _⟩

private def fixedBatch (oracle : Oracle) (state : MachineState)
    (descriptors : List Descriptor) : Option MachineState := do
  let requests ← snapshotAll state descriptors
  return (evaluateFrozen oracle state requests).setPC (state.pc + 4)

private def sequential (oracle : Oracle) (state : MachineState)
    (descriptors : List Descriptor) : Option MachineState :=
  match descriptors with
  | [] => some state
  | descriptor :: descriptors => do
      let next ← fixedBatch oracle state [descriptor]
      sequential oracle next descriptors

private def byteAt (result : Option MachineState) (address : Nat) : Option (BitVec 8) :=
  result.map fun state => state.getByte (BitVec.ofNat 64 address)

-- Empty batches consume no query and no round, while advancing the machine PC once.
example : zeroOracle.eval (runBatch initialMachine []) =
    (some (initialMachine.setPC (initialMachine.pc + 4)), 0) := by
  exact runBatch_refines zeroOracle initialMachine [] [] rfl

example : rounds [] = 0 := rfl

-- Repeated inputs still make two actual calls, even when both answers are identical.
example (oracle : Oracle) :
    (oracle.eval (runFrozen initialMachine [request 1024, request 1056])).2 = 2 := by
  rw [runFrozen_query_count]
  rfl

example : (quote [request 1024, request 1056]).primitiveCycles = 16 := rfl
example : (quote [request 1024, request 1056]).descriptorWords = 8 := rfl
example : (quote [request 1024, request 1056]).oracleRounds = 1 := rfl
example : rounds [request 1024] + rounds [request 1056] = 2 := rfl

-- Illustrative explicit fees only: 16 primitive + 1 entry + 8 reads + 2 bookkeeping.
example : (quote [request 1024, request 1056]).priced ⟨1, 1, 1⟩ = 27 := rfl

-- The second request sees the ORIGINAL bytes at 64, not the first query's reply there.
-- This is deliberately different from two dynamically resnapshotted legacy calls.
example : byteAt (fixedBatch incrementOracle initialMachine
    [compression 0 64, compression 64 128]) 128 = some 1 := by
  decide +kernel

example : byteAt (sequential incrementOracle initialMachine
    [compression 0 64, compression 64 128]) 128 = some 2 := by
  decide +kernel

-- Output overlap is defined by ordered writeback, rather than an implicit race.
example : byteAt (fixedBatch incrementOracle (initialMachine.setByte 256 4)
    [compression 0 64, compression 256 64]) 64 = some 5 := by
  decide +kernel

-- Forward and inverse requests refer to the one shared permutation; no new instance.
example (oracle : Oracle) (input : BitVec PERMUTATION_WIDTH) :
    oracle.answer (m := Id) (.inr (.inr (oracle.permutation input))) = input :=
  forward_inverse_consistent oracle input

example : (quote [⟨.inr (.inl 0), 1024⟩, ⟨.inr (.inr 0), 1224⟩]).publicCalls = 2 := rfl
example : (quote [⟨.inr (.inl 0), 1024⟩, ⟨.inr (.inr 0), 1224⟩]).oracleRounds = 1 := rfl

example : snapshotAll initialMachine [⟨1, 0, 200, 1024⟩, ⟨2, 0, 200, 1224⟩] =
    some [⟨.inr (.inl 0), 1024⟩, ⟨.inr (.inr 0), 1224⟩] := by
  decide +kernel

example : (zeroOracle.eval (runBatch initialMachine
    [⟨1, 0, 200, 1024⟩, ⟨2, 0, 200, 1224⟩])).2 = 2 := by
  rw [runBatch_refines zeroOracle initialMachine _
    [⟨.inr (.inl 0), 1024⟩, ⟨.inr (.inr 0), 1224⟩] (by decide +kernel)]
  rfl


-- Invalid descriptors reject before ANY oracle query; a valid prefix does not leak calls.
private def malformed : Descriptor := ⟨0, 0, 63, 1024⟩
example : snapshotAll initialMachine [compression 0 64, malformed] = none := by
  decide +kernel

example : zeroOracle.eval (runBatch initialMachine [compression 0 64, malformed]) =
    (none, 0) :=
  runBatch_invalid zeroOracle initialMachine _ (by decide +kernel)

example : snapshot initialMachine ⟨3, 0, 64, 1024⟩ = none := by decide +kernel
example : snapshot initialMachine ⟨0, 1, 64, 1024⟩ = none := by decide +kernel
example : snapshot initialMachine ⟨0, 0, 64, 1025⟩ = none := by decide +kernel
example : snapshot initialMachine ⟨0, BitVec.ofNat 64 (MEMORY_BYTES - 32), 64, 0⟩ = none := by
  decide +kernel

end DepthPrototype.BatchTests
