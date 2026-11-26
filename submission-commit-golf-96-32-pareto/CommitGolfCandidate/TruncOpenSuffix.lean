import CommitGolfCandidate.PairSuffix

import CommitGolfCandidate.TruncOpenBlocks

import CommitGolfCandidate.TruncCheckFetch

namespace CommitGolfCandidate.Trunc.Open

open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate.PairCap

set_option maxRecDepth 18000

set_option maxHeartbeats 1600000

theorem bucket_bound (s : MachineState) : (leafBucket s).toNat < 256 := by
  unfold leafBucket
  rw [BitVec.toNat_and]
  exact Nat.lt_succ_of_le Nat.and_le_right

theorem validSources : ∀ i : Fin 256, ∀ j : Fin 4,
    let u := BitVec.ofNat 64 i.val
    accessValid (srcOf u + BitVec.ofNat 64 (8*j.val)) 8 = true := by decide

theorem validDestinations : ∀ i : Fin 256, ∀ j : Fin 4,
    let u := BitVec.ofNat 64 i.val
    accessValid (dstOf u + BitVec.ofNat 64 (8*j.val)) 8 = true := by decide

theorem source_valid (s : MachineState) {n : Nat} (f : Frame s n) (j : Fin 4) :
    accessValid ((headState s).getReg .x23 + BitVec.ofNat 64 (8*j.val)) 8 = true := by
  rw [head_source,srcAddr,f.children]
  change accessValid (srcOf (leafBucket s) + BitVec.ofNat 64 (8*j.val)) 8 = true
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using validSources ⟨_,bucket_bound s⟩ j

theorem destination_valid (s : MachineState) {n : Nat} (f : Frame s n) (j : Fin 4) :
    accessValid ((headState s).getReg .x25 + BitVec.ofNat 64 (8*j.val)) 8 = true := by
  rw [head_destination,dstAddr,f.slots]
  change accessValid (dstOf (leafBucket s) + BitVec.ofNat 64 (8*j.val)) 8 = true
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using validDestinations ⟨_,bucket_bound s⟩ j

theorem latchRun (s : MachineState) (pc : s.pc = 4632) (fuel : Nat) (coins : Bool) :
    execute (Trunc.submission.image .opening) (2 + fuel) s coins =
    (do let next ← execute (Trunc.submission.image .opening) fuel (latchState s) coins
        return next.charge 2 0) := by
  let mid := (s.setReg .x28 (s.getReg .x28 - 1)).setPC 4636
  have f0 : fetch (Trunc.submission.image .opening) s = some (.base (.ADDI .x28 .x28 4095)) := by
    apply openingFetch _ 134 _ (by decide) pc; rfl
  have f1 : fetch (Trunc.submission.image .opening) mid = some (.base (.BNE .x28 .x0 8112)) := by
    apply openingFetch _ 135 _ (by decide) rfl; rfl
  have s0 : ordinaryStep s (.base (.ADDI .x28 .x28 4095)) = some mid := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, mid, pc, BitVec.sub_eq_add_neg]
  have s1 : ordinaryStep mid (.base (.BNE .x28 .x0 8112)) = some (latchState s) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13, mid, latchState,
      MachineState.getReg, MachineState.setPC, MachineState.setReg]
    split <;> simp_all
  rw [show 2+fuel = (1+fuel)+1 by omega, execute_ordinary_step _ _ _ _ _ _ f0 s0,
      Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ f1 s1]
  simp [instructionCycles, Execution.charge, ← Nat.add_assoc]

theorem index_addr (n : Nat) :
    BitVec.ofNat 64 (6442455072+8*(n+1)) + signExtend12 4088 = BitVec.ofNat 64 (6442455072+8*n) := by
  rw [show 6442455072+8*(n+1) = (6442455072+8*n)+8 by omega, BitVec.ofNat_add]
  rw [BitVec.add_assoc, show BitVec.ofNat 64 8 + signExtend12 4088 = 0 by decide]
  exact BitVec.add_zero (BitVec.ofNat 64 (6442455072+8*n))

theorem oneOverride (s : MachineState) {n : Nat} (bound : n < 128) (f : Frame s (n+1))
    (pc : s.pc = 4556) (fuel : Nat) (coins : Bool) :
    execute (Trunc.submission.image .opening) (21 + fuel) s coins =
    (do let next ← execute (Trunc.submission.image .opening) fuel (overrideState s) coins
        return next.charge 21 0) := by
  have idxOk : accessValid (s.getReg .x24 + signExtend12 4088) 8 = true := by
    change accessValid (s.getReg .x24 + signExtend12 4088) 8 = true
    rw [f.cursor, index_addr]
    simp only [accessValid, rangeValid, Bool.and_eq_true, decide_eq_true_eq, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 6442455072 + 8*n < 2^64), MEMORY_BYTES]
    omega
  have pHead : (headState s).pc = 4600 := by
    simp [headState, blockPrefix, headOps, execInstrBr, pc, MachineState.setPC]
  have pCopy : (openingCopyState (headState s)).pc = 4632 := by
    rw [opening_copy_pc, pHead]; rfl
  rw [show 21+fuel = 11+(8+(2+fuel)) by omega, headRun s pc idxOk,
      copyRun _ pHead (source_valid s f) (destination_valid s f), latchRun _ pCopy]
  simp [overrideState, Execution.charge, ← Nat.add_assoc]

theorem decremented (n : Nat) :
    BitVec.ofNat 64 (n+1) - 1 = BitVec.ofNat 64 n := by rw [BitVec.ofNat_add]; exact BitVec.add_sub_cancel _ 1

theorem inheritedReg (s : MachineState) (r : Reg) (hr : r ≠ .x6) :
    (openingCopyState (headState s)).getReg r = (headState s).getReg r :=
  opening_copy_register _ _ hr

theorem onePC (s : MachineState) {n : Nat} (bound : n < 128) (f : Frame s (n+1)) :
    (overrideState s).pc = if n = 0 then 4640 else 4556 := by
  change (if (openingCopyState (headState s)).getReg .x28 - 1 = 0 then _ else _) = _
  rw [inheritedReg _ _ (by decide)]
  change (if s.getReg .x28 - 1 = 0 then _ else _) = _
  rw [f.left, decremented]
  have nz : (BitVec.ofNat 64 n = 0) ↔ n = 0 := by
    constructor
    · intro h; have hh := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hh; exact hh
    · rintro rfl; rfl
  simp only [nz]

theorem overrides (n : Nat) (bound : n ≤ 128) (s : MachineState) (f : Frame s n)
    (pc : s.pc = if n=0 then 4640 else 4556) (fuel : Nat) (coins : Bool) :
    execute (Trunc.submission.image .opening) (21*n + fuel) s coins =
    (do let next ← execute (Trunc.submission.image .opening) fuel (overrideState^[n] s) coins
        return next.charge (21*n) 0) := by
  induction n generalizing s with
  | zero => simp [Execution.charge]
  | succ n ih =>
    have pos : s.pc = 4556 := by simpa using pc
    rw [show 21*(n+1)+fuel = 21+(21*n+fuel) by omega, oneOverride s (by omega) f pos,
      ih (by omega) _ (oneFrame s f) (onePC s (by omega) f)]
    simp [Function.iterate_succ_apply, Execution.charge, Nat.mul_add, ← Nat.add_assoc, Nat.add_comm 21 (21*n)]

theorem overridesPC (n : Nat) (bound : n ≤ 128) (s : MachineState) (f : Frame s n)
    (pc : s.pc = if n=0 then 4640 else 4556) : (overrideState^[n] s).pc = 4640 := by
  induction n generalizing s with
  | zero => simpa using pc
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    exact ih (by omega) _ (oneFrame s f) (onePC s (by omega) f)

theorem suffixRun (law : Wire.PackRun) (s : MachineState) (pc : s.pc = 4424) (fuel : Nat) (coins : Bool) :
    execute (Trunc.submission.image .opening) (71855+fuel) s coins =
      pure ⟨.success, Wire.packedEnd (suffixState s), 71855, 0⟩ := by
  have jf : fetch (Trunc.submission.image .opening) s = some (.base (.JAL .x0 60)) := by
    apply openingFetch _ 82 _ (by decide) pc; rfl
  have js : ordinaryStep s (.base (.JAL .x0 60)) = some (jumpState s) := by rfl
  have jpc : (jumpState s).pc = 4484 := by simp [jumpState, execInstrBr, pc, MachineState.setPC, signExtend21]
  let base := setupState (jumpState s)
  have f : Frame base 128 := setupFrame _
  have bpc : base.pc = 4556 := by
    simp [base, setupState, blockPrefix, setupOps, execInstrBr, MachineState.setPC, jpc]
  let endState := overrideState^[128] base
  have endPC : endState.pc = 4640 := overridesPC 128 (by decide) base f bpc
  have finalPC : (finishState endState).pc = 4660 := by
    simp [finishState, blockPrefix, finishOps, execInstrBr, MachineState.setPC, endPC]
  rw [show 71855+fuel = (18+(21*128+(5+(69143+fuel))))+1 by omega,
    execute_ordinary_step _ _ _ _ _ _ jf js, setupRun _ jpc, overrides 128 (by decide) base f bpc,
    finishRun endState endPC]
  rw [law (finishState endState) fuel coins finalPC]
  rfl

end CommitGolfCandidate.Trunc.Open
