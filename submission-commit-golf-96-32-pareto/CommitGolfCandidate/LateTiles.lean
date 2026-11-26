import CommitGolfCandidate.LateRandom
import CommitGolfCandidate.LateMemory

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def pairCount := 8388608
abbrev destination := pairAddress

structure AtPair (s : MachineState) (p : Nat) : Prop where
  pc : s.pc = pcAt (if p < pairCount then 16+2*(p%256) else 530)
  counter : s.getReg .x20 = BitVec.ofNat 64 (32768-p/256)
  selector : s.getReg .x5 = 2
  bytes : s.getReg .x11 = 48
  dest : s.getReg .x10 = BitVec.ofNat 64 (destination p)

def decrement (s : MachineState) := execInstrBr s (.ADDI .x20 .x20 4095)
def branchBack (s : MachineState) := execInstrBr s (.BNE .x20 .x0 6140)
def nextPair (p : Nat) (s : MachineState) (w : PairCoins) :=
  let r := randomStep s w
  if p%256 = 255 then branchBack (decrement r) else r

def pairSteps (p : Nat) := if p%256 = 255 then 4 else 2
def pairCycles (p : Nat) := if p%256 = 255 then 10 else 8

theorem random_registers (s : MachineState) (w : PairCoins) :
    (randomStep s w).pc = s.pc + 8 ∧
    (randomStep s w).getReg .x10 = s.getReg .x10 + 192 ∧
    ∀ r, r ≠ .x10 → (randomStep s w).getReg r = s.getReg r := by
  constructor
  · change (s.pc+4)+4 = s.pc+8
    rw [BitVec.add_assoc]
    rfl
  constructor
  · simp only [randomStep, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0),
      writeBits_register]
    rfl
  · intro r hr
    simp only [randomStep, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ hr.symm, writeBits_register]

private theorem tail_word (i : Nat) (hi : i < 2) :
    commitImage.code[528+i]? = tail528[i]? := by
  change (setupWords ++ (randomWords ++ (tail528 ++ _)))[528+i]? = _
  have hs : setupWords.length = 16 := rfl
  have hr : randomWords.length = 512 := by simp [randomWords]
  rw [List.getElem?_append_right (by rw [hs]; omega), hs,
    List.getElem?_append_right (by rw [hr]; omega), hr,
    show 528+i-16-512 = i by omega, List.getElem?_append_left (by change i < 128; omega)]

attribute [local irreducible] commitImage randomStep

private theorem execute_end_tile (s : MachineState) (pc : s.pc = pcAt 528) (fuel : Nat) :
    execute commitImage (fuel+2) s true =
      (do let result ← execute commitImage fuel (branchBack (decrement s)) true
          return result.charge 2 0) := by
  have f : fetch commitImage s = some (.base (.ADDI .x20 .x20 4095)) := by
    exact (fetch_word pc (by decide) ((tail_word 0 (by decide)).trans (by rfl))).trans (by rfl)
  have f' : fetch commitImage (decrement s) = some (.base (.BNE .x20 .x0 6140)) := by
    have ip : (decrement s).pc = pcAt 529 := by change s.pc+4 = _; rw [pc]; rfl
    exact (fetch_word ip (by decide) ((tail_word 1 (by decide)).trans (by rfl))).trans (by rfl)
  rw [execute_ordinary_step _ _ _ (decrement s) _ _ f rfl,
    execute_ordinary_step _ _ _ (branchBack (decrement s)) _ _ f' rfl]
  simp [bind_assoc, Execution.charge, instructionCycles, ← Nat.add_assoc]

theorem execute_one_pair {s : MachineState} {p : Nat} (a : AtPair s p) (inside : p < pairCount)
    (fuel : Nat) :
    execute commitImage (fuel+pairSteps p) s true =
      (do let w ← drawPair
          let r ← execute commitImage fuel (nextPair p s w) true
          return r.charge (pairCycles p) 0) := by
  have ip := a.pc
  rw [if_pos inside] at ip
  have valid : randomArgumentsValid s = true := by
    obtain ⟨align, ceiling⟩ := pair_address_valid p inside
    have h : pairAddress p < 2^64 := by change pairAddress p + 48 ≤ 2^36 at ceiling; omega
    simp only [randomArgumentsValid, rangeValid, a.bytes, a.dest, destination, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt h, align, decide_true, Bool.true_and]
    exact decide_eq_true ceiling
  by_cases endOfTile : p%256 = 255
  · unfold pairSteps pairCycles nextPair
    simp only [if_pos endOfTile]
    rw [show fuel+4 = (fuel+2)+2 by omega, execute_pair s _ (fuel+2) (Nat.mod_lt _ (by decide))
      ip a.selector a.bytes valid]
    apply bind_congr
    intro w
    have tailpc : (randomStep s w).pc = pcAt 528 := by
      rw [(random_registers s w).1, ip, endOfTile]; rfl
    rw [execute_end_tile _ tailpc]
    simp [bind_assoc, Execution.charge, ← Nat.add_assoc]
  · simpa only [pairSteps, pairCycles, nextPair, if_neg endOfTile] using
      execute_pair s _ fuel (Nat.mod_lt _ (by decide)) ip a.selector a.bytes valid

end CommitGolfCandidate.Late
