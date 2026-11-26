import CommitGolfCandidate.LateTiles

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

private theorem increment_address (p : Nat) :
    BitVec.ofNat 64 (destination p) + 192 = BitVec.ofNat 64 (destination (p+1)) := by
  change BitVec.ofNat 64 (pairAddress p) + BitVec.ofNat 64 192 = _
  rw [← BitVec.ofNat_add]
  apply congrArg (BitVec.ofNat 64)
  unfold destination pairAddress
  omega

private theorem after_increment {r : MachineState} {p : Nat} (inside : p < 8388608)
    (pc : r.pc = pcAt (16+2*(p%256)) + 8)
    (dest : r.getReg .x10 = BitVec.ofNat 64 (destination (p+1)))
    (c : r.getReg .x20 = BitVec.ofNat 64 (32768-p/256))
    (sel : r.getReg .x5 = 2) (bytes : r.getReg .x11 = 48) :
    AtPair (if p%256 = 255 then branchBack (decrement r) else r) (p+1) := by
  by_cases endTile : p%256 = 255
  · have rp : r.pc = pcAt 528 := by rw [pc, endTile]; rfl
    have newc : (decrement r).getReg .x20 = BitVec.ofNat 64 (32768-(p+1)/256) := by
      change r.getReg .x20 + (-1) = _
      rw [c, ← BitVec.sub_eq_add_neg]
      exact (BitVec.ofNat_sub_ofNat_of_le (w := 64) (32768-p/256) 1 (by decide)
        (by omega)).trans (congrArg (BitVec.ofNat 64) (by omega))
    have dp : (decrement r).pc = pcAt 529 := by change r.pc+4 = _; rw [rp]; rfl
    have branch : branchBack (decrement r) = (decrement r).setPC
        (pcAt (if p+1 < pairCount then 16 else 530)) := by
      change (if (decrement r).getReg .x20 != (0 : Word) then
        (decrement r).setPC ((decrement r).pc + signExtend13 6140)
        else (decrement r).setPC ((decrement r).pc+4)) = _
      rw [newc, dp]
      change (if (BitVec.ofNat 64 (32768-(p+1)/256) != (0 : Word)) then _ else _) = _
      by_cases more : p+1 < pairCount
      · change p+1 < 8388608 at more
        have ne : BitVec.ofNat 64 (32768-(p+1)/256) ≠ 0 := by
          intro e
          have eq := congrArg BitVec.toNat e
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at eq
          change 32768-(p+1)/256 = 0 at eq
          omega
        simp only [show p+1 < pairCount from more, if_true, bne_iff_ne.mpr ne]
        rfl
      · have zero : 32768-(p+1)/256 = 0 := by change ¬p+1 < 8388608 at more; omega
        rw [zero, if_neg more]
        rfl
    rw [if_pos endTile]
    change AtPair (branchBack (decrement r)) _
    rw [branch]
    constructor
    · have z : (p+1)%256 = 0 := by omega
      simp [MachineState.setPC, z]
    · simpa only [MachineState.getReg_setPC] using newc
    · exact sel
    · exact bytes
    · exact dest
  · have more : p+1 < pairCount := by change p+1 < 8388608; omega
    rw [if_neg endTile]
    constructor
    · rw [pc, if_pos more]
      have z : 4096 + 4*(16+2*(p%256)) + 8 = 4096 + 4*(16+2*((p+1)%256)) := by omega
      exact (BitVec.ofNat_add _ _).symm.trans (congrArg (BitVec.ofNat 64) z)
    · simpa only [show (p+1)/256 = p/256 by omega] using c
    · exact sel
    · exact bytes
    · exact dest

theorem next_pair_invariant {s : MachineState} {p : Nat} (a : AtPair s p) (inside : p < pairCount)
    (w : PairCoins) : AtPair (nextPair p s w) (p+1) := by
  obtain ⟨pc, dst, kept⟩ := random_registers s w
  apply after_increment inside
  · rw [pc, a.pc, if_pos inside]
  · rw [dst, a.dest, increment_address]
  · exact (kept _ (by decide)).trans a.counter
  · exact (kept _ (by decide)).trans a.selector
  · exact (kept _ (by decide)).trans a.bytes

end CommitGolfCandidate.Late
