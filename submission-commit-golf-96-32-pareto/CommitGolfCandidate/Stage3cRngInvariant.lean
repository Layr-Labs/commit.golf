import CommitGolfCandidate.Stage3cRngTile

namespace CommitGolfCandidate.Chained.BinaryMachine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

private theorem increment_address (p : Nat) :
    BitVec.ofNat 64 (destination p) + 184 = BitVec.ofNat 64 (destination (p+1)) := by
  change BitVec.ofNat 64 (pairAddress p) + BitVec.ofNat 64 184 = _
  rw [← BitVec.ofNat_add]
  apply congrArg (BitVec.ofNat 64)
  unfold destination pairAddress
  omega

private theorem after_increment {r : MachineState} {p : Nat} (inside : p < 8388608)
    (pc : r.pc = pcAt (12+2*(p%2048)) + 8)
    (dest : r.getReg .x10 = BitVec.ofNat 64 (destination (p+1)))
    (c : r.getReg .x20 = BitVec.ofNat 64 (4096-p/2048))
    (sel : r.getReg .x5 = 2) (bytes : r.getReg .x11 = 40) :
    AtPair (if p%2048 = 2047 then latchState r p else r) (p+1) := by
  by_cases endTile : p%2048 = 2047
  · rw [if_pos endTile]
    have nextc:=latch_counter p r inside endTile c
    refine ⟨?_,nextc,sel,bytes,dest⟩
    change pcAt (if p+1<pairCount then 12 else 4111)=pcAt (if p+1<pairCount then 12+2*((p+1)%2048) else 4111)
    rw [show (p+1)%2048=0 by omega]
  · have more : p+1 < pairCount := by change p+1 < 8388608; omega
    rw [if_neg endTile]
    constructor
    · rw [pc, if_pos more]
      have z : 4096 + 4*(12+2*(p%2048)) + 8 = 4096 + 4*(12+2*((p+1)%2048)) := by omega
      exact (BitVec.ofNat_add _ _).symm.trans (congrArg (BitVec.ofNat 64) z)
    · simpa only [show (p+1)/2048 = p/2048 by omega] using c
    · exact sel
    · exact bytes
    · exact dest

theorem next_pair_invariant {s : MachineState} {p : Nat} (a : AtPair s p) (inside : p < pairCount)
    (w : Draw40) : AtPair (nextPair p s w) (p+1) := by
  obtain ⟨pc, dst, kept⟩ := random_registers s w
  apply after_increment inside
  · rw [pc, a.pc, if_pos inside]
  · rw [dst, a.dest, increment_address]
  · exact (kept _ (by decide)).trans a.counter
  · exact (kept _ (by decide)).trans a.selector
  · exact (kept _ (by decide)).trans a.bytes

end CommitGolfCandidate.Chained.BinaryMachine
