import CommitGolfCandidate.RungATypes
import CommitGolfCandidate.RungAArithmetic
import CommitGolfCandidate.RungAGroup
import CommitGolfCandidate.TruncMask
set_option Elab.async false
set_option maxHeartbeats 1500000
attribute [local irreducible] CommitGolf.Riscv.readBuffer
namespace CommitGolfCandidate.RungA
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open S4.Machine (W Code Runs Safe)
open Late (pcAt nodeAddress rowAddress levelCount Digest)
theorem written (s : MachineState) (a : Nat) (w : Digest) (room:a+32≤2^36) :
    Stored s (writeBits s (W a) w) a w := by
  refine ⟨?_,?_⟩
  · simpa only [Nat.add_zero,Nat.mul_zero,BitVec.extractLsb'_eq_self] using
      write_bits_digest s a 0 w (by decide) (by decide)
  · intro q b outside
    apply write_bits_byte_outside
    intro j h eq
    have he : W q=W (a+j):=eq.trans (BitVec.ofNat_add ..).symm
    change j<32 at h
    have:=S4.Machine.wordNumber (by omega) (by omega) he;omega

theorem Stored.mem {s u t : MachineState} {a v} (w : Stored s u a v) (m:t.mem=u.mem) : Stored s t a v := by
  refine ⟨(readEqual _ _ (fun j hj=>by simp only [S4.Machine.byte,MachineState.getByte,MachineState.getMem,m])).trans w.data,?_⟩
  intro b lim away;simpa only [S4.Machine.byte,MachineState.getByte,MachineState.getMem,m] using w.outside b lim away

theorem realDigest (H : Compression) (td : Late.Trapdoor) (h j : Nat) (bh:h<4) (real:j<levelCount h) :
    rebuildDigest H td h j=(if masked h then Trunc.padLow (H (inputBlock H td h j)) else H (inputBlock H td h j)) := by
  cases h with
  | zero=>
    exact (show rebuildDigest H td 0 j=H (Late.slice td (finalRowAddress j) 96) from if_pos real)
  | succ h=>
    have e : rebuildDigest H td (h+1) j=S4.retained S4.active (h+1) (H (inputBlock H td (h+1) j)):=if_pos real
    apply e.trans
    generalize H (inputBlock H td (h+1) j)=v
    have bound : h≤2:=by omega
    interval_cases h <;> rfl

end CommitGolfCandidate.RungA
