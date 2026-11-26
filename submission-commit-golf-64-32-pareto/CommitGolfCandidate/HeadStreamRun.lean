import CommitGolfCandidate.HeadStreamHeads

namespace TwoPermutationPrototype.PackedOpening.HeadStream
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open Pack
open CommitGolfCandidate.ProofCodec.HeadStreamThree

theorem head_loop (k L base H : Nat) (Q : Proof) (s0 s : MachineState)
    (inv : Heads k L base H Q s0 0 s) (len : Q.length=L) (records : 481*k≤L)
    (small : L+7≤2^33) (gap : base+2^33≤H) (room : base+2^34≤2^36)
    (hroom : H+k+8≤base+2^34)
    (headers : ∀ r<k, (s0.getByte (BitVec.ofNat 64 (H+r))).toNat%8=head k Q r) :
    ∃ t, Heads k L base H Q s0 k t ∧ Runs s t (12*k) (12*k) := by
  obtain ⟨t,inv',ran⟩ := runs_loop (fun r s => Heads k L base H Q s0 r s) k
    (fun _ => 12) (fun _ => 12)
    (fun r hr s inv => head_iter k L base H Q s0 s r inv len records small gap room hroom hr headers)
    k 0 s (by omega) inv
  refine ⟨t,inv',ran.cast ?_ ?_⟩ <;> simp [Nat.mul_comm]

theorem compact_loop (k L base H : Nat) (Q : Proof) (s0 s : MachineState)
    (inv : Compact k L base H Q s0 0 s) (len : Q.length=L) (records : 481*k≤L)
    (small : L+7≤2^33) (room : base+2^34≤2^36)
    (source : ∀ j<L, s0.getByte (BitVec.ofNat 64 (base+j))=Q.getD j 0) :
    ∃ s', Compact k L base H Q s0 (L-k) s' ∧
      Runs s s' (12*(L-k)-(480*k-435)) (15*(L-k)-(480*k-435)) := by
  obtain ⟨s',inv',runs⟩ := runs_loop (fun p s => Compact k L base H Q s0 p s) (L-k)
    (copySteps k) (copyCycles k)
    (fun p hp s inv => compact_iter k L base H Q s0 s p inv len records small room hp source)
    (L-k) 0 s (by omega) inv
  refine ⟨s',inv',runs.cast ?_ ?_⟩
  · rw [← Finset.range_eq_Ico,copy_steps_sum,Nat.min_eq_right (by omega)]
  · rw [← Finset.range_eq_Ico,copy_cycles_sum,Nat.min_eq_right (by omega)]

end TwoPermutationPrototype.PackedOpening.HeadStream
