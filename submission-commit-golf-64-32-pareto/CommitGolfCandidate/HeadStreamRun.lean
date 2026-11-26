import CommitGolfCandidate.StreamCopyRun
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
      Runs s s' (StreamCopy.price 480 k L) (StreamCopy.price 480 k L) := by
  have m (q : Word) : s.getByte q=s0.getByte q := by rw [inv.mem];simp
  have input (j : Nat) (hj:j<L) : s.getByte (StreamCopy.word (base+j))=Q.getD j 0 :=
    (m _).trans (source j hj)
  have inside (r j : Nat) (hr:r<k) (hj:j<480) :
      Q.getD (481*r+StreamCopy.copyOff 480 j) 0=convertedByte k Q (480*r+j) := by
    rw [convertedByte,len,if_pos (by omega),compact_record_source _ _ (by omega)]
    rw [show (480*r+j)/480=r by omega,show (480*r+j)%480=j by omega]
    simp only [StreamCopy.copyOff,Nat.reduceSub,Nat.add_assoc]
  have footer (j : Nat) (hj:j<L-481*k) :
      Q.getD (481*k+j) 0=convertedByte k Q (480*k+j) := by
    rw [convertedByte,len,if_pos (by omega),compact_footer_source _ _ (by omega)]
    apply congrArg (fun i => Q.getD i 0)
    omega
  obtain ⟨z,ran,pc,fr,count,mem⟩:=StreamCopy.compact true k L base Q (convertedByte k Q) s
    records (by omega) inv.pc inv.regs.x16 inv.regs.x18 inv.regs.x20 inv.x22 inv.x26 input
    (fun r hr j hj=>inside r j hr hj) footer
  refine ⟨z,⟨?_,pc,count,(fr _ (by decide)).trans inv.x26,le_rfl,?_⟩,ran⟩
  · constructor <;> rw [fr _ (by decide)]
    all_goals first | exact inv.regs.x5 | exact inv.regs.x10 | exact inv.regs.x11 |
      exact inv.regs.x16 | exact inv.regs.x20 | exact inv.regs.x27 | exact inv.regs.x18 |
      exact inv.regs.x9 | exact inv.regs.x7
  · intro q;rw [mem,m]

end TwoPermutationPrototype.PackedOpening.HeadStream
