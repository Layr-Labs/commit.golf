import CommitGolfCandidate.TailStreamOutput

namespace TwoPermutationPrototype.PackedOpening.TailStream
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open Pack ProofCodec.HeadStreamSeven
attribute [local simp] Opening.getReg_setReg set_byte_read
set_option maxRecDepth 8192

structure Output (k L base H : Nat) (Q : Proof) (s0 : MachineState) (g m : Nat) (s : MachineState) : Prop where
  regs : Regs k L base H s
  pc : s.pc=pcOf (38+8*m)
  x22 : s.getReg .x22=BitVec.ofNat 64 g
  x28 : s.getReg .x28=BitVec.ofNat 64 (H+8*g)
  x26 : s.getReg .x26=BitVec.ofNat 64 (base+(L-k)+7*g)
  mem : ∀ a : Word, s.getByte a=
    if base+(L-k)≤a.toNat ∧ a.toNat<base+(L-k)+(7*g+m)
      then headPackedByte k Q (a.toNat-(base+(L-k))) else s0.getByte a

variable {image : Image} [CodeImage image]

set_option maxHeartbeats 1800000 in
theorem output_iter (k L base H : Nat) (Q : Proof) (s0 s : MachineState) (g m : Nat)
    (inv : Output k L base H Q s0 g m s) (records : 480*k≤L)
    (small : L+7≤2^33) (gap : base+2^33≤H) (room : base+2^34≤2^36)
    (hroom : H+k+8≤base+2^34) (hg : g<(k+7)/8) (hm : m<7)
    (headers : ∀ j<k+7, (s0.getByte (BitVec.ofNat 64 (H+j))).toNat%128=head k Q j) :
    ∃ t, Output k L base H Q s0 g (m+1) t ∧ Runs image s t 8 8 := by
  have bank (j : Nat) (hj : j<k+7) :
      (s.getByte (BitVec.ofNat 64 (H+j))).toNat%128=head k Q j := by
    rw [inv.mem,toNat_w _ (by omega),if_neg (by omega)]
    exact headers j hj
  have value : adjacentByte
      (s.getByte (BitVec.ofNat 64 (H+8*g+m)))
      (s.getByte (BitVec.ofNat 64 (H+8*g+(m+1)))) m=headPackedByte k Q (7*g+m) := by
    unfold adjacentByte
    simp only [Nat.add_assoc]
    rw [bank (8*g+m) (by omega),bank (8*g+(m+1)) (by omega),head_group_byte k Q g m hm,
      show 8*m/7=m by omega,show 8*m%7=m by omega]
    congr 2 <;> omega
  obtain ⟨ran,pc,mem⟩ := emit_one (image := image) s (H+8*g) (base+(L-k)+7*g) m hm
    inv.pc inv.x28 inv.x26 (by omega) (by omega)
  have common : Regs k L base H (run s (emitPath m)) :=
    inv.regs.keep (emitPath m) (by interval_cases m <;> decide)
  have x22 : (run s (emitPath m)).getReg .x22=BitVec.ofNat 64 g :=
    (run_keeps _ (emitPath m) s (by interval_cases m <;> decide)).trans inv.x22
  have x28 : (run s (emitPath m)).getReg .x28=BitVec.ofNat 64 (H+8*g) :=
    (run_keeps _ (emitPath m) s (by interval_cases m <;> decide)).trans inv.x28
  have x26 : (run s (emitPath m)).getReg .x26=BitVec.ofNat 64 (base+(L-k)+7*g) :=
    (run_keeps _ (emitPath m) s (by interval_cases m <;> decide)).trans inv.x26
  refine ⟨_,⟨common,?_,x22,x28,x26,?_⟩,ran⟩
  · simpa only [show 38+8*(m+1)=46+8*m by omega] using pc
  · apply extend_region _ _ (base+(L-k)) (7*g+m) (headPackedByte k Q) s0.getByte
      (headPackedByte k Q (7*g+m)) (by omega) inv.mem
    · intro a
      rw [mem,value,show base+(L-k)+7*g+m=base+(L-k)+(7*g+m) by omega]
    · rfl

theorem output_loop (k L base H : Nat) (Q : Proof) (s0 s : MachineState) (g : Nat)
    (inv : Output k L base H Q s0 g 0 s) (records : 480*k≤L)
    (small : L+7≤2^33) (gap : base+2^33≤H) (room : base+2^34≤2^36)
    (hroom : H+k+8≤base+2^34) (hg : g<(k+7)/8)
    (headers : ∀ j<k+7, (s0.getByte (BitVec.ofNat 64 (H+j))).toNat%128=head k Q j) :
    ∃ t, Output k L base H Q s0 g 7 t ∧ Runs image s t 56 56 := by
  obtain ⟨t,inv',ran⟩ := runs_loop (image := image) (fun m s => Output k L base H Q s0 g m s) 7
    (fun _ => 8) (fun _ => 8)
    (fun m hm s inv => output_iter k L base H Q s0 s g m inv records small gap room hroom hg hm headers)
    7 0 s rfl inv
  exact ⟨t,inv',ran.cast (by decide) (by decide)⟩

end TwoPermutationPrototype.PackedOpening.TailStream
