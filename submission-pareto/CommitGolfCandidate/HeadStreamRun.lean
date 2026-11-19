import CommitGolfCandidate.HeadStreamHeads

namespace TwoPermutationPrototype.PackedOpening.HeadStream
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open Pack
open CommitGolfCandidate.ProofCodec.HeadStreamFive
attribute [local simp] Opening.getReg_setReg set_byte_read
set_option maxRecDepth 8192

@[simp] theorem se12_5 : signExtend12 5#12=5#64 := by decide

set_option maxHeartbeats 1000000 in
theorem head_enter (k L base H : Nat) (Q : Proof) (s0 s : MachineState) (g : Nat)
    (inv : Heads k L base H Q s0 g s) (records : 481*k≤L) (small : L+7≤2^33)
    (gap : base+2^33≤H) (room : base+2^34≤2^36) (hroom : H+8*groups k+1≤base+2^34)
    (hg : g<groups k)
    (headers : ∀ r<8*groups k, (s0.getByte (BitVec.ofNat 64 (H+r))).toNat%32=head k Q r) :
    Partial k L base H Q s0 g 0 (run s headEnter) ∧ Runs s (run s headEnter) 5 5 := by
  have regs := inv.regs
  have gdef : groups k=(k+7)/8 := rfl
  have ne : BitVec.ofNat 64 g≠BitVec.ofNat 64 ((k+7)/8) := by
    rw [Ne,w_inj _ _ (by omega) (by omega)]
    omega
  have ok : PathOK s headEnter := by
    simp (disch := omega) [PathOK,headEnter,execInstrBr,inv.pc,inv.x22,regs.x7,ne,regs.x27,
      ordinaryInstr,memoryArgumentsValid,memAccess,w_shl,w_add]
    apply accessValid_of
    rw [toNat_w _ (by omega)]
    omega
  refine ⟨⟨regs.keep headEnter (by decide),?_,?_,?_,?_,?_⟩,(runs_path _ s ok).cast rfl (by decide)⟩
  · simp [run,headEnter,execInstrBr,inv.pc,inv.x22,regs.x7,ne]
  · exact (run_keeps _ headEnter s (by decide)).trans inv.x22
  · exact (run_keeps _ headEnter s (by decide)).trans inv.x26
  · simp [run,headEnter,execInstrBr,inv.x22,regs.x7,ne,regs.x27,w_shl,w_add,show g*8=8*g by omega]
  · intro a
    simpa only [Nat.add_zero] using (getByte_of_mem (run_mem headEnter s (by decide)) a).trans (inv.mem a)

set_option maxHeartbeats 1000000 in
theorem head_tail (k L base H : Nat) (Q : Proof) (s0 s : MachineState) (g : Nat)
    (inv : Partial k L base H Q s0 g 5 s) (hg : g<groups k)
    (records : 481*k≤L) (small : L+7≤2^33) :
    Heads k L base H Q s0 (g+1) (run s headTail) ∧ Runs s (run s headTail) 3 3 := by
  have gdef : groups k=(k+7)/8 := rfl
  have pc : s.pc=pcOf 234 := inv.pc
  have ok : PathOK s headTail := by
    simp [PathOK,headTail,execInstrBr,pc,ordinaryInstr,memoryArgumentsValid,memAccess]
  refine ⟨⟨inv.regs.keep headTail (by decide),?_,?_,?_,by omega,?_⟩,
    (runs_path _ s ok).cast rfl (by decide)⟩
  · simp [run,headTail,execInstrBr,pc]
  · simp [run,headTail,execInstrBr,inv.x22,w_add]
  · simp [run,headTail,execInstrBr,inv.x26,w_add]
    congr 1 <;> omega
  · intro a
    have e : base+(L-k)+5*(g+1)=base+(L-k)+5*g+5 := by omega
    rw [e]
    exact (getByte_of_mem (run_mem headTail s (by decide)) a).trans (inv.mem a)

theorem head_group (k L base H : Nat) (Q : Proof) (s0 s : MachineState) (g : Nat)
    (inv : Heads k L base H Q s0 g s) (len : Q.length=L) (records : 481*k≤L)
    (small : L+7≤2^33) (gap : base+2^33≤H) (room : base+2^34≤2^36)
    (hroom : H+8*groups k+1≤base+2^34) (hg : g<groups k)
    (headers : ∀ r<8*groups k, (s0.getByte (BitVec.ofNat 64 (H+r))).toNat%32=head k Q r) :
    ∃ s', Heads k L base H Q s0 (g+1) s' ∧ Runs s s' 68 68 := by
  obtain ⟨i0,r0⟩ := head_enter k L base H Q s0 s g inv records small gap room hroom hg headers
  obtain ⟨s1,i1,r1⟩ := partial_iter k L base H Q s0 _ g 0 i0 len records small gap room hroom hg (by decide) headers
  obtain ⟨s2,i2,r2⟩ := partial_iter k L base H Q s0 _ g 1 i1 len records small gap room hroom hg (by decide) headers
  obtain ⟨s3,i3,r3⟩ := partial_iter k L base H Q s0 _ g 2 i2 len records small gap room hroom hg (by decide) headers
  obtain ⟨s4,i4,r4⟩ := partial_iter k L base H Q s0 _ g 3 i3 len records small gap room hroom hg (by decide) headers
  obtain ⟨s5,i5,r5⟩ := partial_iter k L base H Q s0 _ g 4 i4 len records small gap room hroom hg (by decide) headers
  obtain ⟨i8,r8⟩ := head_tail k L base H Q s0 s5 g i5 hg records small
  exact ⟨_,i8,((((((r0.trans r1).trans r2).trans r3).trans r4).trans r5).trans r8)⟩

theorem head_loop (k L base H : Nat) (Q : Proof) (s0 s : MachineState)
    (inv : Heads k L base H Q s0 0 s) (len : Q.length=L) (records : 481*k≤L)
    (small : L+7≤2^33) (gap : base+2^33≤H) (room : base+2^34≤2^36)
    (hroom : H+8*groups k+1≤base+2^34)
    (headers : ∀ r<8*groups k, (s0.getByte (BitVec.ofNat 64 (H+r))).toNat%32=head k Q r) :
    ∃ s', Heads k L base H Q s0 (groups k) s' ∧ Runs s s' (68*groups k) (68*groups k) := by
  obtain ⟨s',inv',runs⟩ := runs_loop (fun g s => Heads k L base H Q s0 g s) (groups k)
    (fun _ => 68) (fun _ => 68)
    (fun g hg s inv => head_group k L base H Q s0 s g inv len records small gap room hroom hg headers)
    (groups k) 0 s (by omega) inv
  refine ⟨s',inv',runs.cast ?_ ?_⟩ <;> simp [Nat.mul_comm]

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
