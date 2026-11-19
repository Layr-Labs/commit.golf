import CommitGolfCandidate.HeadStreamCheckBody

namespace TwoPermutationPrototype.Packed.Checker.HeadRestore
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open ProofCodec.HeadStream
open PackedOpening.Pack (ordinaryInstr toNat_w)
attribute [local simp] Opening.getReg_setReg set_byte_read
set_option maxRecDepth 8192

theorem heads_count (k L B n r : Nat) (Q : Proof) (s0 s : MachineState)
    (inv : Heads k L B Q s0 r s) (count : r+n=k) (len : Q.length+k/4=L)
    (kb : k≤2^24) (capacity : L≤8355061248) (records : 481*k≤L) (room : B+2^34≤2^36)
    (source : ∀ j<2^34,s0.getByte (BitVec.ofNat 64 (B+j))=Q.getD j 0) :
    ∃ t, Heads k L B Q s0 k t ∧ Hop s t (18*n) (24*n) ∧ Reach s t := by
  induction n generalizing r s with
  | zero =>
    have eq : r=k := by omega
    subst r
    exact ⟨s,inv,Hop.refl s,Reach.refl s⟩
  | succ n ih =>
    obtain ⟨t,inv',hop,reach⟩ := head_iter k L B r Q s0 s inv len kb capacity records room (by omega) source
    obtain ⟨u,inv'',hop',reach'⟩ := ih (r+1) t inv' (by omega)
    exact ⟨u,inv'',(hop.thenDo hop').cast (by omega) (by omega),reach.trans reach'⟩

theorem body_count (k L B p : Nat) (Q : Proof) (sH s : MachineState)
    (inv : Body k L B Q sH p s) (capacity : L≤8355061248) (records : 481*k≤L)
    (room : B+2^34≤2^36)
    (source : ∀ j<L-k,sH.getByte (BitVec.ofNat 64 (B+j))=Q.getD j 0) :
    ∃ t, Body k L B Q sH 0 t ∧
      Hop s t (∑ i∈Finset.range p,bodySteps k i) (∑ i∈Finset.range p,bodyCycles k i) ∧ Reach s t := by
  induction p generalizing s with
  | zero => exact ⟨s,inv,by simpa using Hop.refl s,Reach.refl s⟩
  | succ p ih =>
    obtain ⟨t,inv',hop,reach⟩ := body_iter k L B p Q sH s inv capacity records room source
    obtain ⟨u,inv'',hop',reach'⟩ := ih t inv'
    refine ⟨u,inv'',(hop.thenDo hop').cast ?_ ?_,reach.trans reach'⟩ <;>
      rw [Finset.sum_range_succ] <;> omega

def bodyEnter : List Nat := [16,34,35]
@[simp] theorem heads_done_branch : 6352#64+signExtend13 72#13=6424#64 := by decide

theorem heads_to_body (k L B : Nat) (Q : Proof) (s0 s : MachineState)
    (inv : Heads k L B Q s0 k s) (records : 481*k≤L) :
    Body k L B Q s (L-k) (run s bodyEnter) ∧ Hop s (run s bodyEnter) 3 3 ∧ Reach s (run s bodyEnter) := by
  have regs := inv.regs
  have ok : PathOK s bodyEnter := by
    simp [PathOK,bodyEnter,execInstrBr,inv.pc,inv.counter,regs.x16,ordinaryInstr,memoryArgumentsValid,memAccess,pcOf]
  refine ⟨⟨regs.keep bodyEnter (by decide) (by decide),?_,?_,?_,by omega,?_⟩,
    (runs_path s bodyEnter ok).cast rfl (by decide),reach_path s bodyEnter ok⟩
  · simp [run,bodyEnter,execInstrBr,inv.pc,inv.counter,regs.x16,pcOf]
  · simp [run,bodyEnter,execInstrBr,inv.counter,regs.x16,regs.x18]
  · simp [run,bodyEnter,execInstrBr]
  · intro a
    rw [body_initial _ _ _ _ _ _ records]
    simp [run,bodyEnter,execInstrBr,inv.counter,regs.x16]

theorem body_steps_bound (k p : Nat) : (∑ i∈Finset.range p,bodySteps k i)≤12*p := by
  induction p with
  | zero => simp
  | succ p ih =>
    have bound : bodySteps k p≤12 := by unfold bodySteps;split_ifs <;> omega
    rw [Finset.sum_range_succ]
    omega

theorem body_cycles_bound (k p : Nat) : (∑ i∈Finset.range p,bodyCycles k i)≤15*p := by
  induction p with
  | zero => simp
  | succ p ih =>
    have bound : bodyCycles k p≤15 := by unfold bodyCycles;split_ifs <;> omega
    rw [Finset.sum_range_succ]
    omega

end TwoPermutationPrototype.Packed.Checker.HeadRestore
