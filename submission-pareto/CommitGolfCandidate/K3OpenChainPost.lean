import CommitGolfCandidate.K3OpenChainLink
import CommitGolfCandidate.Counting

/-! Opener chain block (rows 777..795 and the link block 896..929), fixed oracle and memory views: `chain_fixed`. Owner: H (draft by S9-L2). -/
namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open CommitGolfCandidate.Permutation.CounterSalt (coord)
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000
set_option pp.deepTerms false

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC pc_of_set mem_of_set
  mem_of_reg
attribute [local simp] chain_zero_reg

/-! ### Fixed oracle -/

/-- A forward permutation query is answered by the fixed permutation. -/
theorem answer_forward (o : Oracle) (q : BitVec PERMUTATION_WIDTH) :
    o.answer (m:=Id) (.inr (.inl q))=o.permutation q := rfl

theorem link_fixed (o : Oracle) : ∀ (c : Nat) (s : MachineState),
    o.run (linkTrace c s)=pure (linkState o c s,c)
  | 0,s => by rw [linkTrace,linkState_zero,oracle_run_pure]
  | c+1,s => by
    rw [linkTrace,oracle_run_public_bind]
    simp only [answer_forward]
    rw [link_fixed o c,linkState_succ]
    simp only [pure_bind,linkStep,Nat.add_comm 1 c]
    rfl

theorem chain_fixed (o : Oracle) (k : BitVec 192) (h : MachineState) (i : Index) (ph : Nat) (e : ChainEntry h i ph)
    (key : KeyWords h k) :
    o.run (chainTrace h i ph)=pure (chainState o h i ph,chainCalls i) := by
  rw [chainTrace,oracle_run_public_bind]
  simp only [answer_forward]
  unfold chainState chainCalls
  simp only [oracle_run_bind,link_fixed,oracle_run_pure,pure_bind,Nat.add_zero]
  rw [Nat.add_comm]
  rfl

/-! ### Memory views -/

theorem chain_view_of_mem {s t : MachineState} (h : t.mem=s.mem) : memoryView t=memoryView s := by
  funext w
  show t.mem _=s.mem _
  rw [h]

/-- Outside the reply window, writing an oracle reply at word 192 leaves the view unchanged. -/
theorem reply_outside (s : MachineState) (z : BitVec PERMUTATION_WIDTH) (w : Nat) (hw : w<2^33)
    (out : w<192 ∨ 217≤w) : memoryView (writeBits s (wordAddress 192) z) w=memoryView s w := by
  refine (permutation_write_memory s 192 w z (by decide) hw).trans ?_
  unfold writeWindow
  rw [dite_eq_right (by omega)]

theorem reply_inside (s : MachineState) (z : BitVec PERMUTATION_WIDTH) (m : Fin 25) :
    memoryView (writeBits s (wordAddress 192) z) (192+m.val)=replyWords z m := by
  refine (permutation_write_memory s 192 (192+m.val) z (by decide) (by omega)).trans ?_
  unfold writeWindow
  rw [dite_eq_left (by omega)]
  congr 1
  apply Fin.ext
  simp

/-- After the counter rows, the view differs from the entry view only at the counter word 128. -/
theorem before_view (h : MachineState) (i : Index) (ph : Nat) (e : ChainEntry h i ph) (w : Nat) (hw : w<2^33) :
    memoryView (chainBefore h) w=
      writeWord (memoryView h) 128 (Permutation.CounterSalt.ctr (K6Chain.restart (coord i).1)) w := by
  obtain ⟨_,_,_,_,_,mem,_⟩ := chain_before h i ph e
  rw [chain_view_of_mem mem]
  exact memory_at_store (address:=128) (index:=w) (by decide) (by omega)

theorem enter_rows_mem (a : MachineState) (ph : Nat) : (walkRows a (chainEnterRows ph)).mem=a.mem := by
  rw [enter_walk]
  rfl

theorem exit_rows_mem (b : MachineState) : (walkRows b chainExitRows).mem=b.mem := rfl

end TwoPermutationPrototype.GroupedOpening
