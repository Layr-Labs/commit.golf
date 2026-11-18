import CommitGolfCandidate.K3OpenChainLink
import CommitGolfCandidate.Counting

/-! Opener chain block (rows 777..795 and the link groups at rows 4..14), fixed oracle and memory views:
`chain_fixed`. Owner: H (draft by S9-L2; 4-unrolled links). -/
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

theorem linkGroupState_succ (o : Oracle) (q : Nat) (s : MachineState) :
    linkGroupState o (q+1) s=linkGroupState o q (linkGroupStep o s) := Function.iterate_succ_apply _ _ _

theorem restState_succ (o : Oracle) (r : Nat) (s : MachineState) :
    restState o (r+1) s=restState o r (restStep o s) := Function.iterate_succ_apply _ _ _

theorem group_fixed (o : Oracle) : ∀ (q : Nat) (s : MachineState),
    o.run (linkGroupTrace q s)=pure (linkGroupState o q s,4*q)
  | 0,s => by rw [linkGroupTrace,oracle_run_pure]; rfl
  | q+1,s => by
    rw [linkGroupTrace]
    simp only [callTrace,bind_assoc,pure_bind]
    rw [oracle_run_public_bind]
    simp only [answer_forward]
    rw [oracle_run_public_bind]
    simp only [answer_forward]
    rw [oracle_run_public_bind]
    simp only [answer_forward]
    rw [oracle_run_public_bind]
    simp only [answer_forward]
    rw [group_fixed o q,linkGroupState_succ,show 4*(q+1)=1+(1+(1+(1+4*q))) by omega]
    simp only [pure_bind]
    rfl

theorem rest_fixed (o : Oracle) : ∀ (r : Nat) (s : MachineState),
    o.run (restTrace r s)=pure (restState o r s,r)
  | 0,s => by rw [restTrace,oracle_run_pure]; rfl
  | r+1,s => by
    rw [restTrace]
    simp only [callTrace,bind_assoc,pure_bind]
    rw [oracle_run_public_bind]
    simp only [answer_forward]
    rw [rest_fixed o r,restState_succ]
    simp only [pure_bind,Nat.add_comm 1 r]
    rfl

theorem chain_fixed (o : Oracle) (k : BitVec 192) (h : MachineState) (i : Index) (e : ChainEntry h i)
    (key : KeyWords h k) :
    o.run (chainTrace h i)=pure (chainState o h i,chainCalls i) := by
  rw [chainTrace,oracle_run_public_bind]
  simp only [answer_forward]
  unfold chainState chainCalls
  by_cases zero : chainLinks i=0
  · simp only [if_pos zero,oracle_run_pure,pure_bind]
    rw [zero]
    rfl
  · simp only [if_neg zero,oracle_run_bind,group_fixed,rest_fixed,oracle_run_pure,pure_bind,Nat.add_zero]
    rw [show 1+chainLinks i=1+(4*(chainLinks i/4)+chainLinks i%4) by omega]
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
theorem before_view (h : MachineState) (i : Index) (e : ChainEntry h i) (w : Nat) (hw : w<2^33) :
    memoryView (chainBefore h) w=
      writeWord (memoryView h) 128 (Permutation.CounterSalt.ctr (K6Chain.restart (coord i).1)) w := by
  obtain ⟨_,_,_,_,mem,_⟩ := chain_before h i e
  rw [chain_view_of_mem mem]
  exact memory_at_store (address:=128) (index:=w) (by decide) (by omega)

/-- One `addi`, branch or `jal x0` row leaves memory unchanged (immediates kept abstract). -/
theorem exec_mem_addi (s : MachineState) (rd rs : Reg) (imm : BitVec 12) :
    (execInstrBr s (.ADDI rd rs imm)).mem=s.mem :=
  (mem_of_set _ _).trans (mem_of_reg _ _ _)

theorem exec_mem_beq (s : MachineState) (a b : Reg) (off : BitVec 13) :
    (execInstrBr s (.BEQ a b off)).mem=s.mem := by
  show (if s.getReg a == s.getReg b then s.setPC _ else s.setPC _).mem=s.mem
  split <;> rfl

theorem exec_mem_bne (s : MachineState) (a b : Reg) (off : BitVec 13) :
    (execInstrBr s (.BNE a b off)).mem=s.mem := by
  show (if s.getReg a != s.getReg b then s.setPC _ else s.setPC _).mem=s.mem
  split <;> rfl

theorem exec_mem_blt (s : MachineState) (a b : Reg) (off : BitVec 13) :
    (execInstrBr s (.BLT a b off)).mem=s.mem := by
  show (if BitVec.slt (s.getReg a) (s.getReg b) then s.setPC _ else s.setPC _).mem=s.mem
  split <;> rfl

theorem exec_mem_jal (s : MachineState) (off : BitVec 21) : (execInstrBr s (.JAL .x0 off)).mem=s.mem := rfl

theorem test_rows_mem (s : MachineState) : (walkRows s groupTestRows).mem=s.mem := by
  rw [test_walk,exec_mem_blt,exec_mem_addi]

theorem back_rows_mem (s : MachineState) : (walkRows s groupBackRows).mem=s.mem := by
  rw [back_walk,exec_mem_jal]

theorem out_rows_mem (s : MachineState) : (walkRows s groupOutRows).mem=s.mem := by
  rw [out_walk,exec_mem_beq,exec_mem_addi,exec_mem_blt,exec_mem_addi]

theorem rest_rows_mem (s : MachineState) : (walkRows s restRows).mem=s.mem := by
  rw [rest_walk,exec_mem_bne,exec_mem_addi,exec_mem_jal]

theorem enter_rows_mem (a : MachineState) : (walkRows a chainEnterRows).mem=a.mem := by
  rw [enter_walk,exec_mem_jal,exec_mem_addi,exec_mem_beq]

theorem skip_rows_mem (a : MachineState) : (walkRows a chainSkipRows).mem=a.mem := by
  simp only [chainSkipRows,walkRows,List.foldl,exec_mem_beq]

theorem exit_rows_mem (b : MachineState) : (walkRows b chainExitRows).mem=b.mem := by
  simp only [chainExitRows,walkRows,List.foldl,exec_mem_addi]

end TwoPermutationPrototype.GroupedOpening
