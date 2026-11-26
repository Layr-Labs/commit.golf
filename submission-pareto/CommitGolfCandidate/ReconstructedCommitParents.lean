import CommitGolfCandidate.ReconstructedCommitParentsRootCopy

namespace CommitGolfCandidate.Reconstruction.CommitParents
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding CommitExact
set_option maxHeartbeats 1000000
set_option maxRecDepth 14000
attribute [local irreducible] readBuffer

structure Result (o : Oracle) (leaves : Nat→Binding.Digest) (initial final : MachineState) : Prop where
  commitment : readBuffer final 4294971392 32 = pack (node (rawC o) leaves 0 1)
  root : cell final (addr 0 1) = node (rawC o) leaves 0 1
  heap : ∀ e k, Cell e k → 0<e → cell final (addr e k)=consumed e k (node (rawC o) leaves e k)
  frame : ∀ a n, a+n≤2^64 → (a+n≤4294971392 ∨ 5637148400≤a) → readBuffer final a n=readBuffer initial a n

theorem Result.outside {o leaves s t} (h : Result o leaves s t) (a n : Nat)
    (bound : a+n≤2^64) (above : 5637148400≤a) : readBuffer t a n=readBuffer s a n :=
  h.frame a n bound (Or.inr above)

theorem Result.key {o leaves s t} (h : Result o leaves s t) :
    readBuffer t 5637148560 24=readBuffer s 5637148560 24 :=
  h.frame _ _ (by decide) (Or.inr (by decide))

private theorem prepare_halt (o : Oracle) (s : MachineState) (start : s.pc=CommitBlocks.addr 150129) :
    ∃ t, Segment o CommitSetup.im 2 s t ∧ t.mem=s.mem ∧ t.pc=CommitBlocks.addr 150131 ∧
      t.getReg .x5=1 ∧ t.getReg .x10=0 := by
  let a := execInstrBr s (.ADDI .x5 .x0 1)
  let b := execInstrBr a (.ADDI .x10 .x0 0)
  have one : Segment o CommitSetup.im 1 s a := plain o _ s a _ (CommitSetup.fetch_at 150129 _ rfl s start) rfl
  have ap : a.pc=CommitBlocks.addr 150130 := congrArg (·+4) start
  have two : Segment o CommitSetup.im 1 a b := plain o _ a b _ (CommitSetup.fetch_at 150130 _ rfl a ap) rfl
  exact ⟨b,compose one two,rfl,congrArg (·+4) ap,rfl,rfl⟩

/-- All parents, the four output copies and HALT setup in the pinned image. -/
theorem certified_segment (o : Oracle) (leaves : Nat→Binding.Digest) (can : ∀ k, Canonical 24 (leaves k))
    (s : MachineState) (pc : s.pc=CommitBlocks.addr 53016) (kind : s.getReg .x5=0)
    (initial : Snapshot (cell s) (node (rawC o) leaves) 23 (2^23)) :
    ∃ t, Segment o CommitSetup.im 108073565 s t ∧ t.pc=CommitBlocks.addr 150131 ∧
      t.getReg .x5=1 ∧ t.getReg .x10=0 ∧ Result o leaves s t := by
  obtain ⟨v,tree,entry,top,heap,frame,source⟩ := built_tree o leaves can s pc kind initial
  obtain ⟨a,copied,next,bytes,write⟩ := RootCopy.copy_root o v entry source
  obtain ⟨t,endSeg,mem,last,code,ok⟩ := prepare_halt o a next
  have steps : treeSteps 23+11+2=108073565 := by decide
  refine ⟨t,steps ▸ compose (compose tree copied) endSeg,last,code,ok,⟨?_,?_,?_,?_⟩⟩
  · have h : cell t 4294971392 = node (rawC o) leaves 0 1 := (cell_congr mem _).trans (bytes.trans top)
    simpa only [cell,pack_unpack] using congrArg pack h
  · exact (cell_congr mem _).trans ((write.cell_at (by decide) (Or.inr (by decide))).trans top)
  · intro e k h pos
    have small : addr e k+32≤2^64 := by
      have lim := Nat.pow_le_pow_right (n:=2) (by decide) (show e+1≤25 by have := h.1;omega)
      have bound := h.2.2;have dep := h.1;unfold addr;omega
    have safe : RootCopy.dst+32≤addr e k := by unfold RootCopy.dst addr;omega
    exact (cell_congr mem _).trans ((write.cell_at small (Or.inr safe)).trans (heap e k h pos))
  · intro a' n small away
    unfold RootCopy.dst at write
    exact (read_buffer_memory_congr _ _ mem _ _).trans ((write a' n small (by omega)).trans
      (frame a' n small (by omega)))

/-- After the leaf loop every fixed public oracle and canonical initialized
leaf table gives a successful execution for any remaining fuel. -/
theorem certified (o : Oracle) (leaves : Nat→Binding.Digest) (can : ∀ k, Canonical 24 (leaves k))
    (s : MachineState) (pc : s.pc=CommitBlocks.addr 53016) (kind : s.getReg .x5=0)
    (initial : Snapshot (cell s) (node (rawC o) leaves) 23 (2^23)) :
    ∃ t c q, Result o leaves s t ∧ ∀ fuel,
      fixedOracleRun o (execute CommitSetup.im (108073566+fuel) s true)=pure (⟨.success,t,c,q⟩ : Execution) := by
  obtain ⟨t,⟨c,q,seg⟩,pos,code,ok,output⟩ := certified_segment o leaves can s pc kind initial
  have halt := CommitSetup.fetch_at 150131 (.base .ECALL) rfl t pos
  refine ⟨t,c+1,q,output,?_⟩
  intro fuel
  rw [show 108073566+fuel=108073565+(fuel+1) by omega,seg,execute,halt]
  simp [code,ok,fixed_oracle_run_pure,Execution.charge]

end CommitGolfCandidate.Reconstruction.CommitParents
