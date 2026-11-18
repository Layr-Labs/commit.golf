import CommitGolfCandidate.K3OpenChainPost

/-! Opener chain block (rows 777..795), exit row and post-state: `chain_post`. Owner: C2 (draft by S9-L2). -/
namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open CommitGolfCandidate.Permutation.CounterSalt (coord)
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000
set_option pp.deepTerms false

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC pc_of_set mem_of_set
  mem_of_reg
attribute [local simp] chain_zero_reg

/-! ### Post-state -/

theorem exit_rows (b : MachineState) (pc : b.pc=address 795) :
    (walkRows b chainExitRows).pc=address 796 ∧ (walkRows b chainExitRows).getReg .x10=1024 ∧
      (∀ x, x≠.x10 → (walkRows b chainExitRows).getReg x=b.getReg x) ∧
      (walkRows b chainExitRows).mem=b.mem := by
  refine ⟨?_,?_,?_,?_⟩
  · simp [chainExitRows,walkRows,execInstrBr,pc,address]
  · simp [chainExitRows,walkRows,execInstrBr] <;> decide
  · intro x hx; simp [chainExitRows,walkRows,execInstrBr,Ne.symm hx]
  · simp [chainExitRows,walkRows,execInstrBr,mem_of_set,mem_of_reg]

theorem link_post : ∀ (c : Nat) (s : MachineState), LinkReady s (c+1) → c+1<34 →
    ∀ t ∈ support (linkTrace (c+1) s),
      t.pc=address 795 ∧ (∀ x, x≠.x30 → t.getReg x=s.getReg x) ∧
        (∀ w, w<2^33 → (w<192 ∨ 217≤w) → memoryView t w=memoryView s w)
  | 0,s,r,hc,t,hit => by
    rw [linkTrace, mem_support_bind_iff] at hit
    obtain ⟨z,_,ht⟩ := hit
    rw [linkTrace, support_pure, Set.mem_singleton_iff] at ht
    obtain ⟨_,pc,_,keep,_⟩ := link_step s 0 r hc z
    refine ⟨?_,fun x hx => ?_,fun w hw out => ?_⟩
    · rw [ht]
      simpa using pc
    · rw [ht]
      exact keep x hx
    · rw [ht, chain_view_of_mem (link_rows_mem _)]
      exact reply_outside s z w hw out
  | c+1,s,r,hc,t,hit => by
    rw [linkTrace, mem_support_bind_iff] at hit
    obtain ⟨z,_,more⟩ := hit
    obtain ⟨_,pc,cnt,keep,_⟩ := link_step s (c+1) r hc z
    have next : LinkReady (walkRows (writeBits s (wordAddress 192) z) chainLinkRows) (c+1) :=
      ⟨by simpa using pc,cnt,(keep _ (by decide)).trans r.input,(keep _ (by decide)).trans r.output,
        (keep _ (by decide)).trans r.selector,(keep _ (by decide)).trans r.width,
        (keep _ (by decide)).trans r.primitive⟩
    obtain ⟨tpc,tkeep,tmem⟩ := link_post c _ next (by omega) t more
    refine ⟨tpc,fun x hx => (tkeep x hx).trans (keep x hx),fun w hw out => ?_⟩
    rw [tmem w hw out,chain_view_of_mem (link_rows_mem _)]
    exact reply_outside s z w hw out

theorem chain_post (h : MachineState) (i : Index) (e : ChainEntry h i) (t : MachineState)
    (hit : t ∈ support (chainTrace h i)) :
    t.pc=address (chainStart+19) ∧ t.getReg .x10=1024 ∧ t.getReg .x28=BitVec.ofNat 64 (rank i.val) ∧
      (∀ r, r≠.x7 → r≠.x10 → r≠.x28 → r≠.x30 → r≠.x31 → t.getReg r=h.getReg r) ∧
      (∀ w, w<2^33 → w≠128 → (w<192 ∨ 217≤w) → memoryView t w=memoryView h w) := by
  have lt := links_lt i
  simp only [chainTrace,mem_support_bind_iff] at hit
  obtain ⟨z,_,more⟩ := hit
  obtain ⟨apc,akeep,a30,a28⟩ := after_keyed h i e z
  let a:=writeBits (chainBefore h) (wordAddress 192) z
  have amem (w : Nat) (hw : w<2^33) (w128 : w≠128) (out : w<192 ∨ 217≤w) : memoryView a w=memoryView h w := by
    rw [reply_outside _ z w hw out,before_view h i e w hw]
    simp [writeWord,w128]
  have ax10 : a.getReg .x10=1024 := (akeep _ (by decide) (by decide) (by decide) (by decide)).trans e.input
  show t.pc=address 796 ∧ _
  by_cases zero : chainLinks i=0
  · simp only [zero,if_pos,support_pure,Set.mem_singleton_iff] at more
    subst more
    obtain ⟨_,spc,skeep,smem⟩ := skip_rows a apc (by rw [a30,zero])
    refine ⟨spc,(skeep _).trans ax10,(skeep _).trans a28,fun x b1 b2 b3 b4 b5 => (skeep x).trans (akeep x b1 b3 b4 b5),
      fun w hw w128 out => ?_⟩
    rw [chain_view_of_mem smem]
    exact amem w hw w128 out
  · obtain ⟨c,hc⟩ : ∃ c, chainLinks i=c+1 := ⟨chainLinks i-1,by omega⟩
    simp only [zero,if_neg,not_false_eq_true,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at more
    obtain ⟨b,bhit,rfl⟩ := more
    obtain ⟨_,epc,e10,ekeep,emem⟩ := enter_rows a c apc (by rw [a30,hc]) (by omega)
    have ready : LinkReady (walkRows a chainEnterRows) (c+1) :=
      ⟨epc,(ekeep _ (by decide)).trans (a30.trans (by rw [hc])),
        e10.trans ((akeep _ (by decide) (by decide) (by decide) (by decide)).trans e.output),
        (ekeep _ (by decide)).trans ((akeep _ (by decide) (by decide) (by decide) (by decide)).trans e.output),
        (ekeep _ (by decide)).trans ((akeep _ (by decide) (by decide) (by decide) (by decide)).trans e.selector),
        (ekeep _ (by decide)).trans ((akeep _ (by decide) (by decide) (by decide) (by decide)).trans e.width),
        (ekeep _ (by decide)).trans ((akeep _ (by decide) (by decide) (by decide) (by decide)).trans e.primitive)⟩
    rw [hc] at bhit
    obtain ⟨bpc,bkeep,bmem⟩ := link_post c _ ready (by omega) b bhit
    obtain ⟨xpc,x10,xkeep,xmem⟩ := exit_rows b bpc
    refine ⟨xpc,x10,?_,fun x b1 b2 b3 b4 b5 => ?_,fun w hw w128 out => ?_⟩
    · exact (xkeep _ (by decide)).trans ((bkeep _ (by decide)).trans ((ekeep _ (by decide)).trans a28))
    · exact (xkeep x b2).trans ((bkeep x b4).trans ((ekeep x b2).trans (akeep x b1 b3 b4 b5)))
    · rw [chain_view_of_mem xmem,bmem w hw out,chain_view_of_mem emem]
      exact amem w hw w128 out

end TwoPermutationPrototype.GroupedOpening
