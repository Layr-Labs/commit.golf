import CommitGolfCandidate.K3OpenChainPost

/-! Opener chain block (rows 3097..3105 and the link block 3106..3138), exit row and post-state: `chain_post`. Owner: C2 (draft by S9-L2). -/
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

theorem exit_rows (b : MachineState) (pc : b.pc=address linkEnd) :
    (walkRows b chainExitRows).pc=address 3139 ∧
      (∀ x, (walkRows b chainExitRows).getReg x=b.getReg x) ∧
      (walkRows b chainExitRows).mem=b.mem :=
  ⟨pc,fun _ => rfl,rfl⟩

theorem link_post : ∀ (c : Nat) (s : MachineState), LinkReady s c → c<34 →
    ∀ t ∈ support (linkTrace c s),
      t.pc=address linkEnd ∧ (∀ x, t.getReg x=s.getReg x) ∧
        (∀ w, w<2^33 → (w<192 ∨ 217≤w) → memoryView t w=memoryView s w)
  | 0,s,r,_,t,hit => by
    rw [linkTrace, support_pure, Set.mem_singleton_iff] at hit
    subst hit
    exact ⟨by simpa using r.pc,fun _ => rfl,fun _ _ _ => rfl⟩
  | c+1,s,r,hc,t,hit => by
    rw [linkTrace, mem_support_bind_iff] at hit
    obtain ⟨z,_,more⟩ := hit
    have regs (x : Reg) : (writeBits s (wordAddress 192) z).getReg x=s.getReg x := writeBits_register ..
    have next : LinkReady (writeBits s (wordAddress 192) z) c :=
      ⟨by rw [write_pc,r.pc,address_succ]; congr 1; unfold linkEnd; omega,
        (regs _).trans r.input,(regs _).trans r.output,(regs _).trans r.selector,(regs _).trans r.width,
        (regs _).trans r.primitive⟩
    obtain ⟨tpc,tkeep,tmem⟩ := link_post c _ next (by omega) t more
    refine ⟨tpc,fun x => (tkeep x).trans (regs x),fun w hw out => ?_⟩
    rw [tmem w hw out]
    exact reply_outside s z w hw out

theorem chain_post (h : MachineState) (i : Index) (e : ChainEntry h i) (t : MachineState)
    (hit : t ∈ support (chainTrace h i)) :
    t.pc=address 3139 ∧ t.getReg .x28=BitVec.ofNat 64 (tabS (i.val%4096)) ∧
      t.getReg .x3=BitVec.ofNat 64 i.val <<< (4:Nat) ∧
      (∀ r, r≠.x3 → r≠.x7 → r≠.x10 → r≠.x28 → r≠.x30 → r≠.x31 → t.getReg r=h.getReg r) ∧
      (∀ w, w<2^33 → w≠128 → (w<192 ∨ 217≤w) → memoryView t w=memoryView h w) := by
  have lt := links_lt i
  simp only [chainTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hit
  obtain ⟨z,_,b,bhit,hb⟩ := hit
  have ht : t=b := by rw [hb]; rfl
  subst ht
  obtain ⟨apc,akeep,a28,a7,a3⟩ := after_keyed h i e z
  let a:=writeBits (chainBefore h) (wordAddress 192) z
  have amem (w : Nat) (hw : w<2^33) (w128 : w≠128) (out : w<192 ∨ 217≤w) : memoryView a w=memoryView h w := by
    rw [reply_outside _ z w hw out,before_view h i e w hw]
    simp [writeWord,w128]
  obtain ⟨_,epc,e10,ekeep,emem⟩ := enter_rows a (chainLinks i) apc (by rw [a7,tab_t_links]) lt
  have ready : LinkReady (walkRows a chainEnterRows) (chainLinks i) :=
    ⟨epc,e10.trans ((akeep _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans e.output),
      (ekeep _ (by decide)).trans ((akeep _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans e.output),
      (ekeep _ (by decide)).trans ((akeep _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans e.selector),
      (ekeep _ (by decide)).trans ((akeep _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans e.width),
      (ekeep _ (by decide)).trans ((akeep _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans e.primitive)⟩
  obtain ⟨bpc,bkeep,bmem⟩ := link_post _ _ ready lt t bhit
  obtain ⟨xpc,xkeep,xmem⟩ := exit_rows t bpc
  refine ⟨xpc,?_,?_,fun x b0 b1 b2 b3 b4 b5 => ?_,fun w hw w128 out => ?_⟩
  · exact (xkeep _).trans ((bkeep _).trans ((ekeep _ (by decide)).trans a28))
  · exact (xkeep _).trans ((bkeep _).trans ((ekeep _ (by decide)).trans a3))
  · exact (xkeep x).trans ((bkeep x).trans ((ekeep x b2).trans (akeep x b0 b1 b3 b4 b5)))
  · rw [bmem w hw out,chain_view_of_mem emem]
    exact amem w hw w128 out

end TwoPermutationPrototype.GroupedOpening
