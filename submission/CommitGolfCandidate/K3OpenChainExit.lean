import CommitGolfCandidate.K3OpenChainPost

/-! Opener chain block (rows 777..795 and the link groups at rows 4..14), exit row and post-state: `chain_post`.
Owner: C2 (draft by S9-L2; 4-unrolled links). -/
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

/-- A link call moves the PC one row, keeps every register and the view outside the reply window. -/
theorem call_post (s t : MachineState) (hit : t ∈ support (callTrace s)) :
    t.pc=s.pc+4 ∧ (∀ x, t.getReg x=s.getReg x) ∧
      (∀ w, w<2^33 → (w<192 ∨ 217≤w) → memoryView t w=memoryView s w) := by
  simp only [callTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hit
  obtain ⟨z,_,rfl⟩ := hit
  exact ⟨write_pc _ _ _,fun x => writeBits_register ..,fun w hw out => reply_outside s z w hw out⟩

theorem group_post (q : Nat) : ∀ (c : Nat) (s : MachineState), LinkGroupReady s (4*q+c) → 4*q+c<34 →
    ∀ t ∈ support (linkGroupTrace q s),
      LinkGroupReady t c ∧ (∀ x, x≠.x30 → t.getReg x=s.getReg x) ∧
        (∀ w, w<2^33 → (w<192 ∨ 217≤w) → memoryView t w=memoryView s w) := by
  induction q with
  | zero =>
    intro c s r _ t hit
    rw [linkGroupTrace,support_pure,Set.mem_singleton_iff] at hit
    subst hit
    exact ⟨by simpa using r,fun _ _ => rfl,fun _ _ _ => rfl⟩
  | succ q ih =>
    intro c s r hc t hit
    obtain ⟨_,tp⟩ := test_rows s _ (by omega) hc r.pc r.count
    rw [linkGroupTrace] at hit
    simp only [mem_support_bind_iff] at hit
    obtain ⟨a,ha,b,hb,c3,hc3,d,hd,ht⟩ := hit
    obtain ⟨apc,areg,amem⟩ := call_post _ a ha
    obtain ⟨bpc,breg,bmem⟩ := call_post _ b hb
    obtain ⟨cpc,creg,cmem⟩ := call_post _ c3 hc3
    obtain ⟨dpc,dreg,dmem⟩ := call_post _ d hd
    have dpc' : d.pc=address 10 := by
      rw [dpc,cpc,bpc,apc,tp.pc,address_succ 6,address_succ 7,address_succ 8,address_succ 9]
    have dkeep (x : Reg) : d.getReg x=(walkRows s groupTestRows).getReg x :=
      (dreg x).trans ((creg x).trans ((breg x).trans (areg x)))
    obtain ⟨_,bp⟩ := back_rows d dpc'
    have ready : LinkGroupReady (walkRows d groupBackRows) (4*q+c) :=
      ⟨bp.pc,bp.r30.trans ((dkeep _).trans (tp.r30.trans (by congr 1; omega))),
        (r.regs.keep tp.keep).keep (fun x hx => (bp.keep x hx).trans (dkeep x))⟩
    obtain ⟨tr,tkeep,tmem⟩ := ih c _ ready (by omega) t ht
    refine ⟨tr,fun x hx => (tkeep x hx).trans ((bp.keep x hx).trans ((dkeep x).trans (tp.keep x hx))),
      fun w hw out => ?_⟩
    rw [tmem w hw out,chain_view_of_mem bp.mem,dmem w hw out,cmem w hw out,bmem w hw out,amem w hw out,
      chain_view_of_mem tp.mem]

theorem rest_post (r : Nat) : ∀ (s : MachineState), RestReady s r → r<34 →
    ∀ t ∈ support (restTrace r s),
      t.pc=address 795 ∧ (∀ x, x≠.x30 → t.getReg x=s.getReg x) ∧
        (∀ w, w<2^33 → (w<192 ∨ 217≤w) → memoryView t w=memoryView s w) := by
  induction r with
  | zero =>
    intro s rr _ t hit
    rw [restTrace,support_pure,Set.mem_singleton_iff] at hit
    subst hit
    exact ⟨by simpa using rr.pc,fun _ _ => rfl,fun _ _ _ => rfl⟩
  | succ r ih =>
    intro s rr hc t hit
    have pc : s.pc=address 13 := by simpa using rr.pc
    rw [restTrace] at hit
    simp only [mem_support_bind_iff] at hit
    obtain ⟨a,ha,ht⟩ := hit
    obtain ⟨apc,areg,amem⟩ := call_post _ a ha
    obtain ⟨_,rp⟩ := rest_rows a r hc (by rw [apc,pc]; exact address_succ 13) ((areg _).trans rr.count)
    have ready : RestReady (walkRows a restRows) r :=
      ⟨rp.pc,rp.r30,rr.regs.keep (fun x hx => (rp.keep x hx).trans (areg x))⟩
    obtain ⟨tpc,tkeep,tmem⟩ := ih _ ready (by omega) t ht
    exact ⟨tpc,fun x hx => (tkeep x hx).trans ((rp.keep x hx).trans (areg x)),
      fun w hw out => by rw [tmem w hw out,chain_view_of_mem rp.mem,amem w hw out]⟩

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
    obtain ⟨g,ghit,b,bhit,rfl⟩ := more
    obtain ⟨_,epc,e10,ekeep,emem⟩ := enter_rows a c apc (by rw [a30,hc]) (by omega)
    have kept (x : Reg) (b1 : x≠.x7) (b2 : x≠.x28) (b3 : x≠.x30) (b4 : x≠.x31) (b5 : x≠.x10) :=
      (ekeep x b5).trans (akeep x b1 b2 b3 b4)
    have ready : LinkGroupReady (walkRows a chainEnterRows) (4*(chainLinks i/4)+chainLinks i%4) :=
      ⟨epc,(ekeep _ (by decide)).trans (a30.trans (by congr 1; omega)),
        ⟨e10.trans ((akeep _ (by decide) (by decide) (by decide) (by decide)).trans e.output),
          (kept _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans e.output,
          (kept _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans e.selector,
          (kept _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans e.width,
          (kept _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans e.primitive⟩⟩
    obtain ⟨rg,gkeep,gmem⟩ := group_post _ _ _ ready (by omega) g ghit
    obtain ⟨_,op⟩ := out_rows g _ (by omega) rg.pc rg.count
    obtain ⟨bpc,bkeep,bmem⟩ := rest_post _ _ ⟨op.pc,op.r30,rg.regs.keep op.keep⟩ (by omega) b bhit
    obtain ⟨xpc,x10,xkeep,xmem⟩ := exit_rows b bpc
    have mid (x : Reg) (hx : x≠.x30) : b.getReg x=(walkRows a chainEnterRows).getReg x :=
      (bkeep x hx).trans ((op.keep x hx).trans (gkeep x hx))
    refine ⟨xpc,x10,?_,fun x b1 b2 b3 b4 b5 => ?_,fun w hw w128 out => ?_⟩
    · exact (xkeep _ (by decide)).trans ((mid _ (by decide)).trans ((ekeep _ (by decide)).trans a28))
    · exact (xkeep x b2).trans ((mid x b4).trans (kept x b1 b3 b4 b5 b2))
    · rw [chain_view_of_mem xmem,bmem w hw out,chain_view_of_mem op.mem,gmem w hw out,chain_view_of_mem emem]
      exact amem w hw w128 out

end TwoPermutationPrototype.GroupedOpening
