import CommitGolfCandidate.K3OpenChainPost

/-! Opener chain block (rows 777..795 and the link calls at rows 896..929), return and exit rows and post-state:
`chain_post`. Owner: C2 (draft by S9-L2; 33-call chain). -/
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

/-- A link call moves the PC one row, keeps every register and the view outside the reply window. -/
theorem call_post (s t : MachineState) (hit : t ∈ support (callTrace s)) :
    t.pc=s.pc+4 ∧ (∀ x, t.getReg x=s.getReg x) ∧
      (∀ w, w<2^33 → (w<192 ∨ 217≤w) → memoryView t w=memoryView s w) := by
  simp only [callTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hit
  obtain ⟨z,_,rfl⟩ := hit
  exact ⟨write_pc _ _ _,fun x => writeBits_register ..,fun w hw out => reply_outside s z w hw out⟩

theorem calls_post (c : Nat) : ∀ (s : MachineState), s.pc=address (929-c) → c≤33 →
    ∀ t ∈ support (callsTrace c s),
      t.pc=address 929 ∧ (∀ x, t.getReg x=s.getReg x) ∧
        (∀ w, w<2^33 → (w<192 ∨ 217≤w) → memoryView t w=memoryView s w) := by
  induction c with
  | zero =>
    intro s pc _ t hit
    rw [callsTrace,support_pure,Set.mem_singleton_iff] at hit
    subst hit
    exact ⟨pc,fun _ => rfl,fun _ _ _ => rfl⟩
  | succ c ih =>
    intro s pc hc t hit
    rw [callsTrace] at hit
    simp only [mem_support_bind_iff] at hit
    obtain ⟨a,ha,ht⟩ := hit
    obtain ⟨apc,areg,amem⟩ := call_post _ a ha
    have apc' : a.pc=address (929-c) := by
      rw [apc,pc,show 929-(c+1)=928-c by omega,address_succ]; congr 1; omega
    obtain ⟨tpc,treg,tmem⟩ := ih a apc' (by omega) t ht
    exact ⟨tpc,fun x => (treg x).trans (areg x),fun w hw out => by rw [tmem w hw out,amem w hw out]⟩

theorem chain_post (h : MachineState) (i : Index) (e : ChainEntry h i) (t : MachineState)
    (hit : t ∈ support (chainTrace h i)) :
    t.pc=address (chainStart+19) ∧ t.getReg .x10=1024 ∧ t.getReg .x28=BitVec.ofNat 64 (rank i.val) ∧
      (∀ r, r≠.x7 → r≠.x10 → r≠.x28 → r≠.x30 → r≠.x31 → t.getReg r=h.getReg r) ∧
      (∀ w, w<2^33 → w≠128 → (w<192 ∨ 217≤w) → memoryView t w=memoryView h w) := by
  have lt := links_lt i
  simp only [chainTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hit
  obtain ⟨z,_,b,bhit,rfl⟩ := hit
  obtain ⟨apc,akeep,a30,a28⟩ := after_keyed h i e z
  let a:=writeBits (chainBefore h) (wordAddress 192) z
  have amem (w : Nat) (hw : w<2^33) (w128 : w≠128) (out : w<192 ∨ 217≤w) : memoryView a w=memoryView h w := by
    rw [reply_outside _ z w hw out,before_view h i e w hw]
    simp [writeWord,w128]
  obtain ⟨_,epc,_,ekeep,emem⟩ := enter_rows a _ lt apc a30
  obtain ⟨bpc,breg,bmem⟩ := calls_post _ _ epc (by omega) b bhit
  obtain ⟨_,xpc,x10,xkeep,xmem⟩ := out_rows b bpc
  show _=address 796 ∧ _
  refine ⟨xpc,x10,?_,fun x b1 b2 b3 b4 b5 => ?_,fun w hw w128 out => ?_⟩
  · rw [xkeep _ (by decide),breg,ekeep _ (by decide) (by decide) (by decide)]; exact a28
  · rw [xkeep x b2,breg,ekeep x b1 b2 b5]; exact akeep x b1 b3 b4 b5
  · rw [chain_view_of_mem xmem,bmem w hw out,chain_view_of_mem emem]
    exact amem w hw w128 out

end TwoPermutationPrototype.GroupedOpening
