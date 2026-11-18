import CommitGolfCandidate.K3OpenChainRows

/-! Opener chain block (rows 777..795), the link loop: `link_rows`, `link_step`, `link_run`. Owner: O (draft by S9-L2). -/
namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open CommitGolfCandidate.Permutation.CounterSalt (coord)
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000
set_option pp.deepTerms false

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC pc_of_set mem_of_set
  mem_of_reg
attribute [local simp] chain_zero_reg

private theorem link_back (s : MachineState) (pc : s.pc=address 794) (nz : s.getReg .x30≠0#64) :
    execInstrBr s (.BNE .x30 .x0 8184)=s.setPC (address 792) := by
  have yes : (s.getReg .x30 != s.getReg .x0)=true := by simp [open_zero,nz]
  simp only [execInstrBr,yes,ite_true,pc]
  exact congrArg s.setPC (by decide : address 794+signExtend13 8184=address 792)

private theorem link_fall (s : MachineState) (pc : s.pc=address 794) (z : s.getReg .x30=0#64) :
    execInstrBr s (.BNE .x30 .x0 8184)=s.setPC (address 795) := by
  simp only [execInstrBr,open_zero,z,beq_self_eq_true,ite_true,pc]
  exact congrArg s.setPC (by decide : address 794+4=address 795)

private theorem minus_one : (-1 : BitVec 12)=4095#12 := by decide

private theorem link_dec (w : MachineState) (c : Nat) (pc : w.pc=address 793)
    (cnt : w.getReg .x30=BitVec.ofNat 64 (c+1)) (hc : c+1<34) :
    (execInstrBr w (.ADDI .x30 .x30 (-1))).pc=address 794 ∧
      (execInstrBr w (.ADDI .x30 .x30 (-1))).getReg .x30=BitVec.ofNat 64 c ∧
      (∀ x, x≠.x30 → (execInstrBr w (.ADDI .x30 .x30 (-1))).getReg x=w.getReg x) ∧
      (execInstrBr w (.ADDI .x30 .x30 (-1))).mem=w.mem := by
  refine ⟨?_,?_,?_,rfl⟩
  · change w.pc+4=_; rw [pc]; exact address_succ 793
  · change w.getReg .x30+signExtend12 (-1)=_; rw [cnt,minus_one]; exact dec_word c hc
  · intro x hx
    change ((w.setReg .x30 (w.getReg .x30+signExtend12 (-1))).setPC (w.pc+4)).getReg x=_
    rw [MachineState.getReg_setPC,Opening.getReg_setReg,if_neg (fun h => hx h.1.symm)]

/-- Two rows, for abstract instructions (the kernel never evaluates the immediates). -/
private theorem walk_two (w : MachineState) (a b : Nat) (p q : Instr) :
    walkRows w [(a,p),(b,q)]=execInstrBr (execInstrBr w p) q := rfl

private theorem link_walk (w : MachineState) : walkRows w chainLinkRows=
    execInstrBr (execInstrBr w (.ADDI .x30 .x30 (-1))) (.BNE .x30 .x0 8184) := by
  unfold chainLinkRows; exact walk_two w _ _ _ _

private theorem link_legal (w : MachineState) (pc : w.pc=address 793)
    (dpc : (execInstrBr w (.ADDI .x30 .x30 (-1))).pc=address 794) : legal chainLinkRows w :=
  ⟨pc,(ord_iff _ _ rfl).mpr (no_mem_valid _ _ rfl),dpc,(ord_iff _ _ rfl).mpr (no_mem_valid _ _ rfl),trivial⟩

private theorem link_branch (d : MachineState) (c : Nat) (dpc : d.pc=address 794)
    (d30 : d.getReg .x30=BitVec.ofNat 64 c) (hc : c<34) :
    execInstrBr d (.BNE .x30 .x0 8184)=d.setPC (if c=0 then address 795 else address 792) := by
  by_cases zc : c=0
  · rw [if_pos zc]; subst zc; exact link_fall d dpc d30
  · rw [if_neg zc]; exact link_back d dpc (fun e => small_ne c hc zc (d30.symm.trans e))

/-- `addi x30,x30,-1 ; bne x30,x0,L` from row 793 with `c+1` links to go. -/
theorem link_rows (w : MachineState) (c : Nat) (pc : w.pc=address 793)
    (cnt : w.getReg .x30=BitVec.ofNat 64 (c+1)) (hc : c+1<34) :
    legal chainLinkRows w ∧
      (walkRows w chainLinkRows).pc=(if c=0 then address 795 else address 792) ∧
      (walkRows w chainLinkRows).getReg .x30=BitVec.ofNat 64 c ∧
      (∀ x, x≠.x30 → (walkRows w chainLinkRows).getReg x=w.getReg x) ∧
      (walkRows w chainLinkRows).mem=w.mem := by
  obtain ⟨dpc,d30,dkeep,dmem⟩ := link_dec w c pc cnt hc
  have hp := (link_walk w).trans (link_branch _ c dpc d30 (by omega))
  refine ⟨link_legal w pc dpc,?_,?_,?_,?_⟩
  · rw [hp]; exact pc_of_set _ _
  · rw [hp,MachineState.getReg_setPC]; exact d30
  · intro x hx; rw [hp,MachineState.getReg_setPC]; exact dkeep x hx
  · rw [hp,mem_of_set]; exact dmem

/-- The state after one link: reply written, `addi; bne` run. -/
theorem link_step {bits : Nat} (s : MachineState) (c : Nat) (r : LinkReady s (c+1)) (hc : c+1<34)
    (z : BitVec bits) :
    let w:=walkRows (writeBits s (wordAddress 192) z) chainLinkRows
    legal chainLinkRows (writeBits s (wordAddress 192) z) ∧
      w.pc=(if c=0 then address 795 else address 792) ∧ w.getReg .x30=BitVec.ofNat 64 c ∧
      (∀ x, x≠.x30 → w.getReg x=s.getReg x) ∧ w.mem=(writeBits s (wordAddress 192) z).mem := by
  have regs (x : Reg) : (writeBits s (wordAddress 192) z).getReg x=s.getReg x := writeBits_register ..
  have wpc : (writeBits s (wordAddress 192) z).pc=address 793 := by
    rw [write_pc,r.pc]; exact address_succ 792
  obtain ⟨ok,pc,cnt,keep,mem⟩ := link_rows _ c wpc ((regs _).trans r.count) hc
  exact ⟨ok,pc,cnt,fun x hx => (keep x hx).trans (regs x),mem⟩

/-- `c+1` links followed by the exit row `addi x10,x0,1024`. -/
theorem link_run (c : Nat) : ∀ (s : MachineState), LinkReady s (c+1) → c+1<34 → ∀ fuel,
    execute openingImage (3*(c+1)+(1+fuel)) s true =
      (do let t ← linkTrace (c+1) s; let z ← execute openingImage fuel (walkRows t chainExitRows) true
          return z.charge (10*(c+1)+1) (c+1)) := by
  have lens := chain_lengths
  induction c with
  | zero =>
    intro s r hc fuel
    rw [show 3*(0+1)+(1+fuel)=((chainLinkRows.length+(chainExitRows.length+fuel)))+1 by rw [lens.2.2.2.2.2.2.1,lens.2.2.2.2.2.2.2.2.1]; omega,
      execute_permutation_call openingImage _ s true 192 192 (by decide) (by decide) r.input r.output r.selector
        r.width r.primitive (link_fetch _ r.pc)]
    simp only [linkTrace,bind_assoc,pure_bind]
    apply bind_congr; intro z
    obtain ⟨ok,pc,_,_,_⟩ := link_step s 0 r (by omega) z
    rw [walk_rows_run _ chainLinkRows ok chain_link_fetch _ true]
    have exitOk : legal chainExitRows (walkRows (writeBits s (wordAddress 192) z) chainLinkRows) := by
      simp only [if_pos rfl] at pc
      exact ⟨pc,rfl,trivial⟩
    rw [walk_rows_run _ chainExitRows exitOk chain_exit_fetch _ true]
    simp only [bind_assoc,pure_bind]
    apply bind_congr; intro y; apply congrArg pure
    simp [Execution.charge,lens.2.2.2.2.2.2.2.1,lens.2.2.2.2.2.2.2.2.2]
    first | omega | (constructor <;> omega)
  | succ c ih =>
    intro s r hc fuel
    rw [show 3*(c+1+1)+(1+fuel)=(chainLinkRows.length+(3*(c+1)+(1+fuel)))+1 by rw [lens.2.2.2.2.2.2.1]; omega,
      execute_permutation_call openingImage _ s true 192 192 (by decide) (by decide) r.input r.output r.selector
        r.width r.primitive (link_fetch _ r.pc)]
    simp only [linkTrace,bind_assoc,pure_bind]
    apply bind_congr; intro z
    obtain ⟨ok,pc,cnt,keep,_⟩ := link_step s (c+1) r hc z
    rw [walk_rows_run _ chainLinkRows ok chain_link_fetch _ true]
    have next : LinkReady (walkRows (writeBits s (wordAddress 192) z) chainLinkRows) (c+1) :=
      ⟨by simpa using pc,cnt,(keep _ (by decide)).trans r.input,(keep _ (by decide)).trans r.output,
        (keep _ (by decide)).trans r.selector,(keep _ (by decide)).trans r.width,
        (keep _ (by decide)).trans r.primitive⟩
    rw [ih _ next (by omega) fuel]
    simp only [bind_assoc,pure_bind]
    apply bind_congr; intro t
    apply bind_congr; intro y; apply congrArg pure
    simp [Execution.charge,lens.2.2.2.2.2.2.2.1]
    first | omega | (constructor <;> omega)

end TwoPermutationPrototype.GroupedOpening
