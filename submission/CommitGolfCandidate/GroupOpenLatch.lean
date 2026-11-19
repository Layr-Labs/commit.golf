import CommitGolfCandidate.GroupOpenSelect
import CommitGolfCandidate.K3OpenChain

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
set_option maxRecDepth 18000
set_option maxHeartbeats 1800000
attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC pc_of_set mem_of_set open_zero
attribute [local simp] mem_of_reg MachineState.getMem_setPC MachineState.getMem_setReg

def finalPC (left : Nat) := if left=1 then address 15 else address 740
def advanced (s : MachineState) (left : Nat) := walkRows s (nextRows (decide (left=1)))

private theorem decremented (left : Nat) (l : 0<left) :
    countWord left+signExtend12 (-1)=countWord (left-1) := by
  have sub := BitVec.ofNat_sub_ofNat_of_le (w:=64) left 1 (by decide) l
  rw [BitVec.sub_eq_add_neg] at sub
  exact sub

private theorem counter_zero (left : Nat) (l : 0<left) (small : left≤16777216) :
    countWord (left-1)=0#64 ↔ left=1 := by
  constructor
  · intro h;have z:=congrArg BitVec.toNat h
    change (left-1)%2^64=0 at z;omega
  · intro h;subst left;rfl

private theorem index_bump (ord : Nat) : indexAt ord+signExtend12 8=indexAt (ord+1) := by
  change BitVec.ofNat 64 _+BitVec.ofNat 64 8=_
  rw [←BitVec.ofNat_add];unfold indexAt;congr 1 <;> omega

private def bump (s : MachineState) :=
  execInstrBr (execInstrBr s (.ADDI .x14 .x14 8)) (.ADDI .x17 .x17 (-1))

private theorem bump_info (s : MachineState) (ord left : Nat) (l : 0<left)
    (pc : s.pc=address 809) (idx : s.getReg .x14=indexAt ord) (count : s.getReg .x17=countWord left) :
    (bump s).pc=address 811 ∧ (bump s).getReg .x14=indexAt (ord+1) ∧
    (bump s).getReg .x17=countWord (left-1) ∧ (bump s).mem=s.mem := by
  refine ⟨?_,?_,?_,?_⟩
  · change s.pc+4+4=_;rw [pc];rfl
  · change s.getReg .x14+signExtend12 8=_;rw [idx];exact index_bump ord
  · change s.getReg .x17+signExtend12 (-1)=_;rw [count];exact decremented left l
  · rfl

private theorem back (s : MachineState) (pc : s.pc=address 811) (nz : s.getReg .x17≠0#64) :
    execInstrBr s (.BNE .x17 .x0 7908)=s.setPC (address 740) := by
  have yes : (s.getReg .x17 != s.getReg .x0)=true := by simp [open_zero,nz]
  simp only [execInstrBr,yes,ite_true,pc]
  exact congrArg s.setPC (by decide : address 811+signExtend13 7908=address 740)

private theorem fall (s : MachineState) (pc : s.pc=address 811) (z : s.getReg .x17=0#64) :
    execInstrBr s (.BNE .x17 .x0 7908)=s.setPC (address 812) := by
  simp only [execInstrBr,open_zero,z,beq_self_eq_true,ite_true,pc]
  exact congrArg s.setPC (by decide : address 811+4=address 812)

private theorem exit_jump (s : MachineState) (pc : s.pc=address 812) :
    execInstrBr s (.JAL .x0 2093964)=s.setPC (address 15) := by
  change s.setPC (s.pc+signExtend21 2093964)=_
  rw [pc];exact congrArg s.setPC (by decide : address 812+signExtend21 2093964=address 15)

private def firstMoves : List Row := [(809,.ADDI .x14 .x14 8),(810,.ADDI .x17 .x17 (-1))]
private def lastMoves (last : Bool) : List Row := if last then [(811,.BNE .x17 .x0 7908),(812,.JAL .x0 2093964)]
  else [(811,.BNE .x17 .x0 7908)]

private theorem next_parts (last : Bool) : nextRows last=firstMoves++lastMoves last := by cases last <;> rfl
private theorem first_value (s : MachineState) : walkRows s firstMoves=bump s := rfl
private theorem first_legal (s : MachineState) (pc : s.pc=address 809) : legal firstMoves s := by
  refine ⟨pc,rfl,?_,rfl,trivial⟩
  change s.pc+4=_
  rw [pc];rfl

private theorem last_done (s : MachineState) (pc : s.pc=address 811) (z : s.getReg .x17=0#64) :
    legal (lastMoves true) s ∧ walkRows s (lastMoves true)=s.setPC (address 15) := by
  have first:=fall s pc z
  have atJump:=congrArg MachineState.pc first
  refine ⟨⟨pc,rfl,atJump,rfl,trivial⟩,?_⟩
  simp only [lastMoves,ite_true,walkRows,List.foldl_cons,List.foldl_nil,first,exit_jump _ (show (s.setPC (address 812)).pc=address 812 from rfl)]
  rfl

private theorem last_again (s : MachineState) (pc : s.pc=address 811) (z : s.getReg .x17≠0#64) :
    legal (lastMoves false) s ∧ walkRows s (lastMoves false)=s.setPC (address 740) :=
  ⟨⟨pc,rfl,trivial⟩,back s pc z⟩

private theorem next_value (s : MachineState) (last : Bool) :
    walkRows s (nextRows last)=walkRows (bump s) (lastMoves last) := by
  rw [next_parts,walk_join,first_value]

private theorem next_legal (s : MachineState) (last : Bool) (pc : s.pc=address 809)
    (good : legal (lastMoves last) (bump s)) : legal (nextRows last) s := by
  rw [next_parts];apply legal_append _ _ _ (first_legal s pc);rw [first_value];exact good

attribute [local irreducible] bump walkRows nextRows

theorem next_ok (s : MachineState) (ord left : Nat) (pc : s.pc=address 809) (l : 0<left) (hi : left≤16777216)
    (index : s.getReg .x14=indexAt ord) (counter : s.getReg .x17=countWord left) :
    legal (nextRows (decide (left=1))) s ∧ (advanced s left).pc=finalPC left ∧
      (advanced s left).getReg .x14=indexAt (ord+1) ∧ (advanced s left).getReg .x17=countWord (left-1) ∧
      (advanced s left).mem=s.mem := by
  have br:=bump_info s ord left l pc index counter
  have test : (bump s).getReg .x17=0#64 ↔ left=1 := br.2.2.1 ▸ counter_zero left l hi
  by_cases last : left=1
  · have d:=last_done (bump s) br.1 (test.mpr last)
    rw [decide_eq_true last,advanced,decide_eq_true last,next_value,d.2,finalPC,if_pos last]
    exact ⟨next_legal s true pc d.1,rfl,br.2.1,br.2.2.1,br.2.2.2⟩
  · have d:=last_again (bump s) br.1 (mt test.mp last)
    rw [decide_eq_false last,advanced,decide_eq_false last,next_value,d.2,finalPC,if_neg last]
    exact ⟨next_legal s false pc d.1,rfl,br.2.1,br.2.2.1,br.2.2.2⟩

attribute [local semireducible] walkRows nextRows

private theorem jump_reg (u : MachineState) (r : Reg) (imm : BitVec 21) :
    (execInstrBr u (.JAL .x0 imm)).getReg r=u.getReg r := MachineState.getReg_setPC ..

theorem next_keeps (s : MachineState) (left : Nat) (r : Reg) (a : r≠.x14) (b : r≠.x17) :
    (advanced s left).getReg r=s.getReg r := by
  unfold advanced;apply rows_preserve;intro p h u
  unfold nextRows at h;cases tag : (decide (left=1)) <;>
    simp only [tag,Bool.false_eq_true,ite_false,ite_true,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at h
  · rcases h with h|h|h <;> subst p <;> first | exact bne_reg .. | simp [execInstrBr,Ne.symm a,Ne.symm b]
  · rcases h with h|h|h|h <;> subst p
    all_goals first | exact bne_reg .. | exact jump_reg u r _ |
      simp [execInstrBr,Ne.symm a,Ne.symm b]

/-- A new quartet (either parity): its reply is inverted into its rebuilt block. -/
def inverts (i : Index) (last : Nat) : Bool := decide (i.val/4≠last)

/-- The head's exit state (row 777); `y` is the inverse reply, used only when `inverts i last`. -/
def headed (s : MachineState) (i : Index) (last : Nat) (y : BitVec 1600) : MachineState :=
  if i.val/4=last then walkRows s headRows
  else walkRows (writeBits (walkRows s (preRows (oddOf i))) (wordAddress (rebuiltWord (i.val/4))) y) headPost

/-- The salt rows after the chain (796..812). -/
def finishOne (t : MachineState) (i : Index) (left : Nat) := advanced (copied (choose t i)) left

def inverseQuery (s : MachineState) (i : Index) :=
  packBuffer (window (memoryView (walkRows s (preRows (oddOf i)))) (replyWord (i.val/4)))

def perTrace (s : MachineState) (i : Index) (left last : Nat) : OracleComp World MachineState :=
  if inverts i last then do
    let y ← World.query (.inr (.inr (.inr (inverseQuery s i))))
    let t ← chainTrace (headed s i last y) i
    return finishOne t i left
  else do
    let t ← chainTrace (headed s i last 0) i
    return finishOne t i left

def headSteps (i : Index) (last : Nat) := if i.val/4=last then 3 else if i.val/4%2=1 then 28 else 29
def headCycles (i : Index) (last : Nat) := if i.val/4=last then 3 else if i.val/4%2=1 then 35 else 36
def postSteps (i : Index) (left : Nat) := 12+(if kindOf i=0 then 1 else if kindOf i=1 then 1 else 0)+(if left=1 then 1 else 0)
def perSteps (i : Index) (left last : Nat) := headSteps i last+(chainSteps i+postSteps i left)
def perCalls (i : Index) (last : Nat) := (if inverts i last then 1 else 0)+chainCalls i
def perCycles (i : Index) (left last : Nat) := headCycles i last+(chainCycles i+postSteps i left)

private theorem post_length (k : Fin 3) (last : Bool) :
    (postRows k last).length=12+(if k=0 then 1 else if k=1 then 1 else 0)+(if last then 1 else 0) ∧
    price (postRows k last)=(postRows k last).length := by
  revert k last; decide

private theorem post_steps (i : Index) (left : Nat) :
    (postRows (kindOf i) (decide (left=1))).length=postSteps i left ∧
    price (postRows (kindOf i) (decide (left=1)))=postSteps i left := by
  have pl := post_length (kindOf i) (decide (left=1))
  rw [pl.2,pl.1]; unfold postSteps
  constructor <;> (rcases kind_cases i with ⟨_,k⟩|⟨_,k⟩|⟨_,k⟩ <;> by_cases x : left=1 <;> simp [k,x])

/-- From the chain's exit (row 796): the salt select, the copy and the loop latch. -/
theorem post_run (t : MachineState) (i : Index) (ord left fuel : Nat) (l : 0<left) (hi : left≤16777216)
    (pc : t.pc=address 796) (idx : t.getReg .x6=BitVec.ofNat 64 i.val) (sub : t.getReg .x28=BitVec.ofNat 64 (rank i.val))
    (one : t.getReg .x23=1) (out : t.getReg .x12=1536) (salt : t.getReg .x22=9126809632)
    (index : t.getReg .x14=indexAt ord) (count : t.getReg .x17=countWord left) :
    execute openingImage (postSteps i left+fuel) t true =
      (do let e ← execute openingImage fuel (finishOne t i left) true; return e.charge (postSteps i left) 0) := by
  have chooseOk:=choose_legal t i pc sub one
  obtain ⟨ap,ar,ad⟩:=chosen t i pc idx sub one out salt
  let a:=choose t i
  let b:=copied a
  have keep (k : Reg) (h7 : k≠.x7) (h30 : k≠.x30) (h31 : k≠.x31) : b.getReg k=t.getReg k :=
    (copied_keeps a k h31).trans (choose_keeps t i k h7 h30)
  have nx:=next_ok b ord left (copied_pc a ap) l hi
    ((keep .x14 (by decide) (by decide) (by decide)).trans index)
    ((keep .x17 (by decide) (by decide) (by decide)).trans count)
  have ok : legal (postRows (kindOf i) (decide (left=1))) t := by
    rw [post_parts]
    apply legal_append
    · exact legal_append t _ _ chooseOk (copy_legal a i ap ar ad)
    · simpa only [b,a,copied,choose,walkRows,List.foldl_append] using nx.1
  have ps := post_steps i left
  rw [show postSteps i left+fuel=(postRows (kindOf i) (decide (left=1))).length+fuel by rw [ps.1],
    walk_rows_run t _ ok (post_row_fetch _ _) fuel true, ps.2]
  have same : walkRows t (postRows (kindOf i) (decide (left=1)))=finishOne t i left := by
    rw [post_parts]
    simp only [finishOne,advanced,copied,choose,walkRows,List.foldl_append]
  rw [same]

/-- Registers of the head's exit state, from the entry state. -/
structure HeadExit (s h : MachineState) (i : Index) (ord left : Nat) : Prop where
  entry : ChainEntry h i
  regs : Registers h ord left
  keep : ∀ k, k≠.x4 → k≠.x6 → k≠.x7 → k≠.x10 → k≠.x13 → k≠.x28 → k≠.x30 → k≠.x31 → h.getReg k=s.getReg k
  quartet : h.getReg .x4=BitVec.ofNat 64 (i.val/4)

private theorem exit_of (s h : MachineState) (i : Index) (ord left last : Nat) (r : Input s i ord left last)
    (pc : h.pc=address 777) (idx : h.getReg .x6=BitVec.ofNat 64 i.val) (x10 : h.getReg .x10=1024) (x13 : h.getReg .x13=1)
    (q : h.getReg .x4=BitVec.ofNat 64 (i.val/4))
    (keep : ∀ k, k≠.x4 → k≠.x6 → k≠.x7 → k≠.x10 → k≠.x13 → k≠.x28 → k≠.x30 → k≠.x31 → h.getReg k=s.getReg k) :
    HeadExit s h i ord left := by
  have k (x : Reg) (h4 : x≠.x4 := by decide) (h6 : x≠.x6 := by decide) (h7 : x≠.x7 := by decide)
      (h10 : x≠.x10 := by decide) (h13 : x≠.x13 := by decide) (h28 : x≠.x28 := by decide) (h30 : x≠.x30 := by decide)
      (h31 : x≠.x31 := by decide) := keep x h4 h6 h7 h10 h13 h28 h30 h31
  exact ⟨⟨pc,x10,(k .x12).trans r.output,(k .x5).trans r.selector,(k .x11).trans r.width,x13,(k .x26).trans r.base,
    (k .x29).trans r.divReg,idx⟩,
    ⟨x10,(k .x12).trans r.output,(k .x5).trans r.selector,(k .x11).trans r.width,x13,(k .x14).trans r.index,
     (k .x17).trans r.leftReg,(k .x22).trans r.salt,(k .x26).trans r.base,(k .x29).trans r.divReg⟩,keep,q⟩

theorem head_exit (s : MachineState) (i : Index) (ord left last : Nat) (r : Input s i ord left last) (y : BitVec 1600) :
    HeadExit s (headed s i last y) i ord left := by
  by_cases same : i.val/4=last
  · obtain ⟨_,hpc,_,h6,hkeep⟩ := head_skip s i ord left last r same
    have hd : headed s i last y=walkRows s headRows := by simp [headed,same]
    rw [hd]
    exact exit_of s _ i ord left last r hpc h6 ((hkeep _ (by decide) (by decide)).trans r.input)
      ((hkeep _ (by decide) (by decide)).trans r.primitive) ((hkeep _ (by decide) (by decide)).trans (by rw [r.quartet, same]))
      (fun k _ h6 _ _ _ h28 _ _ => hkeep k h6 h28)
  · obtain ⟨_,apc,_,_,_,_,a30,a6,a28,a4,akeep⟩ := head_pre s i ord left last r same
    let a1:=writeBits (walkRows s (preRows (oddOf i))) (wordAddress (rebuiltWord (i.val/4))) y
    have reg1 (x : Reg) : a1.getReg x=(walkRows s (preRows (oddOf i))).getReg x := writeBits_register ..
    have a1pc : a1.pc=address 762 := by rw [show a1.pc=(walkRows s (preRows (oddOf i))).pc+4 from reply_pc ..,apc]; rfl
    have k (x : Reg) (h4 : x≠.x4 := by decide) (h6 : x≠.x6 := by decide) (h7 : x≠.x7 := by decide)
        (h10 : x≠.x10 := by decide) (h12 : x≠.x12 := by decide) (h13 : x≠.x13 := by decide)
        (h28 : x≠.x28 := by decide) (h30 : x≠.x30 := by decide) : a1.getReg x=s.getReg x :=
      (reg1 x).trans (akeep x h4 h6 h7 h10 h12 h13 h28 h30)
    obtain ⟨_,ppc,p10,p12,p13,pkeep,_⟩ := head_post a1 i a1pc ((reg1 _).trans a28) ((k .x19).trans r.leaves)
      ((k .x9).trans r.heap) ((reg1 _).trans a30)
    have hd : headed s i last y=walkRows a1 headPost := by simp [headed,same,a1]
    rw [hd]
    exact exit_of s _ i ord left last r ppc
      ((pkeep _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((reg1 _).trans a6)) p10 p13
      ((pkeep _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((reg1 _).trans a4))
      (fun x h4 h6 h7 h10 h13 h28 h30 h31 => by
        by_cases h12 : x=.x12
        · subst h12; rw [p12]; exact r.output.symm
        · exact (pkeep x h10 h12 h13 h28 h31).trans (k x h4 h6 h7 h10 h12 h13 h28 h30))

private theorem charge_comm (e : Execution) (a b c d : Nat) :
    (e.charge a c).charge b d=e.charge (b+a) (d+c) := by
  cases e; simp [Execution.charge,Nat.add_assoc]

/-- One position: its head, the chained generator and the salt rows. -/
theorem per_run (s : MachineState) (i : Index) (ord left last fuel : Nat) (l : 0<left) (hi : left≤16777216)
    (r : Input s i ord left last) : execute openingImage (perSteps i left last+fuel) s true =
      (do let t ← perTrace s i left last; let z ← execute openingImage fuel t true
          return z.charge (perCycles i left last) (perCalls i last)) := by
  have tail (h : MachineState) (y : BitVec 1600) (hx : h=headed s i last y) :
      execute openingImage (chainSteps i+(postSteps i left+fuel)) h true =
        (do let t ← chainTrace h i; let e ← execute openingImage fuel (finishOne t i left) true
            return e.charge (chainCycles i+postSteps i left) (chainCalls i)) := by
    have ex := head_exit s i ord left last r y
    rw [← hx] at ex
    rw [chain_run h i ex.entry]
    apply bind_congr_of_forall_mem_support; intro t hit
    obtain ⟨tpc,t10,t28,tkeep,_⟩ := chain_post h i ex.entry t hit
    have tk (x : Reg) (h7 : x≠.x7 := by decide) (h10 : x≠.x10 := by decide) (h28 : x≠.x28 := by decide)
        (h30 : x≠.x30 := by decide) (h31 : x≠.x31 := by decide) := tkeep x h7 h10 h28 h30 h31
    rw [post_run t i ord left fuel l hi tpc ((tk .x6).trans ex.entry.idx) t28
      ((tk .x23).trans ((ex.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)).trans r.one)) ((tk .x12).trans ex.regs.output) ((tk .x22).trans ex.regs.salt)
      ((tk .x14).trans ex.regs.index) ((tk .x17).trans ex.regs.leftReg)]
    simp only [bind_assoc,pure_bind]
    apply bind_congr; intro e; apply congrArg pure; rw [charge_comm]; congr 1 <;> omega
  unfold perSteps perTrace
  by_cases same : i.val/4=last
  · obtain ⟨l1,_,_,_,_⟩ := head_skip s i ord left last r same
    have inv : inverts i last=false := by simp [inverts,same]
    have hs : headSteps i last=headRows.length := by simp [headSteps,same]; rfl
    rw [hs, show headRows.length+(chainSteps i+postSteps i left)+fuel=headRows.length+(chainSteps i+(postSteps i left+fuel)) by omega,
      walk_rows_run s headRows l1 skip_row_fetch _ true,
      tail (walkRows s headRows) 0 (by simp [headed,same])]
    simp only [inv,Bool.false_eq_true,ite_false,bind_assoc,pure_bind]
    have hd : headed s i last 0=walkRows s headRows := by simp [headed,same]
    rw [hd]
    apply bind_congr; intro t; apply bind_congr; intro e; apply congrArg pure
    rw [charge_comm]; congr 1
    · simp [perCycles,headCycles,same,show price headRows=3 from rfl] <;> omega
    · simp [perCalls,inv]
  · have inv : inverts i last=true := by simp [inverts,same]
    obtain ⟨l1,apc,_,a10,a12,a13,a30,_,a28,_,akeep⟩ := head_pre s i ord left last r same
    have hs : headSteps i last=(preRows (oddOf i)).length+(headPost.length+1) := by
      rcases Nat.mod_two_eq_zero_or_one (i.val/4) with h|h <;> simp [headSteps,oddOf,same,h] <;> rfl
    have k (x : Reg) (h4 : x≠.x4 := by decide) (h6 : x≠.x6 := by decide) (h7 : x≠.x7 := by decide)
        (h10 : x≠.x10 := by decide) (h12 : x≠.x12 := by decide) (h13 : x≠.x13 := by decide)
        (h28 : x≠.x28 := by decide) (h30 : x≠.x30 := by decide) := akeep x h4 h6 h7 h10 h12 h13 h28 h30
    have hix : i.val<16777216 := i.isLt
    have src : replyWord (i.val/4)+25≤2^33 := by unfold replyWord blockWord; omega
    have dst : rebuiltWord (i.val/4)+25≤2^33 := by unfold rebuiltWord blockWord; omega
    rw [hs, show (preRows (oddOf i)).length+(headPost.length+1)+(chainSteps i+postSteps i left)+fuel=
      (preRows (oddOf i)).length+((headPost.length+(chainSteps i+(postSteps i left+fuel)))+1) by omega,
      walk_rows_run s _ l1 (pre_row_fetch _) _ true,
      execute_inverse_call openingImage _ (walkRows s (preRows (oddOf i))) true (replyWord (i.val/4))
        (rebuiltWord (i.val/4)) src dst a10 a12 ((k .x5).trans r.selector) ((k .x11).trans r.width) a13
        (inverse_fetch _ apc)]
    simp only [inv,ite_true,bind_assoc,pure_bind]
    apply bind_congr; intro y
    let a1:=writeBits (walkRows s (preRows (oddOf i))) (wordAddress (rebuiltWord (i.val/4))) y
    have reg1 (x : Reg) : a1.getReg x=(walkRows s (preRows (oddOf i))).getReg x := writeBits_register ..
    have a1pc : a1.pc=address 762 := by rw [show a1.pc=(walkRows s (preRows (oddOf i))).pc+4 from reply_pc ..,apc]; rfl
    have al : legal headPost a1 := (head_post a1 i a1pc ((reg1 _).trans a28) ((reg1 _).trans ((k .x19).trans r.leaves))
      ((reg1 _).trans ((k .x9).trans r.heap)) ((reg1 _).trans a30)).1
    have hd : headed s i last y=walkRows a1 headPost := by simp only [headed,if_neg same]; rfl
    rw [walk_rows_run _ headPost al head_post_fetch _ true, tail (walkRows a1 headPost) y hd.symm]
    simp only [bind_assoc,pure_bind]
    rw [hd]
    apply bind_congr; intro t; apply bind_congr; intro e; apply congrArg pure
    rw [charge_comm, charge_comm, charge_comm]; congr 1
    · rcases Nat.mod_two_eq_zero_or_one (i.val/4) with h|h <;>
        simp [perCycles,headCycles,oddOf,same,h,show price (preRows true)=12 from rfl,
          show price (preRows false)=13 from rfl,show price headPost=15 from rfl] <;> omega
    · simp [perCalls,inv] <;> omega

end TwoPermutationPrototype.GroupedOpening
