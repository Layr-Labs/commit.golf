import CommitGolfCandidate.GroupedPacket

/-! Register walk of one pair packet: every action is valid, and the registers at the end match the next pair. -/

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.QuartetCommit (qSource qSalt qLeaf)
set_option maxRecDepth 24000
set_option maxHeartbeats 4000000

/-- A finite straight-line path certificate includes every possible public reply. -/
def walk (post : MachineState → Prop) : List Action → MachineState → Prop
  | [],s => post s
  | a::rest,s => a.valid s ∧
      match a with
      | .offset rd _ _ target | .add rd _ _ target => walk post rest (putReg s rd (wordAddress target))
      | .load rd _ _ addr => walk post rest (putReg s rd (memoryView s addr))
      | .store _ value _ addr => walk post rest (putWord s addr (s.getReg value))
      | .perm _ dst => ∀ y : BitVec 1600, walk post rest (writeBits s (wordAddress dst) y)

theorem walk_post (post : MachineState → Prop) (ops : List Action) (s : MachineState)
    (h : walk post ops s) : validOps ops s ∧ ∀ t ∈ support (runOps ops s), post t := by
  induction ops generalizing s with
  | nil =>
    refine ⟨trivial,?_⟩
    simpa only [runOps,support_pure,Set.mem_singleton_iff,forall_eq] using (show post s from h)
  | cons a rest ih =>
    have restOk : ∀ t∈support (a.run s),walk post rest t := by
      cases a <;> simp only [Action.run,mem_support_bind_iff,support_pure,Set.mem_singleton_iff,forall_eq]
      all_goals first | exact h.2 | intro t hit;obtain ⟨y,_,rfl⟩ := hit;exact h.2 y
    exact ⟨⟨h.1,fun t hit => (ih t (restOk t hit)).1⟩,fun t hit => by
      rw [runOps,mem_support_bind_iff] at hit
      obtain ⟨st,prior,tail⟩ := hit
      exact (ih st (restOk st prior)).2 t tail⟩

theorem ops_pc (ops : List Action) (s t : MachineState) (hit : t∈support (runOps ops s)) :
    t.pc=s.pc+BitVec.ofNat 64 (4*ops.length) := by
  induction ops generalizing s with
  | nil => simp only [runOps,support_pure,Set.mem_singleton_iff] at hit;subst t;simp
  | cons a rest ih =>
    rw [runOps,mem_support_bind_iff] at hit
    obtain ⟨st,one,tail⟩ := hit
    rw [ih st tail,action_pc a s st one,List.length_cons,Nat.mul_add]
    rw [BitVec.ofNat_add,show BitVec.ofNat 64 (4*1)=4#64 from rfl,BitVec.add_comm (BitVec.ofNat 64 (4*rest.length)),BitVec.add_assoc];rfl

/-! ## Address arithmetic -/

theorem word_fwd (a d : Nat) : wordAddress a+BitVec.ofNat 64 (8*d)=wordAddress (a+d) :=
  (wordAddress_add a d).symm

theorem word_back (a d : Nat) (h : d ≤ a) (small : 8*a<2^64) :
    wordAddress a+-(BitVec.ofNat 64 (8*d))=wordAddress (a-d) := by
  unfold wordAddress
  rw [←BitVec.sub_eq_add_neg,BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]
  congr 1; omega

theorem pair_head_iff (P : Nat) : pairHead (P%2048) ↔ groupK P=0 := by
  unfold pairHead groupK pairRank; split_ifs <;> omega

theorem copy_index_le (n : Nat) (h : ¬pairHead ((n/2)%2048)) (hn : n<4096) : copyIndex n ≤ 9 := by
  unfold copyIndex; unfold pairHead at h; dsimp only; split_ifs <;> omega

private theorem imm_table : ∀ c : Fin 9, ∀ d : Fin 2,
    signExtend12 (BitVec.ofNat 12 (416+16*c.val)+BitVec.ofNat 12 (8*d.val))=BitVec.ofNat 64 (8*(52+2*c.val+d.val)) := by
  decide

private theorem imm_borrow : ∀ d : Fin 2,
    signExtend12 (BitVec.ofNat 12 2080+BitVec.ofNat 12 (8*d.val))=-(BitVec.ofNat 64 (8*(252-d.val))) := by
  decide

theorem head_pair_ge (P : Nat) (h : copyIndex ((2*P)%4096)=9 ∨ copyIndex ((2*P+1)%4096)=9) : 5 ≤ headPair P := by
  unfold headPair groupK pairRank; unfold copyIndex at h; dsimp only at h; split_ifs at h ⊢ <;> omega

/-- The copied salt addresses: t2 plus the copy immediate is the salt's word in a head's reply. -/
theorem src_address (P n : Nat) (hn : n=2*P ∨ n=2*P+1) (nh : ¬pairHead (P%2048)) (d : Fin 2) (limit : P<2^23) :
    wordAddress (anchorWord P)+signExtend12 (srcImm (n%4096)+BitVec.ofNat 12 (8*d.val))=wordAddress (srcWord n+d.val) := by
  have half : n/2=P := by omega
  have nh' : ¬pairHead ((n%4096/2)%2048) := by rwa [show (n%4096/2)%2048=P%2048 by omega]
  have cle := copy_index_le (n%4096) nh' (by omega)
  have hk : groupK P ≠ 0 := fun z => nh ((pair_head_iff P).mpr z)
  have kle : groupK P ≤ P := by unfold groupK pairRank; split_ifs <;> omega
  unfold srcImm srcWord anchorWord
  rw [half]
  by_cases nine : copyIndex (n%4096)=9
  · rw [if_pos nine,if_pos nine,imm_borrow d]
    have ge : 5 ≤ headPair P := head_pair_ge P (by rcases hn with rfl|rfl <;> simp_all)
    unfold replyWord msgWord at *
    rw [word_back _ _ (by omega) (by unfold headPair at *; omega)]
    congr 1; omega
  · rw [if_neg nine,if_neg nine]
    have c8 : copyIndex (n%4096) ≤ 8 := by omega
    have t := imm_table ⟨copyIndex (n%4096),by omega⟩ d
    simp only [Fin.val_mk] at t
    rw [t,word_fwd]
    unfold replyWord msgWord
    congr 1
    unfold headPair at *
    omega

/-! ## The walk of one pair packet -/

structure PairRegs (s : MachineState) (P : Nat) : Prop where
  msg : s.getReg .x10=wordAddress (msgWord (2*P)-25)
  heap : s.getReg .x20=wordAddress (cursor (2*P))
  stride : s.getReg .x23=4096
  counter : s.getReg .x24=wordAddress (qSalt 0)
  anchor : ¬pairHead (P%2048) → s.getReg .x7=wordAddress (anchorWord P)
  selector : s.getReg .x5=0
  size : s.getReg .x11=200
  primitive : s.getReg .x13=1

def pairFinish (s t : MachineState) (P : Nat) : Prop :=
  t.getReg .x10=wordAddress (msgWord (2*P+2)-25) ∧ t.getReg .x20=wordAddress (cursor (2*P+2)) ∧
  t.getReg .x23=4096 ∧ t.getReg .x24=wordAddress (qSalt 0) ∧
  t.getReg .x7=wordAddress (anchorWord P) ∧
  t.getReg .x5=0 ∧ t.getReg .x11=200 ∧ t.getReg .x13=1 ∧
  t.getReg .x8=s.getReg .x8 ∧ t.getReg .x9=s.getReg .x9 ∧
  t.getReg .x19=s.getReg .x19 ∧ t.getReg .x21=s.getReg .x21 ∧ t.getReg .x25=s.getReg .x25

private theorem word_getReg (s : MachineState) (addr : Nat) (v : Word) (reg : Reg) :
    (putWord s addr v).getReg reg = s.getReg reg := by cases reg <;> rfl

private theorem offset_getReg (s : MachineState) (rd : Reg) (value : Word) (reg : Reg) :
    (putReg s rd value).getReg reg = if rd=reg ∧ reg≠.x0 then value else s.getReg reg := by
  simp only [putReg,MachineState.getReg_setPC]
  cases rd <;> cases reg <;> rfl

theorem anchor_head (P : Nat) (h : pairHead (P%2048)) : anchorWord P=msgWord (2*P+1)-65 := by
  have z := (pair_head_iff P).mp h
  unfold anchorWord replyWord headPair; rw [z]; unfold msgWord; omega

theorem cursor_pair (P : Nat) :
    (P%2048%16=15 → wordAddress (cursor (2*P))+4096=wordAddress (cursor (2*P+2))) ∧
    (P%2048%16≠15 → cursor (2*P+2)=cursor (2*P)) := by
  unfold cursor qSource
  constructor
  · intro h
    change wordAddress _+wordAddress 512=_
    rw [←wordAddress_add];congr 1;omega
  · intro h;congr 1;omega

/-- All address facts of a pair packet, in the literal forms `simp` produces. -/
theorem pair_addrs (P : Nat) (limit : P<2^23) :
    let E := msgWord (2*P)
    let O := msgWord (2*P+1)
    wordAddress (E-25)+signExtend12 256#12=wordAddress (E+7) ∧
    wordAddress (E+7)+signExtend12 3840#12=wordAddress (E-25) ∧
    wordAddress (E+7)+signExtend12 200#12=wordAddress O ∧
    wordAddress O+signExtend12 4064#12=wordAddress (O-4) ∧
    wordAddress O+signExtend12 3976#12=wordAddress (O-15) ∧
    wordAddress (O-15)+signExtend12 3696#12=wordAddress (O-65) ∧
    wordAddress (O-15)+signExtend12 3912#12=wordAddress (E-6) ∧
    wordAddress O+signExtend12 3984#12=wordAddress (O-14) ∧
    wordAddress O+signExtend12 64#12=wordAddress (O+8) ∧
    wordAddress O+signExtend12 72#12=wordAddress (O+9) ∧
    wordAddress O+signExtend12 3792#12=wordAddress (E-6) ∧
    wordAddress (E-6)+signExtend12 360#12=wordAddress (O+7) := by
  intro E O
  have eE : E=512+64*P := by simp only [E,msgWord]; omega
  have eO : O=544+64*P := by simp only [O,msgWord]; omega
  have big : 8*(O+32)<2^64 := by omega
  have back (a d : Nat) (imm : BitVec 12) (h : signExtend12 imm=-(BitVec.ofNat 64 (8*d))) (le : d ≤ a)
      (sm : 8*a<2^64) (b : Nat) (eq : a-d=b) : wordAddress a+signExtend12 imm=wordAddress b := by
    rw [h,word_back a d le sm,eq]
  have fwd (a d : Nat) (imm : BitVec 12) (h : signExtend12 imm=BitVec.ofNat 64 (8*d)) (b : Nat) (eq : a+d=b) :
      wordAddress a+signExtend12 imm=wordAddress b := by
    rw [h,word_fwd,eq]
  refine ⟨fwd _ 32 _ (by decide) _ (by omega),back _ 32 _ (by decide) (by omega) (by omega) _ (by omega),
    fwd _ 25 _ (by decide) _ (by omega),back _ 4 _ (by decide) (by omega) (by omega) _ rfl,
    back _ 15 _ (by decide) (by omega) (by omega) _ rfl,back _ 50 _ (by decide) (by omega) (by omega) _ (by omega),
    back _ 23 _ (by decide) (by omega) (by omega) _ (by omega),back _ 14 _ (by decide) (by omega) (by omega) _ rfl,
    fwd _ 8 _ (by decide) _ rfl,fwd _ 9 _ (by decide) _ rfl,
    back _ 38 _ (by decide) (by omega) (by omega) _ (by omega),fwd _ 45 _ (by decide) _ (by omega)⟩

theorem copy_index_any (n : Nat) : copyIndex n ≤ 9 := by
  unfold copyIndex; dsimp only; split_ifs <;> omega

theorem src_bound (n : Nat) : srcWord n+2 ≤ msgWord (2*(n/2)+1)+64 := by
  have := copy_index_any (n%4096)
  unfold srcWord replyWord headPair groupK pairRank msgWord; split_ifs <;> omega

attribute [local irreducible] wordAddress msgWord cursor anchorWord srcWord qSalt qLeaf qSource writeBits

theorem pair_walk (s : MachineState) (P : Nat) (limit : P<2^23) (r : PairRegs s P) :
    walk (fun t => pairFinish s t P) (pairPlan P) s := by
  obtain ⟨f1,f2,f3,f4,f5,f6,f7,f8,f9,f10,f11,f12⟩ := pair_addrs P limit
  have h0 : wordAddress (cursor (2*P))+signExtend12 (heapImm (2*(P%2048)))=wordAddress (qLeaf (2*P)) := by
    have := heap_address (2*P); rwa [show (2*P)%4096=2*(P%2048) by omega] at this
  have h1 : wordAddress (cursor (2*P))+signExtend12 (heapImm (2*(P%2048)+1))=wordAddress (qLeaf (2*P+1)) := by
    have := heap_address (2*P+1)
    rwa [show (2*P+1)%4096=2*(P%2048)+1 by omega,show cursor (2*P+1)=cursor (2*P) by unfold cursor; congr 2; omega] at this
  have c := cursor_pair P
  simp only [show P%2048%16=P%16 by omega] at c
  have z : signExtend12 0#12=0#64 := rfl
  have eE : msgWord (2*P)=512+64*P := by unfold msgWord; omega
  have eO : msgWord (2*P+1)=544+64*P := by unfold msgWord; omega
  have eN : msgWord (2*P+2)-25=msgWord (2*P+1)+7 := by unfold msgWord; omega
  have bQ0 : qLeaf (2*P)+25 ≤ 2^33 := by unfold qLeaf qSource; omega
  have bQ1 : qLeaf (2*P+1)+25 ≤ 2^33 := by unfold qLeaf qSource; omega
  have bS : qSalt 0+25 ≤ 2^33 := by unfold qSalt; decide
  have bW0 := src_bound (2*P)
  have bW1 := src_bound (2*P+1)
  rw [show (2*P)/2=P by omega] at bW0
  rw [show (2*P+1)/2=P by omega] at bW1
  by_cases head : pairHead (P%2048)
  · have aw := anchor_head P head
    by_cases k : P%16=15
    all_goals simp [pairPlan,head,k,walk,pairFinish,Action.valid,offset_getReg,word_getReg,writeBits_register,
      r.msg,r.heap,r.counter,r.stride,r.selector,r.size,r.primitive,c.2,eN,aw,show P%2048%16=P%16 by omega]
    all_goals simp only [f1,f2,f3,f4,f5,f6,f7,f8,f9,f10,f11,f12,h0,h1,z,BitVec.add_zero,true_and,and_true]
    all_goals try rw [show wordAddress (cursor (2*P))+4096#64=wordAddress (cursor (2*P+2)) from c.1 k]
    all_goals repeat' apply And.intro
    all_goals first | omega | rfl | skip
  · have src0 : wordAddress (anchorWord P)+signExtend12 (srcImm (2*(P%2048)))=wordAddress (srcWord (2*P)) := by
      simpa [show (2*P)%4096=2*(P%2048) by omega] using src_address P (2*P) (Or.inl rfl) head 0 limit
    have src1 := src_address P (2*P) (Or.inl rfl) head 1 limit
    rw [show (2*P)%4096=2*(P%2048) by omega] at src1
    change wordAddress (anchorWord P)+signExtend12 (srcImm (2*(P%2048))+8#12)=wordAddress (srcWord (2*P)+1) at src1
    have src2 : wordAddress (anchorWord P)+signExtend12 (srcImm (2*(P%2048)+1))=wordAddress (srcWord (2*P+1)) := by
      simpa [show (2*P+1)%4096=2*(P%2048)+1 by omega] using src_address P (2*P+1) (Or.inr rfl) head 0 limit
    have src3 := src_address P (2*P+1) (Or.inr rfl) head 1 limit
    rw [show (2*P+1)%4096=2*(P%2048)+1 by omega] at src3
    change wordAddress (anchorWord P)+signExtend12 (srcImm (2*(P%2048)+1)+8#12)=wordAddress (srcWord (2*P+1)+1) at src3
    by_cases k : P%16=15
    all_goals simp [pairPlan,head,k,walk,pairFinish,Action.valid,offset_getReg,word_getReg,writeBits_register,
      r.msg,r.heap,r.counter,r.stride,r.selector,r.size,r.primitive,r.anchor head,c.2,eN,show P%2048%16=P%16 by omega]
    all_goals simp only [f1,f2,f3,f4,f5,f6,f7,f8,f9,f10,f11,f12,h0,h1,z,src0,src1,src2,src3,BitVec.add_zero,
      true_and,and_true]
    all_goals try rw [show wordAddress (cursor (2*P))+4096#64=wordAddress (cursor (2*P+2)) from c.1 k]
    all_goals repeat' apply And.intro
    all_goals first | omega | rfl | skip

end TwoPermutationPrototype.Grouped
