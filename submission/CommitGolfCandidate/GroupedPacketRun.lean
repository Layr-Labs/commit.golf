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

theorem local_k_eq (n : Nat) : localK (n%4096)=groupK (n/2) := by
  unfold localK groupK pairRank
  have e : n%4096/2%11=n/2%2048%11 := by omega
  dsimp only; rw [e]

private theorem imm_table : ∀ k : Fin 4, ∀ par : Fin 2, ∀ d : Fin 2,
    signExtend12 (BitVec.ofNat 12 (4096-(512*(k.val+1)+72-16*(2*k.val+par.val)))+BitVec.ofNat 12 (8*d.val))=
      -(BitVec.ofNat 64 (8*(60*k.val+73-2*par.val-d.val))) := by
  decide

/-- The copied salt addresses: a2 (= the odd entry − 4 words) plus the copy immediate is the salt's word in the group
head's reply (pairs other than heads and 11m+10). -/
theorem src_address (P n : Nat) (hn : n=2*P ∨ n=2*P+1) (nh : ¬pairHead (P%2048)) (nt : ¬fromRegs (P%2048))
    (d : Fin 2) (limit : P<2^23) :
    wordAddress (msgWord (2*P+1)-4)+signExtend12 (srcImm (n%4096)+BitVec.ofNat 12 (8*d.val))=
      wordAddress (srcWord n+d.val) := by
  have half : n/2=P := by omega
  have lk := local_k_eq n
  rw [half] at lk
  unfold pairHead at nh; unfold fromRegs at nt
  have kpos : 1 ≤ groupK P ∧ groupK P ≤ 4 := by unfold groupK pairRank; split_ifs <;> omega
  have kle : groupK P ≤ P := by unfold groupK pairRank; split_ifs <;> omega
  have ci : copyIndex (n%4096)=2*(groupK P-1)+n%2 := by
    unfold copyIndex groupK pairRank; dsimp only
    rw [show n%4096/2%11=P%2048%11 by omega,show n%4096%2=n%2 by omega]
  have c9 : copyIndex (n%4096) ≠ 9 := by omega
  have t := imm_table ⟨groupK P-1,by omega⟩ ⟨n%2,by omega⟩ d
  simp only [Fin.val_mk] at t
  unfold srcImm srcWord
  rw [lk,ci,show groupK P-1+1=groupK P by omega] at *
  rw [if_neg c9,show 2*(groupK P-1)+n%2=2*(groupK P-1)+n%2 from rfl] at *
  rw [t,word_back _ _ (by unfold msgWord; omega) (by unfold msgWord; omega)]
  unfold replyWord headPair msgWord
  rw [half]
  congr 1
  omega

/-! ## The walk of one pair packet -/

structure PairRegs (s : MachineState) (P : Nat) : Prop where
  msg : s.getReg .x10=wordAddress (msgWord (2*P)-25)
  heap : s.getReg .x20=wordAddress (cursor (2*P))
  stride : s.getReg .x23=4096
  counter : s.getReg .x24=wordAddress (qSalt 0)
  selector : s.getReg .x5=0
  size : s.getReg .x11=200
  primitive : s.getReg .x13=1

def pairFinish (s t : MachineState) (P : Nat) : Prop :=
  t.getReg .x10=wordAddress (msgWord (2*P+2)-25) ∧ t.getReg .x20=wordAddress (cursor (2*P+2)) ∧
  t.getReg .x23=4096 ∧ t.getReg .x24=wordAddress (qSalt 0) ∧
  t.getReg .x5=0 ∧ t.getReg .x11=200 ∧ t.getReg .x13=1 ∧
  t.getReg .x8=s.getReg .x8 ∧ t.getReg .x9=s.getReg .x9 ∧
  t.getReg .x19=s.getReg .x19 ∧ t.getReg .x21=s.getReg .x21 ∧ t.getReg .x25=s.getReg .x25

private theorem word_getReg (s : MachineState) (addr : Nat) (v : Word) (reg : Reg) :
    (putWord s addr v).getReg reg = s.getReg reg := by cases reg <;> rfl

private theorem offset_getReg (s : MachineState) (rd : Reg) (value : Word) (reg : Reg) :
    (putReg s rd value).getReg reg = if rd=reg ∧ reg≠.x0 then value else s.getReg reg := by
  simp only [putReg,MachineState.getReg_setPC]
  cases rd <;> cases reg <;> rfl

theorem cursor_next (i : Nat) :
    (rebase (i%4096) → wordAddress (cursor i)+4096#64=wordAddress (cursor (i+1))) ∧
    (¬rebase (i%4096) → cursor (i+1)=cursor i) := by
  have succ := rebases_succ i
  unfold cursor qSource
  constructor
  · intro h
    rw [if_pos h] at succ
    change wordAddress _+wordAddress 512=_
    rw [←wordAddress_add];congr 1;omega
  · intro h
    rw [if_neg h] at succ
    omega

/-- All address facts of a pair packet, in the literal forms `simp` produces. -/
theorem pair_addrs (P : Nat) (limit : P<2^23) :
    let E := msgWord (2*P)
    let O := msgWord (2*P+1)
    wordAddress (E-25)+signExtend12 256#12=wordAddress (E+7) ∧
    wordAddress (E+7)+signExtend12 3840#12=wordAddress (E-25) ∧
    wordAddress (E+7)+signExtend12 200#12=wordAddress O ∧
    wordAddress O+signExtend12 4064#12=wordAddress (O-4) ∧
    wordAddress O+signExtend12 3976#12=wordAddress (O-15) ∧
    wordAddress (O-15)+signExtend12 144#12=wordAddress (O+3) ∧
    wordAddress (O-15)+signExtend12 152#12=wordAddress (O+4) ∧
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
    back _ 15 _ (by decide) (by omega) (by omega) _ rfl,fwd _ 18 _ (by decide) _ (by omega),fwd _ 19 _ (by decide) _ (by omega),
    back _ 23 _ (by decide) (by omega) (by omega) _ (by omega),back _ 14 _ (by decide) (by omega) (by omega) _ rfl,
    fwd _ 8 _ (by decide) _ rfl,fwd _ 9 _ (by decide) _ rfl,
    back _ 38 _ (by decide) (by omega) (by omega) _ (by omega),fwd _ 45 _ (by decide) _ (by omega)⟩

theorem copy_index_any (n : Nat) : copyIndex n ≤ 9 := by
  unfold copyIndex; dsimp only; split_ifs <;> omega

theorem src_bound (n : Nat) : srcWord n+2 ≤ msgWord (2*(n/2)+1)+64 := by
  have := copy_index_any (n%4096)
  unfold srcWord replyWord headPair groupK pairRank msgWord; split_ifs <;> omega

attribute [local irreducible] wordAddress msgWord cursor srcWord qSalt qLeaf qSource writeBits

theorem pair_walk (s : MachineState) (P : Nat) (limit : P<2^23) (r : PairRegs s P) :
    walk (fun t => pairFinish s t P) (pairPlan P) s := by
  obtain ⟨f1,f2,f3,f4,f5,f6,f6',f7,f8,f9,f10,f11,f12⟩ := pair_addrs P limit
  have h0 : wordAddress (cursor (2*P))+signExtend12 (heapImm (2*(P%2048)))=wordAddress (qLeaf (2*P)) := by
    have := heap_address (2*P); rwa [show (2*P)%4096=2*(P%2048) by omega] at this
  have h1 : wordAddress (cursor (2*P+1))+signExtend12 (heapImm (2*(P%2048)+1))=wordAddress (qLeaf (2*P+1)) := by
    have := heap_address (2*P+1); rwa [show (2*P+1)%4096=2*(P%2048)+1 by omega] at this
  have c0 := cursor_next (2*P)
  have c1 := cursor_next (2*P+1)
  rw [show (2*P)%4096=2*(P%2048) by omega] at c0
  rw [show (2*P+1)%4096=2*(P%2048)+1 by omega] at c1
  have nd := no_double_rebase (P%2048)
  have rbc : (rebase (2*(P%2048)) ∧ ¬rebase (2*(P%2048)+1)) ∨ (¬rebase (2*(P%2048)) ∧ rebase (2*(P%2048)+1)) ∨
      (¬rebase (2*(P%2048)) ∧ ¬rebase (2*(P%2048)+1)) := by
    by_cases a : rebase (2*(P%2048)) <;> by_cases b : rebase (2*(P%2048)+1)
    · exact absurd ⟨a,b⟩ nd
    · exact Or.inl ⟨a,b⟩
    · exact Or.inr (Or.inl ⟨a,b⟩)
    · exact Or.inr (Or.inr ⟨a,b⟩)
  have h1' : ¬rebase (2*(P%2048)) →
      wordAddress (cursor (2*P))+signExtend12 (heapImm (2*(P%2048)+1))=wordAddress (qLeaf (2*P+1)) :=
    fun n => by rw [← c0.2 n]; exact h1
  have c1' : ¬rebase (2*(P%2048)) → rebase (2*(P%2048)+1) →
      wordAddress (cursor (2*P))+4096#64=wordAddress (cursor (2*P+2)) :=
    fun n r => by rw [← c0.2 n]; exact c1.1 r
  have e2 : ¬rebase (2*(P%2048)) → ¬rebase (2*(P%2048)+1) → cursor (2*P+2)=cursor (2*P) :=
    fun n n' => (c1.2 n').trans (c0.2 n)
  have e2' : rebase (2*(P%2048)) → ¬rebase (2*(P%2048)+1) → cursor (2*P+2)=cursor (2*P+1) :=
    fun _ n' => c1.2 n'
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
  · by_cases a : prefetchA (P%2048) <;> by_cases b : P%2048%11=5 <;> rcases rbc with ⟨k0,k1⟩|⟨k0,k1⟩|⟨k0,k1⟩
    all_goals simp [pairPlan,head,a,b,k0,k1,walk,pairFinish,Action.valid,offset_getReg,word_getReg,writeBits_register,
      r.msg,r.heap,r.counter,r.stride,r.selector,r.size,r.primitive,eN]
    all_goals simp only [f1,f2,f3,f4,f5,f6,f6',f7,f8,f9,f10,f11,f12,h0,h1,z,BitVec.add_zero,true_and,and_true,
      k0,k1,c0.1,h1',c1',e2,c1.1,e2']
    all_goals repeat' apply And.intro
    all_goals first | omega | rfl | exact h1' ‹_› | exact c1' ‹_› ‹_› |
      exact congrArg wordAddress (e2' ‹_› ‹_›).symm | exact congrArg wordAddress (e2 ‹_› ‹_›).symm | skip
  · by_cases t : fromRegs (P%2048)
    · rcases rbc with ⟨k0,k1⟩|⟨k0,k1⟩|⟨k0,k1⟩
      all_goals simp [pairPlan,head,t,k0,k1,walk,pairFinish,Action.valid,offset_getReg,word_getReg,writeBits_register,
        r.msg,r.heap,r.counter,r.stride,r.selector,r.size,r.primitive,eN]
      all_goals simp only [f1,f2,f3,f4,f5,f6,f6',f7,f8,f9,f10,f11,f12,h0,h1,z,BitVec.add_zero,true_and,and_true,
        k0,k1,c0.1,h1',c1',e2,c1.1,e2']
      all_goals repeat' apply And.intro
      all_goals first | omega | rfl | exact h1' ‹_› | exact c1' ‹_› ‹_› |
      exact congrArg wordAddress (e2' ‹_› ‹_›).symm | exact congrArg wordAddress (e2 ‹_› ‹_›).symm | skip
    · have src0 : wordAddress (msgWord (2*P+1)-4)+signExtend12 (srcImm (2*(P%2048)))=wordAddress (srcWord (2*P)) := by
        simpa [show (2*P)%4096=2*(P%2048) by omega] using src_address P (2*P) (Or.inl rfl) head t 0 limit
      have src1 := src_address P (2*P) (Or.inl rfl) head t 1 limit
      rw [show (2*P)%4096=2*(P%2048) by omega] at src1
      change wordAddress (msgWord (2*P+1)-4)+signExtend12 (srcImm (2*(P%2048))+8#12)=wordAddress (srcWord (2*P)+1) at src1
      have src2 : wordAddress (msgWord (2*P+1)-4)+signExtend12 (srcImm (2*(P%2048)+1))=wordAddress (srcWord (2*P+1)) := by
        simpa [show (2*P+1)%4096=2*(P%2048)+1 by omega] using src_address P (2*P+1) (Or.inr rfl) head t 0 limit
      have src3 := src_address P (2*P+1) (Or.inr rfl) head t 1 limit
      rw [show (2*P+1)%4096=2*(P%2048)+1 by omega] at src3
      change wordAddress (msgWord (2*P+1)-4)+signExtend12 (srcImm (2*(P%2048)+1)+8#12)=wordAddress (srcWord (2*P+1)+1) at src3
      rcases rbc with ⟨k0,k1⟩|⟨k0,k1⟩|⟨k0,k1⟩
      all_goals simp [pairPlan,head,t,k0,k1,walk,pairFinish,Action.valid,offset_getReg,word_getReg,writeBits_register,
        r.msg,r.heap,r.counter,r.stride,r.selector,r.size,r.primitive,eN]
      all_goals simp only [f1,f2,f3,f4,f5,f6,f6',f7,f8,f9,f10,f11,f12,h0,h1,z,src0,src1,src2,src3,BitVec.add_zero,
        true_and,and_true,k0,k1,c0.1,h1',c1',e2,c1.1,e2']
      all_goals repeat' apply And.intro
      all_goals first | omega | rfl | exact h1' ‹_› | exact c1' ‹_› ‹_› |
      exact congrArg wordAddress (e2' ‹_› ‹_›).symm | exact congrArg wordAddress (e2 ‹_› ‹_›).symm | skip

end TwoPermutationPrototype.Grouped
