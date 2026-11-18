import CommitGolfCandidate.GroupedPacket

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.QuartetCommit (qSource qSalt qLeaf)
set_option maxRecDepth 24000
set_option maxHeartbeats 3000000

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

def finish (s t : MachineState) (i : Nat) : Prop :=
  t.getReg .x10=wordAddress (entryWord (i+1)) ∧ t.getReg .x20=s.getReg .x20 ∧
  t.getReg .x23=s.getReg .x23 ∧ t.getReg .x24=wordAddress (qSalt 0) ∧
  t.getReg .x5=0 ∧ t.getReg .x11=200 ∧ t.getReg .x13=1 ∧
  t.getReg .x8=s.getReg .x8 ∧ t.getReg .x9=s.getReg .x9 ∧
  t.getReg .x19=s.getReg .x19 ∧ t.getReg .x21=s.getReg .x21 ∧ t.getReg .x25=s.getReg .x25 ∧
  t.getReg .x26=s.getReg .x26 ∧ t.getReg .x27=s.getReg .x27 ∧ t.getReg .x28=s.getReg .x28 ∧
  t.getReg .x29=s.getReg .x29 ∧ t.getReg .x30=s.getReg .x30 ∧ t.getReg .x6=s.getReg .x6 ∧
  t.getReg .x1=s.getReg .x1 ∧ t.getReg .x2=s.getReg .x2 ∧ t.getReg .x3=s.getReg .x3

theorem word_getReg (s : MachineState) (addr : Nat) (v : Word) (reg : Reg) :
    (putWord s addr v).getReg reg = s.getReg reg := by cases reg <;> rfl

theorem offset_getReg (s : MachineState) (rd : Reg) (value : Word) (reg : Reg) :
    (putReg s rd value).getReg reg = if rd=reg ∧ reg≠.x0 then value else s.getReg reg := by
  simp only [putReg,MachineState.getReg_setPC]
  cases rd <;> cases reg <;> rfl

theorem entry_head (i : Nat) (h : rank i≤1) : entryWord i=msgWord i+7 := by
  unfold entryWord;rw [if_pos h]

theorem entry_follower (i : Nat) (h0 : rank i≠0) (h1 : rank i≠1) : entryWord i=msgWord i := by
  unfold entryWord;rw [if_neg (show ¬rank i≤1 by omega)]

theorem imm_facts :
    signExtend12 3840#12+wordAddress 32=0 ∧ signExtend12 200#12=wordAddress 25 ∧
    signExtend12 4064#12+wordAddress 4=0 ∧ signExtend12 4000#12+wordAddress 12=0 ∧
    signExtend12 3912#12+wordAddress 23=0 ∧ signExtend12 16#12=wordAddress 2 ∧
    signExtend12 368#12=wordAddress 46 ∧ signExtend12 56#12=wordAddress 7 ∧ signExtend12 8#12=wordAddress 1 ∧
    signExtend12 2248#12+wordAddress 231=0 ∧ signExtend12 2256#12+wordAddress 230=0 ∧
    signExtend12 2264#12+wordAddress 229=0 ∧ signExtend12 2272#12+wordAddress 228=0 := by decide

theorem source_bounds (i : Nat) (limit : i<16777216) : sourceWord i+2≤2^33 ∧ genWord i+20≤2^33 := by
  unfold sourceWord genWord msgWord rank;constructor <;> omega

theorem salt_addresses (i : Nat) (h0 : rank i≠0) (h1 : rank i≠1) (h8 : rank i≤8) :
    wordAddress (msgWord i+7)+signExtend12 (saltImm (rank i))=wordAddress (sourceWord i) ∧
    wordAddress (msgWord i+7)+signExtend12 (saltImm (rank i)+8#12)=wordAddress (sourceWord i+1) := by
  have v := salt_imm_value ⟨rank i,rank_lt i⟩ (show 2≤rank i by omega) h8
  change signExtend12 (saltImm (rank i))+wordAddress (30*rank i-7)=0 ∧
    signExtend12 (saltImm (rank i)+8)+wordAddress (30*rank i-8)=0 at v
  have g := genWord_rank i (rank i) rfl
  have big : 30*rank i-7≤msgWord i+7 := by unfold msgWord rank at *;omega
  have big' : 30*rank i-8≤msgWord i+7 := by omega
  refine ⟨(addr_back _ _ _ v.1 big).trans ?_,(addr_back _ _ _ v.2 big').trans ?_⟩
  · unfold sourceWord;congr 1;omega
  · unfold sourceWord;congr 1;omega

theorem prefetch_addresses (i : Nat) (h : rank i=8) :
    wordAddress (msgWord i+7)+signExtend12 2248#12=wordAddress (genWord i+16) ∧
    wordAddress (msgWord i+7)+signExtend12 2256#12=wordAddress (genWord i+17) ∧
    wordAddress (msgWord i+7)+signExtend12 2264#12=wordAddress (genWord i+18) ∧
    wordAddress (msgWord i+7)+signExtend12 2272#12=wordAddress (genWord i+19) := by
  have g := genWord_rank i 8 h
  have low : 512≤msgWord i := by unfold msgWord;omega
  refine ⟨(addr_back _ 231 _ imm_facts.2.2.2.2.2.2.2.2.2.1 (by omega)).trans ?_,(addr_back _ 230 _ imm_facts.2.2.2.2.2.2.2.2.2.2.1 (by omega)).trans ?_,
    (addr_back _ 229 _ imm_facts.2.2.2.2.2.2.2.2.2.2.2.1 (by omega)).trans ?_,(addr_back _ 228 _ imm_facts.2.2.2.2.2.2.2.2.2.2.2.2 (by omega)).trans ?_⟩
  all_goals congr 1;omega

theorem rreg_x14 (n : Nat) : (Reg.x14=rreg n)=False := eq_false (by unfold rreg;split <;> decide)
theorem rreg_x15 (n : Nat) : (Reg.x15=rreg n)=False := eq_false (by unfold rreg;split <;> decide)
theorem rreg_x16 (n : Nat) : (Reg.x16=rreg n)=False := eq_false (by unfold rreg;split <;> decide)
theorem rreg_x17 (n : Nat) : (Reg.x17=rreg n)=False := eq_false (by unfold rreg;split <;> decide)
theorem rreg_x31 (n : Nat) : (Reg.x31=rreg n)=False := eq_false (by unfold rreg;split <;> decide)

theorem tail_facts (i : Nat) (limit : i<16777216) :
    qSource (i/4)+25≤2^33 ∧ qLeaf i+25≤2^33 ∧ 82≤qSource (i/4) := by
  unfold qLeaf qSource;omega

attribute [local irreducible] wordAddress msgWord slotGap aGap genWord sourceWord entryWord qSalt qLeaf qSource writeBits
  saltImm trail rGap

/-- Restore facts in both the `+ -x` and the `- x` forms `simp` may produce. -/
theorem restore_forms (i : Nat) (t : i%4=3) (s : MachineState) (r : PacketRegs s i) :
    wordAddress (qSource (i/4))+s.getReg (rreg (i%4096))=wordAddress (entryWord (i+1)) := by
  have e := restore_address i t
  have g : s.getReg (rreg (i%4096))=-wordAddress (rGap (i%4096)) := by
    unfold rreg rGap
    cases near (i%4096)
    · simp [r.far]
    · simp [r.close]
  rw [g];exact e

theorem walk_head (s : MachineState) (i : Nat) (limit : i<16777216) (r : PacketRegs s i) (h : rank i=0) :
    walk (fun t => finish s t i) (plan i) s := by
  have x10 : s.getReg .x10=wordAddress (msgWord i+7) := by rw [r.msg,entry_head i (by omega)]
  have low : 512≤msgWord i := by unfold msgWord;omega
  have boundM : msgWord i+64≤2^33 := by unfold msgWord;omega
  have boundQ : qLeaf i+25≤2^33 := by unfold qLeaf qSource;omega
  have ctrRoom : qSalt 0+25≤2^33 := by unfold qSalt;decide
  have tf := tail_facts i limit
  have h0 := a_slot_address i
  have m4 : i%4096%4=i%4 := by omega
  have q : i%4=0 ∨ i%4=1 ∨ i%4=2 ∨ i%4=3 := by omega
  have a1 := addr_back (msgWord i+7) 32 3840#12 imm_facts.1 (by omega)
  have a2 := addr_fwd (msgWord i+7) 25 200#12 imm_facts.2.1
  have a3 := addr_back (msgWord i+7+25) 4 4064#12 imm_facts.2.2.1 (by omega)
  have a4 := addr_back (msgWord i+7+25-4) 12 4000#12 imm_facts.2.2.2.1 (by omega)
  have a5 := addr_back (msgWord i+7+25-4-12) 23 3912#12 imm_facts.2.2.2.2.1 (by omega)
  have a6 := addr_fwd (msgWord i+7+25-4-12-23) 2 16#12 imm_facts.2.2.2.2.2.1
  rw [show msgWord i+7-32=msgWord i-25 by omega] at a1
  rw [show msgWord i+7+25=msgWord i+32 by omega] at a2 a3 a4 a5 a6
  rw [show msgWord i+32-4=msgWord i+28 by omega] at a3 a4 a5 a6
  rw [show msgWord i+28-12=msgWord i+16 by omega] at a4 a5 a6
  rw [show msgWord i+16-23=msgWord i-7 by omega] at a5 a6
  rw [show msgWord i-7+2=msgWord i-5 by omega] at a6
  have z : signExtend12 0#12=0#64 := rfl
  have th := trail_head i h
  have oo := odd_output i
  have nz : rank i≠1 := by omega
  have cs : ¬keyed (i%4096) → wordAddress (msgWord i+28)+-wordAddress 364=wordAddress (genWord (i-11)) :=
    chain_source i h
  have cs' : ¬keyed (i%4096) → wordAddress (msgWord i+28)-wordAddress 364=wordAddress (genWord (i-11)) :=
    fun k => by rw [BitVec.sub_eq_add_neg];exact cs k
  have gb : genWord (i-11)+25≤2^33 := by unfold genWord msgWord;omega
  by_cases kd : keyed (i%4096) <;> rcases q with q|q|q|q
  all_goals first
    | (have gi := group_input i q
       have rs := restore_forms i q s r
       rw [q] at h0
       by_cases e : i%4096/4%2=0
       all_goals simp [plan,bodyPlan,tailPlan,eq_true h,eq_false nz,kd,e,walk,finish,Action.valid,offset_getReg,
         word_getReg,writeBits_register,x10,r.counter,r.a0,r.a1,r.a2,r.a3,r.link,areg,m4,q,r.selector,r.size,r.primitive,
         h0,a1,a2,a3,a4,a5,a6,z,cs,cs',gi,oo,rs,rreg_x10,rreg_x12,rreg_x14,rreg_x15,rreg_x16,rreg_x17,rreg_x31]
       all_goals omega)
    | (rw [q] at h0
       simp [plan,bodyPlan,tailPlan,eq_true h,eq_false nz,kd,walk,finish,Action.valid,offset_getReg,word_getReg,
         writeBits_register,x10,r.counter,r.a0,r.a1,r.a2,r.a3,r.link,areg,m4,q,r.selector,r.size,r.primitive,
         h0,a1,a2,a3,a4,a5,a6,z,cs,cs',th]
       all_goals omega)

theorem walk_c (s : MachineState) (i : Nat) (limit : i<16777216) (r : PacketRegs s i) (h : rank i=1) :
    walk (fun t => finish s t i) (plan i) s := by
  have x10 : s.getReg .x10=wordAddress (msgWord i+7) := by rw [r.msg,entry_head i (by omega)]
  have low : 512≤msgWord i := by unfold msgWord;omega
  have boundM : msgWord i+64≤2^33 := by unfold msgWord;omega
  have boundQ : qLeaf i+25≤2^33 := by unfold qLeaf qSource;omega
  have tf := tail_facts i limit
  have h0 := slot_address i
  have m4 : i%4096%4=i%4 := by omega
  have q : i%4=0 ∨ i%4=1 ∨ i%4=2 ∨ i%4=3 := by omega
  have c2 := addr_fwd (msgWord i+7) 2 16#12 imm_facts.2.2.2.2.2.1
  have tr := trail_address i (by omega)
  have oo := odd_output i
  have nz : rank i≠0 := by omega
  rcases q with q|q|q|q
  · rw [q] at h0
    simp [plan,bodyPlan,tailPlan,eq_true h,eq_false nz,walk,finish,Action.valid,offset_getReg,word_getReg,
      writeBits_register,x10,r.counter,r.s0,r.s1,r.s2,r.s3,sreg,m4,q,r.selector,r.size,r.primitive,h0,c2,tr]
    all_goals omega
  · rw [q] at h0
    simp [plan,bodyPlan,tailPlan,eq_true h,eq_false nz,walk,finish,Action.valid,offset_getReg,word_getReg,
      writeBits_register,x10,r.counter,r.s0,r.s1,r.s2,r.s3,sreg,m4,q,r.selector,r.size,r.primitive,h0,c2,tr]
    all_goals omega
  · rw [q] at h0
    simp [plan,bodyPlan,tailPlan,eq_true h,eq_false nz,walk,finish,Action.valid,offset_getReg,word_getReg,
      writeBits_register,x10,r.counter,r.s0,r.s1,r.s2,r.s3,sreg,m4,q,r.selector,r.size,r.primitive,h0,c2,tr]
    all_goals omega
  · have gi := group_input i q
    have rs := restore_forms i q s r
    rw [q] at h0
    by_cases e : i%4096/4%2=0
    · simp [plan,bodyPlan,tailPlan,eq_true h,eq_false nz,eq_true e,walk,finish,Action.valid,offset_getReg,word_getReg,
        writeBits_register,x10,r.counter,r.s0,r.s1,r.s2,r.s3,sreg,m4,q,r.selector,r.size,r.primitive,h0,c2,gi,rs,rreg_x10,rreg_x12,rreg_x14,rreg_x15,rreg_x16,rreg_x17,rreg_x31]
      all_goals omega
    · simp [plan,bodyPlan,tailPlan,eq_true h,eq_false nz,eq_false e,walk,finish,Action.valid,offset_getReg,word_getReg,
        writeBits_register,x10,r.counter,r.s0,r.s1,r.s2,r.s3,sreg,m4,q,r.selector,r.size,r.primitive,h0,c2,gi,oo,rs,rreg_x10,rreg_x12,rreg_x14,rreg_x15,rreg_x16,rreg_x17,rreg_x31]
      all_goals omega

/-- The follower body under its salt variant; `extra` are the salt-plan address facts. -/
theorem walk_follower (s : MachineState) (i : Nat) (limit : i<16777216) (r : PacketRegs s i)
    (h0 : rank i≠0) (h1 : rank i≠1) : walk (fun t => finish s t i) (plan i) s := by
  have x10 : s.getReg .x10=wordAddress (msgWord i) := by rw [r.msg,entry_follower i h0 h1]
  have low : 512≤msgWord i := by unfold msgWord;omega
  have boundM : msgWord i+64≤2^33 := by unfold msgWord;omega
  have boundQ : qLeaf i+25≤2^33 := by unfold qLeaf qSource;omega
  have tf := tail_facts i limit
  have sb := source_bounds i limit
  have h0' := slot_address i
  have m4 : i%4096%4=i%4 := by omega
  have q : i%4=0 ∨ i%4=1 ∨ i%4=2 ∨ i%4=3 := by omega
  have f1 := addr_back (msgWord i) 4 4064#12 imm_facts.2.2.1 (by omega)
  have f2 := addr_fwd (msgWord i) 7 56#12 imm_facts.2.2.2.2.2.2.2.1
  have c2 := addr_fwd (msgWord i+7) 2 16#12 imm_facts.2.2.2.2.2.1
  have f8 := addr_fwd (msgWord i+7) 1 8#12 imm_facts.2.2.2.2.2.2.2.2.1
  rw [show msgWord i+7+1=msgWord i+8 by omega] at f8
  have z : signExtend12 0#12=0#64 := rfl
  have tr := trail_address i h0
  have oo := odd_output i
  have hr := rank_lt i
  have salt : (rank i≤8 → wordAddress (msgWord i+7)+signExtend12 (saltImm (rank i))=wordAddress (sourceWord i) ∧
      wordAddress (msgWord i+7)+signExtend12 (saltImm (rank i)+8#12)=wordAddress (sourceWord i+1)) :=
    fun r8 => salt_addresses i h0 h1 r8
  have pre : (rank i=8 → wordAddress (msgWord i+7)+signExtend12 2248#12=wordAddress (genWord i+16) ∧
      wordAddress (msgWord i+7)+signExtend12 2256#12=wordAddress (genWord i+17) ∧
      wordAddress (msgWord i+7)+signExtend12 2264#12=wordAddress (genWord i+18) ∧
      wordAddress (msgWord i+7)+signExtend12 2272#12=wordAddress (genWord i+19)) :=
    fun e8 => prefetch_addresses i e8
  by_cases r8 : rank i≤8
  · obtain ⟨sa1,sa2⟩ := salt r8
    by_cases e8 : rank i=8
    · obtain ⟨p1,p2,p3,p4⟩ := pre e8
      rcases q with q|q|q|q
      · rw [q] at h0'
        simp [plan,bodyPlan,tailPlan,saltPlan,eq_false h0,eq_false h1,eq_true r8,eq_true e8,walk,finish,
          Action.valid,offset_getReg,word_getReg,writeBits_register,x10,r.counter,r.s0,r.s1,r.s2,r.s3,sreg,m4,q,
          r.selector,r.size,r.primitive,h0',f1,f2,c2,f8,z,sa1,sa2,p1,p2,p3,p4,tr]
        all_goals omega
      · rw [q] at h0'
        simp [plan,bodyPlan,tailPlan,saltPlan,eq_false h0,eq_false h1,eq_true r8,eq_true e8,walk,finish,
          Action.valid,offset_getReg,word_getReg,writeBits_register,x10,r.counter,r.s0,r.s1,r.s2,r.s3,sreg,m4,q,
          r.selector,r.size,r.primitive,h0',f1,f2,c2,f8,z,sa1,sa2,p1,p2,p3,p4,tr]
        all_goals omega
      · rw [q] at h0'
        simp [plan,bodyPlan,tailPlan,saltPlan,eq_false h0,eq_false h1,eq_true r8,eq_true e8,walk,finish,
          Action.valid,offset_getReg,word_getReg,writeBits_register,x10,r.counter,r.s0,r.s1,r.s2,r.s3,sreg,m4,q,
          r.selector,r.size,r.primitive,h0',f1,f2,c2,f8,z,sa1,sa2,p1,p2,p3,p4,tr]
        all_goals omega
      · have gi := group_input i q
        have rs := restore_forms i q s r
        rw [q] at h0'
        by_cases e : i%4096/4%2=0
        all_goals simp [plan,bodyPlan,tailPlan,saltPlan,eq_false h0,eq_false h1,eq_true r8,eq_true e8,e,walk,finish,
          Action.valid,offset_getReg,word_getReg,writeBits_register,x10,r.counter,r.s0,r.s1,r.s2,r.s3,sreg,m4,q,
          r.selector,r.size,r.primitive,h0',f1,f2,c2,f8,z,sa1,sa2,p1,p2,p3,p4,gi,oo,rs,rreg_x10,rreg_x12,rreg_x14,rreg_x15,rreg_x16,rreg_x17,rreg_x31]
        all_goals omega
    · rcases q with q|q|q|q
      · rw [q] at h0'
        simp [plan,bodyPlan,tailPlan,saltPlan,eq_false h0,eq_false h1,eq_true r8,eq_false e8,walk,finish,
          Action.valid,offset_getReg,word_getReg,writeBits_register,x10,r.counter,r.s0,r.s1,r.s2,r.s3,sreg,m4,q,
          r.selector,r.size,r.primitive,h0',f1,f2,c2,f8,z,sa1,sa2,tr]
        all_goals omega
      · rw [q] at h0'
        simp [plan,bodyPlan,tailPlan,saltPlan,eq_false h0,eq_false h1,eq_true r8,eq_false e8,walk,finish,
          Action.valid,offset_getReg,word_getReg,writeBits_register,x10,r.counter,r.s0,r.s1,r.s2,r.s3,sreg,m4,q,
          r.selector,r.size,r.primitive,h0',f1,f2,c2,f8,z,sa1,sa2,tr]
        all_goals omega
      · rw [q] at h0'
        simp [plan,bodyPlan,tailPlan,saltPlan,eq_false h0,eq_false h1,eq_true r8,eq_false e8,walk,finish,
          Action.valid,offset_getReg,word_getReg,writeBits_register,x10,r.counter,r.s0,r.s1,r.s2,r.s3,sreg,m4,q,
          r.selector,r.size,r.primitive,h0',f1,f2,c2,f8,z,sa1,sa2,tr]
        all_goals omega
      · have gi := group_input i q
        have rs := restore_forms i q s r
        rw [q] at h0'
        by_cases e : i%4096/4%2=0
        all_goals simp [plan,bodyPlan,tailPlan,saltPlan,eq_false h0,eq_false h1,eq_true r8,eq_false e8,e,walk,finish,
          Action.valid,offset_getReg,word_getReg,writeBits_register,x10,r.counter,r.s0,r.s1,r.s2,r.s3,sreg,m4,q,
          r.selector,r.size,r.primitive,h0',f1,f2,c2,f8,z,sa1,sa2,gi,oo,rs,rreg_x10,rreg_x12,rreg_x14,rreg_x15,rreg_x16,rreg_x17,rreg_x31]
        all_goals omega
  · by_cases e9 : rank i=9
    · rcases q with q|q|q|q
      · rw [q] at h0'
        simp [plan,bodyPlan,tailPlan,saltPlan,eq_false h0,eq_false h1,eq_false r8,eq_true e9,walk,finish,
          Action.valid,offset_getReg,word_getReg,writeBits_register,x10,r.counter,r.s0,r.s1,r.s2,r.s3,sreg,m4,q,
          r.selector,r.size,r.primitive,h0',f1,f2,c2,f8,z,tr]
        all_goals omega
      · rw [q] at h0'
        simp [plan,bodyPlan,tailPlan,saltPlan,eq_false h0,eq_false h1,eq_false r8,eq_true e9,walk,finish,
          Action.valid,offset_getReg,word_getReg,writeBits_register,x10,r.counter,r.s0,r.s1,r.s2,r.s3,sreg,m4,q,
          r.selector,r.size,r.primitive,h0',f1,f2,c2,f8,z,tr]
        all_goals omega
      · rw [q] at h0'
        simp [plan,bodyPlan,tailPlan,saltPlan,eq_false h0,eq_false h1,eq_false r8,eq_true e9,walk,finish,
          Action.valid,offset_getReg,word_getReg,writeBits_register,x10,r.counter,r.s0,r.s1,r.s2,r.s3,sreg,m4,q,
          r.selector,r.size,r.primitive,h0',f1,f2,c2,f8,z,tr]
        all_goals omega
      · have gi := group_input i q
        have rs := restore_forms i q s r
        rw [q] at h0'
        by_cases e : i%4096/4%2=0
        all_goals simp [plan,bodyPlan,tailPlan,saltPlan,eq_false h0,eq_false h1,eq_false r8,eq_true e9,e,walk,finish,
          Action.valid,offset_getReg,word_getReg,writeBits_register,x10,r.counter,r.s0,r.s1,r.s2,r.s3,sreg,m4,q,
          r.selector,r.size,r.primitive,h0',f1,f2,c2,f8,z,gi,oo,rs,rreg_x10,rreg_x12,rreg_x14,rreg_x15,rreg_x16,rreg_x17,rreg_x31]
        all_goals omega
    · rcases q with q|q|q|q
      · rw [q] at h0'
        simp [plan,bodyPlan,tailPlan,saltPlan,eq_false h0,eq_false h1,eq_false r8,eq_false e9,walk,finish,
          Action.valid,offset_getReg,word_getReg,writeBits_register,x10,r.counter,r.s0,r.s1,r.s2,r.s3,sreg,m4,q,
          r.selector,r.size,r.primitive,h0',f1,f2,c2,f8,z,tr]
        all_goals omega
      · rw [q] at h0'
        simp [plan,bodyPlan,tailPlan,saltPlan,eq_false h0,eq_false h1,eq_false r8,eq_false e9,walk,finish,
          Action.valid,offset_getReg,word_getReg,writeBits_register,x10,r.counter,r.s0,r.s1,r.s2,r.s3,sreg,m4,q,
          r.selector,r.size,r.primitive,h0',f1,f2,c2,f8,z,tr]
        all_goals omega
      · rw [q] at h0'
        simp [plan,bodyPlan,tailPlan,saltPlan,eq_false h0,eq_false h1,eq_false r8,eq_false e9,walk,finish,
          Action.valid,offset_getReg,word_getReg,writeBits_register,x10,r.counter,r.s0,r.s1,r.s2,r.s3,sreg,m4,q,
          r.selector,r.size,r.primitive,h0',f1,f2,c2,f8,z,tr]
        all_goals omega
      · have gi := group_input i q
        have rs := restore_forms i q s r
        rw [q] at h0'
        by_cases e : i%4096/4%2=0
        all_goals simp [plan,bodyPlan,tailPlan,saltPlan,eq_false h0,eq_false h1,eq_false r8,eq_false e9,e,walk,finish,
          Action.valid,offset_getReg,word_getReg,writeBits_register,x10,r.counter,r.s0,r.s1,r.s2,r.s3,sreg,m4,q,
          r.selector,r.size,r.primitive,h0',f1,f2,c2,f8,z,gi,oo,rs,rreg_x10,rreg_x12,rreg_x14,rreg_x15,rreg_x16,rreg_x17,rreg_x31]
        all_goals omega

theorem packet_walk (s : MachineState) (i : Nat) (limit : i<16777216) (r : PacketRegs s i) :
    walk (fun t => finish s t i) (plan i) s := by
  by_cases h0 : rank i=0
  · exact walk_head s i limit r h0
  by_cases h1 : rank i=1
  · exact walk_c s i limit r h1
  exact walk_follower s i limit r h0 h1

end TwoPermutationPrototype.Grouped
