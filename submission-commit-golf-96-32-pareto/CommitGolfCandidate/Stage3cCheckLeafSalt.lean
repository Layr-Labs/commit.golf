import CommitGolfCandidate.Stage3cCheckLeafPrefix
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W Outside wordAt)
def chooseSalt : List Sym.Calc := [.lui .x28 32,.andi .x6 .x14 1]
def selectedPC (odd : Bool) :=if odd then 150 else 142
def saltCopy (odd : Bool) : CopySpec:=⟨.x7,.x28,.x25,0,saltOffset odd⟩
theorem parity (i : Nat) : ((W i &&& 1#64) != 0)=i.testBit 0 := by
  change ((BitVec.ofNat 64 i &&& BitVec.ofNat 64 (2^1-1)) != 0)=_
  rw [←BitVec.ofNat_and,Nat.and_two_pow_sub_one_eq_mod]
  simp only [Nat.testBit_eq_decide_div_mod_eq,Nat.pow_zero,Nat.div_one]
  by_cases pos : i%2=0
  · rw [pos];decide
  · rw [show i%2=1 by omega];decide

theorem salt_select (o : Oracle) (s : MachineState) (i : Nat) (pc : s.pc=pcAt 139) (idx : s.getReg .x14=W i) :
    ∃ t,Flow o s t 3 0 ∧ t.pc=pcAt (selectedPC (i.testBit 0)) ∧ t.getReg .x28=W saltBuf ∧ t.mem=s.mem ∧
      ∀ q,q≠.x6 → q≠.x28 → t.getReg q=s.getReg q := by
  let u:=Sym.evaluated chooseSalt s
  obtain ⟨head,regs,mem,ip⟩:=Sym.compiled o chooseSalt 139 s pc (by decide +kernel)
    (by change ∀ e∈([] : List (Sym.Expr×Nat)),_;simp)
  let t:=u.setPC (pcAt (selectedPC (i.testBit 0)))
  have test : (u.getReg .x6 != 0#64)=i.testBit 0 := by
    have h:=regs .x6;change u.getReg .x6=s.getReg .x14 &&& 1#64 at h;rw [h,idx];exact parity i
  have branch : ordinaryStep u (.base (.BNE .x6 .x0 36))=some t := by
    change some (if u.getReg .x6 != 0#64 then u.setPC (u.pc+signExtend13 36) else u.setPC (u.pc+4))=_
    rw [test,show u.pc=pcAt 141 from ip];unfold t;cases i.testBit 0 <;> rfl
  have step:=one_flow o (show u.pc=pcAt 141 from ip) (known (by decide +kernel)) branch
  refine ⟨t,head.trans step,rfl,MachineState.getReg_setPC.trans (regs .x28),mem,?_⟩
  intro q x y;apply MachineState.getReg_setPC.trans;apply (regs q).trans;cases q <;> first | rfl | contradiction

private theorem after_salt (o : Oracle) (s : MachineState) (odd : Bool) (pc : s.pc=pcAt (selectedPC odd+6))
    (row : s.getReg .x25=W rowBuf) :
    ∃ t,Flow o s t (if odd then 1 else 2) 0 ∧ t.pc=pcAt 157 ∧ t.getReg .x29=W (rowBuf+laneOffset odd) ∧
      t.mem=s.mem ∧ ∀ q,q≠.x29 → t.getReg q=s.getReg q := by
  let imm:=BitVec.ofNat 12 (laneOffset odd)
  let u:=execInstrBr s (.ADDI .x29 .x25 imm)
  have sites : ∀ b : Bool,matchesWord .check (selectedPC b+6,.ADDI .x29 .x25 (BitVec.ofNat 12 (laneOffset b))) :=by decide +kernel
  have move:=one_flow o (t:=u) pc (known (sites odd)) rfl
  have ip : u.pc=pcAt (selectedPC odd+7):=(congrArg (·+4) pc).trans (pc_succ _)
  have val : u.getReg .x29=W (rowBuf+laneOffset odd):=by change s.getReg .x25+signExtend12 imm=_;rw [row];cases odd <;> rfl
  have keep (q : Reg) (h : q≠.x29) : u.getReg q=s.getReg q:=MachineState.getReg_setPC.trans (MachineState.getReg_setReg_ne _ _ _ _ h.symm)
  cases odd with
  | true=>exact ⟨u,move,ip,val,rfl,keep⟩
  | false=>
    let t:=u.setPC (pcAt 157)
    have jump : ordinaryStep u (.base (.JAL .x0 32))=some t := by change some (u.setPC (u.pc+signExtend21 32))=_;rw [ip];rfl
    have last:=one_flow o (show u.pc=pcAt 149 from ip) (known (by decide +kernel)) jump
    exact ⟨t,move.trans last,rfl,MachineState.getReg_setPC.trans val,rfl,fun q h=>MachineState.getReg_setPC.trans (keep q h)⟩

theorem leaf_salt (o : Oracle) (s : MachineState) (i : Nat) (salt : Late.Salt)
    (pc : s.pc=pcAt 139) (idx : s.getReg .x14=W i) (row : s.getReg .x25=W rowBuf)
    (read : readBuffer s saltBuf 24=salt) (zero : ∀ j<12,wordAt s (rowBuf+8*j)=0) :
    let odd:=i.testBit 0
    ∃ t,Flow o s t (if odd then 10 else 11) 0 ∧ t.pc=pcAt 157 ∧ t.getReg .x29=W (rowBuf+laneOffset odd) ∧
      readBuffer t (rowBuf+saltOffset odd) 24=salt ∧ readBuffer t (rowBuf+padOffset odd) 8=0 ∧
      Outside s t (rowBuf+saltOffset odd) 24 ∧ ∀ q,q∉([.x6,.x7,.x28,.x29] : List Reg)→t.getReg q=s.getReg q := by
  dsimp only
  obtain ⟨u,head,pc1,src,mem1,keep1⟩:=salt_select o s i pc idx
  generalize e : i.testBit 0=odd at pc1 ⊢
  have r:=(keep1 _ (by decide) (by decide)).trans row
  have sites : ∀ b : Bool,CopySites (saltCopy b) (selectedPC b) 3:=by unfold CopySites;decide +kernel
  obtain ⟨v,copy⟩:=copy_words o u (selectedPC odd) saltBuf rowBuf 3 (saltCopy odd) (sites odd)
    (by cases odd <;> decide) (by cases odd <;> decide) pc1 src r ⟨by change saltBuf%8=0;decide,by change saltBuf+24≤MEMORY_BYTES;decide⟩
    (by cases odd <;> constructor <;> decide) (Or.inr (by cases odd <;> decide))
  obtain ⟨t,tail,ep,slot,mem2,keep2⟩:=after_salt o v odd copy.pc ((copy.keep _ (by change Reg.x25≠.x7;decide)).trans r)
  have frame : Outside s t (rowBuf+saltOffset odd) 24 := by
    intro q h al ne;exact (congrFun mem2 _).trans ((copy.data.outside q h al ne).trans (congrFun mem1 _))
  have random : readBuffer t (rowBuf+saltOffset odd) 24=salt :=
    (read_buffer_memory_congr t v mem2 _ _).trans ((copied_read (n:=3) copy.data (by change saltBuf%8=0;decide) (by cases odd <;> decide)).trans ((read_buffer_memory_congr u s mem1 _ _).trans read))
  have gap : readBuffer s (rowBuf+padOffset odd) 8=0:=by
    rw [read_word _ _ (by cases odd <;> decide)]
    cases odd <;> first | exact zero 8 (by decide) | exact zero 3 (by decide)
  have all:=(head.trans copy.run).trans tail
  refine ⟨t,?_,ep,slot,random,?_,frame,?_⟩
  · change Flow o s t (if odd then 10 else 11) 0;cases odd <;> exact all
  · exact (Open.outside_read frame (by cases odd <;> decide) (by decide) _ _ (by cases odd <;> decide) (by cases odd <;> decide)).trans gap
  · intro q safe;apply (keep2 q (by intro e;subst q;simp at safe)).trans
    apply (copy.keep q (by change q≠.x7;intro e;subst q;simp at safe)).trans
    apply keep1 <;> intro e <;> subst q <;> simp at safe
end CommitGolfCandidate.Chained.BinaryMachine.Check
