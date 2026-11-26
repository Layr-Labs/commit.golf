import CommitGolfCandidate.ReconstructedCheckField

namespace CommitGolfCandidate.Reconstruction.CheckStream
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckValues CheckParentRun
set_option maxHeartbeats 1000000
set_option maxRecDepth 14000

structure Reader where
  proofBase : Nat
  block : Nat
  widthCell : Nat
  maskCell : Nat

def wordBase (g : Reader) := g.proofBase+8*g.block

def base (g : Reader) : Nat→Nat
  | 1=>64*g.block | 2=>8*g.block | 3=>wordBase g | 4=>g.proofBase | 5=>g.widthCell | 6=>g.maskCell | _=>0

def env (s : MachineState) (g : Reader) : Env where
  initial:=s;zero:=rfl;base:=fun r=>BitVec.ofNat 64 (base g r);answer:=fun _ _=>0

theorem phys (s : MachineState) (g : Reader) (a : Loc) :
    physical (env s g) a=BitVec.ofNat 64 (base g a.region+a.offset.toNat) := by
  simp [physical,env,BitVec.ofNat_add]

theorem point (s : MachineState) (g : Reader) (r n : Nat) :
    physical (env s g) (loc r n)=BitVec.ofNat 64 (base g r+n) := by
  simp [physical,env,loc,BitVec.ofNat_add]

def context (s : MachineState) (g : Reader) (room : g.block<2^40) : CheckCursorValues.Context (env s g) := by
  refine ⟨g.block,room,rfl,rfl,?_⟩
  change BitVec.ofNat 64 (g.proofBase+8*g.block)=BitVec.ofNat 64 (8*g.block)+BitVec.ofNat 64 g.proofBase
  rw [BitVec.ofNat_add,BitVec.add_comm]

structure Placed (g : Reader) : Prop where
  align : g.proofBase%8=0
  room : wordBase g+40≤MEMORY_BYTES

theorem block_bound (g : Reader) (good : Placed g) : g.block<2^40 := by
  have h:=good.room;unfold wordBase MEMORY_BYTES at h;omega

theorem header_layout (s : MachineState) (g : Reader) (good : Placed g) : Layout (env s g) CheckHeaderPlan.table := by
  have ok (a : Loc) (v : CheckHeaderPlan.table.allowed a=true) :
      a.region=3 ∧ a.offset.toNat%8=0 ∧ a.offset.toNat<40 := of_decide_eq_true v
  constructor
  · intro a v;obtain ⟨r,al,small⟩:=ok a v
    rw [phys,r]
    have b := good.room;have hab:=good.align
    change (decide ((BitVec.ofNat 64 (wordBase g+a.offset.toNat)).toNat+8≤MEMORY_BYTES) &&
       decide ((BitVec.ofNat 64 (wordBase g+a.offset.toNat)).toNat%8=0))=true
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by unfold MEMORY_BYTES at b;omega),Bool.and_eq_true]
    simp only [decide_eq_true_eq];unfold wordBase at *;omega
  · intro a b va vb same
    obtain ⟨ra,_,ha⟩:=ok a va;obtain ⟨rb,_,hb⟩:=ok b vb
    rw [phys,phys,ra,rb] at same
    have eq := congrArg BitVec.toNat same;have lim := good.room;unfold MEMORY_BYTES at lim
    change (wordBase g+a.offset.toNat)%2^64=(wordBase g+b.offset.toNat)%2^64 at eq
    rw [Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)] at eq
    have off : a.offset=b.offset:=BitVec.eq_of_toNat_eq (by omega)
    cases a;cases b;simp_all
  · intro a w impossible;cases impossible

def Source (s : MachineState) (g : Reader) (stream : Nat) :=
  ∀ i<5,s.getMem (BitVec.ofNat 64 (wordBase g+8*i))=BitVec.ofNat 64 (HonestStream.word stream (g.block+i))

theorem input (s : MachineState) (g : Reader) (stream : Nat) (same : Source s g stream) : CheckField.Source (env s g) stream g.block := by
  intro i small
  change s.getMem (physical (env s g) (loc 3 (8*i)))=_
  rw [point];exact same i small

theorem header (o : Oracle) (s : MachineState) (g : Reader) (r : Fin 64) (stream : Nat)
    (good : Placed g) (source : Source s g stream) (pc : s.pc=CommitBlocks.addr 122)
    (cursor : s.getReg .x24=BitVec.ofNat 64 (64*g.block+r.val)) (baseReg : s.getReg .x19=BitVec.ofNat 64 g.proofBase) :
    let c:=64*g.block+r.val
    ∃ t, CheckRecorded.Segment o (CheckHeaderPlan.done r).ticks s t [] ∧ t.pc=CommitBlocks.addr 175 ∧
      (t.getReg .x14).toNat=HonestStream.get stream c 64 ∧ (t.getReg .x10).toNat%2^56=HonestStream.get stream (c+64) 56 ∧
      (t.getReg .x11).toNat=HonestStream.get stream (c+120) 64 ∧ (t.getReg .x12).toNat%2^38=HonestStream.get stream (c+184) 38 ∧
      (∀ p,t.getMem p=s.getMem p) ∧ (∀ v∈CheckHeaderPlan.preserve,t.getReg v=s.getReg v) := by
  let e:=env s g
  have init : Matches e (CheckHeaderPlan.start r) s := by
    refine ⟨pc,?_,fun _=>rfl⟩
    intro reg;cases reg <;> try rfl
    · change s.getReg .x19=physical (env s g) (loc 4 0);rw [point];exact baseReg
    · change s.getReg .x24=physical (env s g) (loc 1 r.val);rw [point];exact cursor
  have ref:=input s g stream source
  obtain ⟨t,sg,hm,pos,one,two,three,four,mem,cost,preserve⟩ :=
    CheckHeaderPlan.positive o e (context s g (block_bound g good)) (header_layout s g good) r s init
  have bits (i n : Nat) (positive : 0<n) (w : n≤64) (inside : r.val+i+n≤320) :
      ((CheckHeaderPlan.field (r.val+i) n).val e).toNat%2^n=HonestStream.get stream (64*g.block+r.val+i) n := by
    rw [Nat.add_assoc (64*g.block)]
    exact CheckField.bits e stream g.block _ n w inside (by have:=r.isLt;omega) ref
  refine ⟨t,sg,pos,?_,?_,?_,?_,?_,?_⟩
  · rw [hm.regs,one];have v:=bits 0 64 (by decide) (by decide) (by have:=r.isLt;omega)
    simpa only [Nat.add_zero,Nat.mod_eq_of_lt (Term.val e (CheckHeaderPlan.field r.val 64)).isLt] using v
  · rw [hm.regs,two];exact bits 64 56 (by decide) (by decide) (by have:=r.isLt;omega)
  · rw [hm.regs,three];have v:=bits 120 64 (by decide) (by decide) (by have:=r.isLt;omega)
    simpa only [Nat.mod_eq_of_lt (Term.val e (CheckHeaderPlan.field (r.val+120) 64)).isLt] using v
  · rw [hm.regs,four];exact bits 184 38 (by decide) (by decide) (by have:=r.isLt;omega)
  · intro p;rw [hm.mem,mem];rfl
  · intro v keep
    have e₀:=CheckHeaderPlan.checked r
    simp only [CheckHeaderPlan.receipt,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at e₀
    rw [hm.regs,e₀.2 v keep,←init.regs]

end CommitGolfCandidate.Reconstruction.CheckStream
