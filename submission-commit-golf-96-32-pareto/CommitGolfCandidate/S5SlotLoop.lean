import CommitGolfCandidate.S5BucketMemory
import CommitGolfCandidate.S5SlotRead
import CommitGolfCandidate.S5CheckAdvance
namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W Outside)
private def slotEntryOps : List Sym.Calc:=[.addi .x23 .x0 0,.lui .x14 21,.addi .x15 .x0 171]
theorem slot_entry (o : Oracle) (x : CheckInput) (s : MachineState) (pc : s.pc=pcAt 810) (reg : RecordRegs true x 128 s)
    (table : BucketTable o.compression x 128 s) : ∃ t,Flow o s t 3 0 ∧ SlotState o.compression x 0 t := by
  obtain ⟨run,out,mem,ep⟩:=Sym.compiled o slotEntryOps 810 s pc (by decide +kernel)
    (by change ∀ a∈([] : List (Sym.Expr×Nat)),_;simp)
  let t:=Sym.evaluated slotEntryOps s
  have hold (q : Reg) (ne : q∉([.x23,.x14,.x15] : List Reg)) : t.getReg q=s.getReg q:=by
    apply (out q).trans;cases q <;> first | (exfalso;apply ne;decide) | rfl
  obtain ⟨k,small,c⟩:=reg.stream
  have cursor:=c.same mem (hold _ (by decide)) (hold _ (by decide)) (hold _ (by decide)) (hold _ (by decide))
  exact ⟨t,run,⟨ep,out .x23,out .x14,out .x15,⟨(hold _ (by decide)).trans reg.root,(hold _ (by decide)).trans reg.fixed.row,
    (hold _ (by decide)).trans reg.fixed.chain,(read_buffer_memory_congr t s mem _ _).trans
      ((reg.high.read rootBase 32 le_rfl (by decide)).trans (loaded_root x))⟩,⟨k,small,cursor⟩,fun _ h=>by omega,table.same mem⟩⟩

private theorem slot_next (o : Oracle) (s : MachineState) (p : Nat) (small : p<171) (pc : s.pc=pcAt 817) (index : s.getReg .x23=W p) (last : s.getReg .x15=W 171) :
    let t:=(s.setReg .x23 (W (p+1))).setPC (pcAt (slotPC (p+1)))
    Flow o s t 2 0 := by
  let u:=(s.setReg .x23 (W (p+1))).setPC (pcAt 818)
  have inc:=imm_step o s 817 .x23 .x23 1 (W (p+1)) pc (known (by decide +kernel)) ((congrArg (·+signExtend12 1) index).trans (BitVec.ofNat_add p 1).symm)
  have flag : Rel.lt.test (u.getReg .x23) (u.getReg .x15)=decide (p+1<171):=by
    change BitVec.ult (W (p+1)) (s.getReg .x15)=_;rw [last]
    simp only [BitVec.ult,W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : p+1<2^64),Nat.mod_eq_of_lt (by decide : 171<2^64)]
  have back:=branch o u 818 813 .lt .x23 .x15 (by decide +kernel) rfl _ flag
  have e : (if decide (p+1<171) then 813 else 818+1)=slotPC (p+1):=by simp [slotPC]
  rw [e] at back;exact inc.trans back

theorem slot_cycle (o : Oracle) (x : CheckInput) (p : Nat) (s : MachineState) (small : p<171) (state : SlotState o.compression x p s) :
    ∃ t n,n≤442 ∧ Flow o s t n 0 ∧ SlotState o.compression x (p+1) t := by
  obtain ⟨u,n,lim,read,ip,cursor,d,out,keep⟩:=read_slot o x p s state small
  let t:=(u.setReg .x23 (W (p+1))).setPC (pcAt (slotPC (p+1)))
  have update:=slot_next o u p small ip ((keep _ (by decide)).trans state.counter) ((keep _ (by decide)).trans state.limit)
  have stable (q : Reg) (ne : q≠.x23) : t.getReg q=u.getReg q:=MachineState.getReg_setPC.trans (MachineState.getReg_setReg_ne _ _ _ _ ne.symm)
  have old (q : Reg) (h : q∈slotRegs) (ne : q≠.x23) : t.getReg q=s.getReg q:=(stable q ne).trans (keep q h)
  have mem : t.mem=u.mem:=rfl
  obtain ⟨k,rb,c⟩:=cursor
  have ct:=c.same mem (stable _ (by decide)) (stable _ (by decide)) (stable _ (by decide)) (stable _ (by decide))
  have al : slotAddr p%8=0:=by dsimp [slotAddr,slotBase];omega
  have env : CapEnv x t:=⟨(old _ (by decide) (by decide)).trans state.env.root,(old _ (by decide) (by decide)).trans state.env.row,
    (old _ (by decide) (by decide)).trans state.env.chain,(read_buffer_memory_congr t u mem _ _).trans
    ((Open.outside_read out al (by decide) rootBase 32 (by decide) (Or.inr (by dsimp [slotAddr,slotBase,rootBase];omega))).trans state.env.read)⟩
  refine ⟨t,n+2,by omega,read.trans update,⟨rfl,rfl,(old _ (by decide) (by decide)).trans state.slots,
    (old _ (by decide) (by decide)).trans state.limit,env,⟨k,rb,ct⟩,?_,(state.table.slots_away p small out).same mem⟩⟩
  intro j hj;apply (read_buffer_memory_congr t u mem _ _).trans
  by_cases eq:j=p
  · subst j;exact d
  · apply (Open.outside_read out al (by decide) _ 32 (by dsimp [slotAddr,slotBase,MEMORY_BYTES];omega) (Or.inl (by dsimp [slotAddr];omega))).trans
    exact state.previous j (by omega)

theorem slots (o : Oracle) (x : CheckInput) (p n : Nat) (s : MachineState) (last : p+n≤171) (old : SlotState o.compression x p s) :
    ∃ t k,k≤442*n ∧ Flow o s t k 0 ∧ SlotState o.compression x (p+n) t := by
  induction n generalizing p s with
  | zero=>exact ⟨s,0,le_rfl,Flow.refl o s,old⟩
  | succ n ih=>
    obtain ⟨u,a,small,first,mid⟩:=slot_cycle o x p s (by omega) old
    obtain ⟨t,b,lim,in_,end_⟩:=ih (p+1) u (by omega) mid
    exact ⟨t,a+b,by omega,first.trans in_,by simpa only [Nat.add_assoc,Nat.add_comm 1 n] using end_⟩

theorem slots_finished (o : Oracle) (x : CheckInput) (s : MachineState) (st : SlotState o.compression x 171 s) :
    Flow o s (s.setPC (pcAt 823)) 2 0 := by
  obtain ⟨k,small,c⟩:=st.cursor
  have aligned:=c.whole
  change (555170+k)%8=0 at aligned
  have six : k=6:=by omega
  have same : s.getReg .x19=s.getReg .x20:=by rw [c.ptr,c.end_,six];rfl
  have bits : (s.getReg .x21).toNat=0:=by
    rw [c.buf];unfold Reader.window
    have lo : S5.packedInput x<2^S5.wireBits:=BitVec.isLt (S5.atProof x 0 69396)
    rw [Nat.div_eq_of_lt (lt_of_lt_of_le lo (Nat.pow_le_pow_right (by decide) (by decide : S5.wireBits≤slotBit 171)))];rfl
  have zero : s.getReg .x21=0#64:=BitVec.eq_of_toNat_eq bits
  have a:=branch o s 819 821 .eq .x19 .x20 (by decide +kernel) st.pc true (beq_iff_eq.mpr same)
  let u:=s.setPC (pcAt 821)
  have b:=branch o u 821 823 .eq .x21 .x0 (by decide +kernel) rfl true (beq_iff_eq.mpr zero)
  exact a.trans b
end CommitGolfCandidate.S5Machine.Check
