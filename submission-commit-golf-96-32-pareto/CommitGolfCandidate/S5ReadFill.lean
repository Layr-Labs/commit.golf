import CommitGolfCandidate.S5ReadCursor
namespace CommitGolfCandidate.S5Machine.Reader
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W)
open Check (Flow)
def FillKeeps (s t : MachineState) := ∀ q,q∉([.x7,.x19,.x21,.x22] : List Reg)→t.getReg q=s.getReg q
attribute [local irreducible] loaded refilled
theorem read_until (o : Oracle) (s : MachineState) (base bytes v bit k w n : Nat) (width : w≤32)
    (amount : n=(w-k+7)/8) (space : bit+w≤8*bytes) (room : base+bytes≤MEMORY_BYTES)
    (pc : s.pc=pcAt 38) (want : s.getReg .x6=W w) (c : Cursor s base bytes v bit k) :
    ∃ t,Flow o s t (8*n) 0 ∧ t.pc=pcAt 38 ∧ Cursor t base bytes v bit (k+8*n) ∧ t.mem=s.mem ∧ FillKeeps s t := by
  induction n generalizing k s with
  | zero=>simp only [Nat.mul_zero,Nat.add_zero];exact ⟨s,Flow.refl o s,pc,c,rfl,fun _ _=>rfl⟩
  | succ n ih=>
    have ksmall : k<w:=by omega
    obtain ⟨one,ip,newc,mem,keep⟩:=read_byte o s base bytes v bit k w width ksmall space room pc want c
    obtain ⟨t,tail,last,ct,same,pres⟩:=ih (s:=refilled s) (k:=k+8) (by omega) ip ((keep _ (by decide)).trans want) newc
    refine ⟨t,?_,last,?_,same.trans mem,fun q h=>(pres q h).trans (keep q h)⟩
    · simpa only [Nat.mul_succ,Nat.add_zero,Nat.add_comm 8 (8*n)] using one.trans tail
    · simpa only [show k+8+8*n=k+8*(n+1) by omega] using ct

theorem filled (o : Oracle) (s : MachineState) (base bytes v bit k w : Nat) (width : w≤32) (kmax : k<8)
    (space : bit+w≤8*bytes) (room : base+bytes≤MEMORY_BYTES) (pc : s.pc=pcAt 38) (want : s.getReg .x6=W w)
    (c : Cursor s base bytes v bit k) :
    ∃ t steps buffered,steps≤33 ∧ w≤buffered ∧ buffered<w+8 ∧ Flow o s t steps 0 ∧ t.pc=pcAt 47 ∧
      Cursor t base bytes v bit buffered ∧ t.mem=s.mem ∧ FillKeeps s t := by
  let n:=(w-k+7)/8
  let b:=k+8*n
  obtain ⟨u,run,ip,cu,mem,keep⟩:=read_until o s base bytes v bit k w n width rfl space room pc want c
  let t:=u.setPC (pcAt 47)
  have enough : w≤b ∧ b<w+8:=by dsimp [b,n];omega
  have cond : (u.getReg .x22).ult (u.getReg .x6)=false := by
    rw [cu.count,keep _ (by decide),want]
    change (W b).ult (W w)=false
    simp only [BitVec.ult,W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show b<2^64 by omega),Nat.mod_eq_of_lt (show w<2^64 by omega),decide_eq_false (Nat.not_lt.mpr enough.1)]
  have go : ordinaryStep u (.base (.BGEU .x22 .x6 36))=some t := by
    change some (if ¬(u.getReg .x22).ult (u.getReg .x6) then u.setPC (u.pc+signExtend13 36) else u.setPC (u.pc+4))=some t
    rw [cond,ip];rfl
  have step:=Check.one_flow o ip (Check.known (by decide +kernel)) (i:=.BGEU .x22 .x6 36) go
  refine ⟨t,8*n+1,b,by dsimp [n];omega,enough.1,enough.2,run.trans step,rfl,?_,mem,?_⟩
  · exact cu.same rfl MachineState.getReg_setPC MachineState.getReg_setPC MachineState.getReg_setPC MachineState.getReg_setPC
  · exact fun q h=>MachineState.getReg_setPC.trans (keep q h)
end CommitGolfCandidate.S5Machine.Reader
