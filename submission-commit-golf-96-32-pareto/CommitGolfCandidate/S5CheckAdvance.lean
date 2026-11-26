import CommitGolfCandidate.S5CheckRecordInput
namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W)
def latchPC (b : Bool):=if b then 807 else 2327
def afterRows (b : Bool):=if b then 810 else 2330
def advanced (s : MachineState) (b : Bool) (k r : Nat) :=
  (s.setReg .x23 (W (k-(r+1)))).setPC (pcAt (if r+1<k then recordBegin b else afterRows b))

theorem record_advance (o : Oracle) (s : MachineState) (b : Bool) (k r : Nat) (small : k≤16777216) (left : r<k)
    (pc : s.pc=pcAt (latchPC b)) (cnt : s.getReg .x23=W (k-r)) :
    ∃ n,n≤3 ∧ Flow o s (advanced s b k r) n 0 := by
  have sites : ∀ b : Bool,matchesWord .check (latchPC b,.ADDI .x23 .x23 4095) ∧
      BranchSite (latchPC b+1) (afterRows b) .eq .x23 .x0 ∧ JumpSite (latchPC b+2) (recordBegin b) .x0:=by decide +kernel
  let n:=k-(r+1)
  let u:=(s.setReg .x23 (W n)).setPC (pcAt (latchPC b+1))
  have dec : s.getReg .x23+signExtend12 4095=W n:=by
    change s.getReg .x23+(-1#64)=_;rw [cnt,←BitVec.sub_eq_add_neg]
    exact (BitVec.ofNat_sub_ofNat_of_le (w:=64) _ 1 (by decide) (by omega)).trans (congrArg W (by dsimp [n];omega))
  have step:=imm_step o s (latchPC b) .x23 .x23 4095 (W n) pc (known (sites b).1) dec
  have flag : Rel.eq.test (u.getReg .x23) (u.getReg .x0)=decide (n=0):=word_eq n 0 (by dsimp [n];omega) (by decide)
  have test:=branch o u (latchPC b+1) (afterRows b) .eq .x23 .x0 (sites b).2.1 rfl _ flag
  by_cases more : r+1<k
  · rw [decide_eq_false (by dsimp [n];omega : n≠0)] at test
    let z:=u.setPC (pcAt (latchPC b+2))
    have back:=jump o z (latchPC b+2) (recordBegin b) .x0 (sites b).2.2 rfl
    refine ⟨3,le_rfl,?_⟩;unfold advanced;rw [if_pos more];exact (step.trans test).trans back
  · rw [decide_eq_true (by dsimp [n];omega : n=0)] at test
    refine ⟨2,by decide,?_⟩;unfold advanced;rw [if_neg more];exact step.trans test

def persistentRegs : List Reg:=[.x3,.x8,.x9,.x18,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27]
theorem RecordRegs.same {b x r s t} (old : RecordRegs b x r s) (mem : t.mem=s.mem)
    (keep : ∀ q∈persistentRegs,t.getReg q=s.getReg q) : RecordRegs b x r t :=
  ⟨(keep _ (by decide)).trans old.root,(keep _ (by decide)).trans old.indices,(keep _ (by decide)).trans old.values,
    (keep _ (by decide)).trans old.count,(keep _ (by decide)).trans old.leaf,
    ⟨(keep _ (by decide)).trans old.fixed.radix,(keep _ (by decide)).trans old.fixed.row,(keep _ (by decide)).trans old.fixed.chain,
     (keep _ (by decide)).trans old.fixed.digest⟩,
    old.stream.same mem (keep _ (by decide)) (keep _ (by decide)) (keep _ (by decide)) (keep _ (by decide)),old.high.same mem⟩
theorem RecordRegs.advanced {b : Bool} {x : CheckInput} {r : Nat} {s u : MachineState} (old : RecordRegs b x (r+1) (s.setReg .x23 (W (x.positions.card-(r+1)))))
    (mem : u.mem=s.mem) (keep : ∀ q∈persistentRegs,u.getReg q=s.getReg q) :
    RecordRegs b x (r+1) (advanced u b x.positions.card r) := by
  apply old.same (t:=Check.advanced u b x.positions.card r) mem
  intro q h
  by_cases eq : q=.x23
  · subst q;rfl
  · exact MachineState.getReg_setPC.trans ((MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm eq)).trans
      ((keep q h).trans (MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm eq)).symm))

theorem dispatch_regs (o : Oracle) (x : CheckInput) (s : MachineState) (b : Bool) (n : Nat)
    (entry : Dispatched o x s b true n) (match_ : x.proof.length=expectLen b x.positions.card) : RecordRegs b x 0 s := by
  refine ⟨entry.root,entry.ix,entry.value,by simpa only [Nat.sub_zero] using entry.num,entry.leaf,
    ⟨entry.radix,entry.row,entry.chain,entry.digest⟩,?_,fun q _ _ _=>congrFun entry.mem _⟩
  cases b
  · exact entry.proof
  · change x.proof.length=69396 at match_
    have source:=wire_source x match_
    refine ⟨0,by decide,⟨entry.proof,?_,entry.bits,?_,by decide,source.same entry.mem⟩⟩
    · simpa only [match_,Bool.true_and,ite_true] using entry.end_
    · rw [entry.held];simp [Reader.window,Nat.mod_one]
end CommitGolfCandidate.S5Machine.Check
