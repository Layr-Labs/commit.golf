import CommitGolfCandidate.LateOpenCapMemory

namespace CommitGolfCandidate.Late.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

structure PairFrame (s : MachineState) (p : Nat) : Prop where
  source : s.getReg .x23=W (nodeAddress 17 (2*p))
  dest : s.getReg .x25=W (slotAddr (2*p))
  left : s.getReg .x28=W (64-p)

def capPair (s : MachineState) :=
  Test.moreCap.after (Part.capNext.after (copyWords (Part.capMid.after (copyWords s 4)) 4))

structure PairResult (s : MachineState) (tree : Levels) (p : Nat) : Prop where
  run : Runs s (capPair s) 22 22
  pc : (capPair s).pc = pcAt (if p+1<64 then 68 else 90)
  frame : PairFrame (capPair s) (p+1)
  outside : Outside s (capPair s) (slotAddr (2*p)) 64
  left : SlotData (capPair s) (2*p) (node tree 17 (2*p))
  right : SlotData (capPair s) (2*p+1) (node tree 17 (2*p+1))

theorem pair_run (s : MachineState) {xs tree salts} (input : Sources s xs tree salts) (size : xs.length≤LENGTH)
    (p : Nat) (lt : p<64) (pc : s.pc=pcAt 68) (fr : PairFrame s p) : PairResult s tree p := by
  let a := copyWords s 4
  let b := Part.capMid.after a
  let c := copyWords b 4
  let u := Part.capNext.after c
  have lo : 2*p < 128 := by omega
  have hi : 2*p+1 < 128 := by omega
  have trail : slotAddr (2*p+1)=slotAddr (2*p)+32 := by unfold slotAddr;omega
  have addr := (children_contiguous 17 p).1
  have first := copy_node .firstCap rfl s input 17 (2*p) (2*p) (by decide) lo lo pc fr.source fr.dest
  have mid := no_load .capMid a first.pc rfl
  have al := slot_bounds (2*p) lo
  have firstOutside : Outside s a (slotAddr (2*p)) 32 := by simpa only [bytes,List.length_ofFn] using first.data.outside
  have inputB := (input.after size _ _ firstOutside (by unfold capBase at al;omega) al.2.2.1 (by decide)).same_mem mid.mem
  have srcB := mid.regs .x23; change b.getReg .x23=a.getReg .x23+32 at srcB
  have dstB := mid.regs .x25; change b.getReg .x25=a.getReg .x25+32 at dstB
  rw [copy_keeps s 4 _ (by decide : Reg.x6≠.x23),fr.source] at srcB
  rw [copy_keeps s 4 _ (by decide : Reg.x6≠.x25),fr.dest] at dstB
  have sb : b.getReg .x23=W (nodeAddress 17 (2*p+1)) := srcB.trans ((BitVec.ofNat_add _ 32).symm.trans (congrArg W addr.symm))
  have db : b.getReg .x25=W (slotAddr (2*p+1)) := dstB.trans ((BitVec.ofNat_add _ 32).symm.trans (congrArg W trail.symm))
  have second := copy_node .secondCap rfl b inputB 17 (2*p+1) (2*p+1) (by decide) hi hi mid.pc sb db
  have bump := no_load .capNext c second.pc rfl
  have latch := test_run .moreCap u bump.pc
  have left0 := (copy_keeps b 4 .x28 (by decide)).trans ((mid.keep _ rfl).trans ((copy_keeps s 4 _ (by decide)).trans fr.left))
  have left := bump.regs .x28;change u.getReg .x28=c.getReg .x28+18446744073709551615 at left
  rw [left0,W,decrement (64-p) (by omega), show 64-p-1=64-(p+1) by omega] at left
  have taken : Test.moreCap.taken u=decide (p+1<64) := by
    change (u.getReg .x28 != 0)=_
    rw [left,count_test (64-(p+1)) (by omega)]
    by_cases h:p+1<64 <;> simp [h,show 64-(p+1)≠0 ↔ p+1<64 by omega] <;> omega
  have srcC := (copy_keeps b 4 .x23 (by decide)).trans sb
  have dstC := (copy_keeps b 4 .x25 (by decide)).trans db
  have srcU := bump.regs .x23;change u.getReg .x23=c.getReg .x23+64 at srcU
  have dstU := bump.regs .x25;change u.getReg .x25=c.getReg .x25+32 at dstU
  rw [srcC] at srcU;rw [dstC] at dstU
  have written := second.data.congr_mem (s' := a) mid.mem.symm (show (capPair s).mem=c.mem from bump.mem)
  have out2 : Outside a (capPair s) (slotAddr (2*p+1)) 32 := by simpa only [bytes,List.length_ofFn] using written.outside
  refine ⟨(((first.run.trans mid.runs).trans second.run).trans bump.runs).trans latch,?_,⟨?_,?_,?_⟩,?_,?_,written.data⟩
  · change pcAt (if Test.moreCap.taken u then _ else _)=_
    rw [taken];by_cases e:p+1<64 <;> simp [e,Test.target,Test.start]
  · apply MachineState.getReg_setPC.trans (srcU.trans _)
    exact (BitVec.ofNat_add _ 64).symm.trans (congrArg W (by unfold nodeAddress gapOffset;omega))
  · apply MachineState.getReg_setPC.trans (dstU.trans _)
    exact (BitVec.ofNat_add _ 32).symm.trans (congrArg W (by unfold slotAddr;omega))
  · exact MachineState.getReg_setPC.trans left
  · exact (firstOutside.weaken _ _ le_rfl (by omega)).chain (out2.weaken _ _ (by omega) (by omega))
  · apply first.data.data.after_outside out2 (slot_bounds _ hi).2.2.1 (by decide)
    · simpa only [bytes,List.length_ofFn] using al.2.2.2
    · left;simp only [bytes,List.length_ofFn,trail];omega

def fillCap : Nat → MachineState → MachineState
  | 0,s => s | n+1,s => fillCap n (capPair s)

structure FillResult (s : MachineState) (tree : Levels) (p n : Nat) : Prop where
  run : Runs s (fillCap n s) (22*n) (22*n)
  pc : (fillCap n s).pc=pcAt (if p+n<64 then 68 else 90)
  outside : Outside s (fillCap n s) (slotAddr (2*p)) (64*n)
  slots : ∀ j, 2*p≤j → j<2*(p+n) → SlotData (fillCap n s) j (node tree 17 j)

theorem fill_run (s : MachineState) {xs tree salts} (input : Sources s xs tree salts) (size : xs.length≤LENGTH)
    (n p : Nat) (bound : p+n≤64) (pc : s.pc=pcAt (if p<64 then 68 else 90)) (f : PairFrame s p) :
    FillResult s tree p n := by
  induction n generalizing p s with
  | zero =>
    exact ⟨Runs.refl _,by simpa only [fillCap,Nat.add_zero] using pc,fun _ _ _ _ => rfl,fun j a b => False.elim ((Nat.not_lt_of_ge a) b)⟩
  | succ n ih =>
    have lt : p<64 := by omega
    rw [if_pos lt] at pc
    have one := pair_run s input size p lt pc f
    obtain ⟨h,_,al,_⟩ := slot_bounds (2*p) (by omega)
    have high : proofBase≤slotAddr (2*p) := (Nat.le_add_right proofBase 68608).trans h
    have nextInput := input.after size (slotAddr (2*p)) 64 one.outside high al (by decide)
    have rem := ih (capPair s) nextInput
      (p+1) (by omega) one.pc one.frame
    have step : slotAddr (2*(p+1))=slotAddr (2*p)+64 := by unfold slotAddr;omega
    have sum : p+1+n=p+(n+1) := by omega
    refine ⟨?_,by simpa only [fillCap,sum] using rem.pc,?_,?_⟩
    · simpa only [fillCap,Nat.mul_succ,Nat.add_comm 22 (22*n)] using one.run.trans rem.run
    · exact (one.outside.weaken _ _ le_rfl (by omega)).chain (rem.outside.weaken _ _ (by omega) (by omega))
    · intro j low high
      by_cases after : 2*(p+1)≤j
      · exact rem.slots j after (by omega)
      have small : j<128 := by omega
      have prior : SlotData (capPair s) j (node tree 17 j) := by
        rcases (show j=2*p ∨ j=2*p+1 by omega) with rfl|rfl
        · exact one.left
        · exact one.right
      apply prior.after_outside rem.outside (by unfold slotAddr capBase proofBase;omega) (by omega)
      · simpa only [bytes,List.length_ofFn] using (slot_bounds j small).2.2.2
      · left;simp only [bytes,List.length_ofFn,slotAddr];omega

end CommitGolfCandidate.Late.Open
