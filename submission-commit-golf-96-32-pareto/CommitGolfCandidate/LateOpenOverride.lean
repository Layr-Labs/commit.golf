import CommitGolfCandidate.LateOpenCapMemory

namespace CommitGolfCandidate.Late.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def slotOf (i : Index) := i.val/131072
def bucketOf (i : Index) := i.val/65536

structure ReverseFrame (s : MachineState) (n : Nat) : Prop where
  output : s.getReg .x18=W capBase
  nodes : s.getReg .x19=W (layerBase 16)
  cursor : s.getReg .x24=W (indexBase+8*n)
  left : s.getReg .x28=W n

def Slots (s : MachineState) (tree : Levels) (xs : List Index) :=
  ∀ p < 128, SlotData s p (capSlot tree xs p)

def overrideOne (s : MachineState) :=
  Test.moreOverrides.after (Part.reverseNext.after (copyWords (Part.overrideSource.after s) 4))

structure OverrideResult (s : MachineState) (xs : List Index) (tree : Levels) (r : Nat) : Prop where
  run : Runs s (overrideOne s) 21 21
  pc : (overrideOne s).pc=pcAt (if r=0 then 129 else 108)
  frame : ReverseFrame (overrideOne s) r
  outside : Outside s (overrideOne s) capBase 4096
  slots : Slots (overrideOne s) tree (xs.drop r)

private theorem back8 (base r : Nat) :
    W (base+8*(r+1))+18446744073709551608=W (base+8*r) := by
  rw [show base+8*(r+1)=base+8*r+8 by omega]
  unfold W; rw [BitVec.ofNat_add (base+8*r) 8,BitVec.add_assoc]
  exact BitVec.add_zero _

private theorem mask_bucket (i : Index) :
    ((W i.val >>> 16) &&& 255) = W (bucketOf i) := by
  have hi := i.isLt;change i.val<16777216 at hi
  rw [show W i.val=BitVec.ofNat 64 i.val by rfl,shr _ 16 (by omega)]
  change BitVec.ofNat 64 (i.val/65536) &&& BitVec.ofNat 64 (2^8-1) = _
  rw [←BitVec.ofNat_and,Nat.and_two_pow_sub_one_eq_mod,Nat.mod_eq_of_lt (by change i.val/65536<256;omega)]
  rfl

private theorem obtain_src (s : MachineState) (i : Index) (r : Nat) (f : ReverseFrame s (r+1))
    (loaded : s.getMem (W (indexBase+8*r))=W i.val) (block : BlockResult .overrideSource s) :
    let a := Part.overrideSource.after s
    a.getReg .x23=W (nodeAddress 16 (mate i 16)) ∧ a.getReg .x25=W (slotAddr (slotOf i)) ∧
    a.getReg .x24=W (indexBase+8*r) := by
  let a := Part.overrideSource.after s
  let load := s.getMem ((s.getReg .x24 + 18446744073709551608)+0)
  let bucket := (load >>> 16) &&& 255
  have cur : s.getReg .x24 +18446744073709551608=W (indexBase+8*r) := by rw [f.cursor,back8]
  have reduced : bucket = W (bucketOf i) := by
    unfold bucket load
    rw [cur,show W (indexBase+8*r)+(0:Word)=W (indexBase+8*r) from BitVec.add_zero _,loaded,mask_bucket]
  have sb := block.regs .x23; change a.getReg .x23 = s.getReg .x19 + (((bucket ^^^ 1)+(bucket >>> 1)) <<< 5) at sb
  rw [f.nodes,reduced] at sb
  have db := block.regs .x25; change a.getReg .x25 = s.getReg .x18 + ((bucket >>> 1) <<< 5) at db
  rw [f.output,reduced] at db
  have h := i.isLt;change i.val < 16777216 at h
  have small : bucketOf i<2^64 := by unfold bucketOf;omega
  refine ⟨sb.trans (sibling_ptr _ _ small),db.trans ?_,(block.regs .x24).trans cur⟩
  change BitVec.ofNat 64 capBase+((BitVec.ofNat 64 (bucketOf i) >>> 1) <<< 5)=_
  rw [shr _ _ small,shifted,←BitVec.ofNat_add]
  apply congrArg W; unfold slotAddr slotOf bucketOf;omega

theorem override_run (s : MachineState) {xs tree salts} (input : Sources s xs tree salts) (k : xs.length=128)
    (r : Nat) (lt : r<128) (pc : s.pc=pcAt 108) (f : ReverseFrame s (r+1))
    (table : Slots s tree (xs.drop (r+1))) : OverrideResult s xs tree r := by
  let i := ix xs r; let p := slotOf i
  let a := Part.overrideSource.after s;let c := copyWords a 4;let u := Part.reverseNext.after c
  have loc : s.getReg .x24+18446744073709551608=W (indexBase+8*r) := by rw [f.cursor,back8]
  have head := block_result .overrideSource s pc (by
    intro e mem; change e∈[_] at mem; rcases List.mem_singleton.mp mem with rfl
    change accessValid ((s.getReg .x24+18446744073709551608)+0) 8=true
    rw [loc,show W (indexBase+8*r)+(0:Word)=W (indexBase+8*r) from BitVec.add_zero _]
    apply access_at <;> simp only [indexBase,MEMORY_BYTES] <;> omega)
  obtain ⟨sp,dp,idx⟩ := obtain_src s i r f (input.index r (by omega)) head
  have sb : p<128 := by have h:=i.isLt;change i.val<16777216 at h;unfold p slotOf;omega
  have copied := copy_node .overrideCap rfl a (input.same_mem head.mem) 16 (mate i 16) p
    (by decide) (mate_bound _ _ (by decide)) sb head.pc sp dp
  have next := no_load .reverseNext c copied.pc rfl
  have latch := test_run .moreOverrides u next.pc
  have reg (x : Reg) (ok : Reg.x6≠x) (saved : Part.overrideSource.equation x=original x) :
      c.getReg x=s.getReg x := (copy_keeps a 4 x ok).trans (head.keep x saved)
  have left := next.regs .x28
  change u.getReg .x28=c.getReg .x28+18446744073709551615 at left
  rw [reg _ (by decide) rfl,f.left,W,decrement (r+1) (by omega),Nat.add_sub_cancel] at left
  have take : Test.moreOverrides.taken u=decide (r≠0) := by
    change (u.getReg .x28 != 0)=_
    rw [left];exact count_test r (by omega)
  have data := copied.data.congr_mem head.mem.symm (show (overrideOne s).mem=c.mem from next.mem)
  have save : Outside s (overrideOne s) (slotAddr p) 32 := by simpa only [bytes,List.length_ofFn] using data.outside
  have keep (x : Reg) (ok : Part.reverseNext.equation x=original x) :
      (overrideOne s).getReg x = c.getReg x := MachineState.getReg_setPC.trans (next.keep x ok)
  refine ⟨((head.runs.trans copied.run).trans next.runs).trans latch,?_,
    ⟨(keep _ rfl).trans ((reg _ (by decide) rfl).trans f.output),
     (keep _ rfl).trans ((reg _ (by decide) rfl).trans f.nodes),
     (keep _ rfl).trans ((copy_keeps a 4 _ (by decide)).trans idx),MachineState.getReg_setPC.trans left⟩,
    save.weaken _ _ (slot_bounds p sb).1 (slot_bounds p sb).2.1,?_⟩
  · change pcAt (if Test.moreOverrides.taken u then _ else _)=_
    rw [take];by_cases z:r=0 <;> simp [z,Test.target,Test.start]
  · intro q hq
    have hi : r<xs.length := by omega
    have drop : xs.drop r=i::xs.drop (r+1) := by
      rw [List.drop_eq_getElem_cons hi];simp only [i,ix,List.getElem?_eq_getElem hi,Option.getD_some]
    rw [drop];by_cases hit : q=p
    · subst q
      have eq : capSlot tree (i::xs.drop (r+1)) p=node tree 16 (mate i 16) := by simp [capSlot,p,slotOf,mate,indexAbove]
      rw [eq];exact data.data
    · have ne : i.val/2^17≠q := Ne.symm hit
      have eq : capSlot tree (i::xs.drop (r+1)) q=capSlot tree (xs.drop (r+1)) q := by
        unfold capSlot;rw [List.find?_cons_of_neg (p:=fun z : Index => z.val/2^17 == q) (a:=i) (show ¬ ((i.val/2^17 == q)=true) from fun h => ne (beq_iff_eq.mp h))]
      rw [eq];exact slot_transfer (table q hq) hq sb hit save

end CommitGolfCandidate.Late.Open
