import CommitGolfCandidate.OPBatchRecord
import CommitGolfCandidate.LateFormat
import CommitGolfCandidate.LateOpenCapMemory

/-! A96 batch opening: all 128 records (words 140..264), then the 128 thirty-byte cap slots
(default fill at 265..336, sibling overrides at 337..399). -/
namespace CommitGolfCandidate.Late.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def runRecordsB : Nat → MachineState → MachineState
  | 0,s => s | n+1,s => runRecordsB n (recordB s)

def recordsB (tree : Levels) (salt : SaltTape) (xs : List Index) (r n : Nat) : Proof :=
  (List.range' r n).flatMap fun j => batchRecord tree salt (ix xs j)

theorem recordsB_cons (tree : Levels) (salt : SaltTape) (xs : List Index) (r n : Nat) :
    recordsB tree salt xs r (n+1) = batchRecord tree salt (ix xs r) ++ recordsB tree salt xs (r+1) n := by
  simp only [recordsB,List.range'_succ,List.flatMap_cons]

theorem recordsB_len (tree : Levels) (salt : SaltTape) (xs : List Index) (r n : Nat) :
    (recordsB tree salt xs r n).length = 510*n := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih => rw [recordsB_cons,List.length_append,batch_record_size,ih,Nat.mul_succ]; omega

theorem all_recordsB (tree : Levels) (salt : SaltTape) (xs : List Index) :
    recordsB tree salt xs 0 xs.length = xs.flatMap (batchRecord tree salt) := by
  have xsEq : (List.range xs.length).map (ix xs)=xs := by
    apply List.ext_getElem
    · simp
    · intro k _ hk; simp only [List.getElem_map,List.getElem_range,ix,List.getElem?_eq_getElem hk,Option.getD_some]
  unfold recordsB
  rw [←List.range_eq_range',←List.flatMap_map, xsEq]

structure RecordsBResult (s : MachineState) (tree : Levels) (salts : SaltTape) (xs : List Index) (r n : Nat) : Prop where
  run : Runs s (runRecordsB n s) (703*n) (703*n)
  pc : (runRecordsB n s).pc = pcAt (if r+n < 128 then 140 else 265)
  anchor : BAnchor (runRecordsB n s) (r+n)
  data : BWritten s (runRecordsB n s) (bRecAddr r) (recordsB tree salts xs r n)

theorem records_b (s : MachineState) (tree : Levels) (salts : SaltTape) (xs : List Index) (r n : Nat)
    (pc : s.pc = pcAt (if r < 128 then 140 else 265)) (anchor : BAnchor s r) (inside : r+n ≤ 128)
    (card : xs.length = 128) (src : Sources s xs tree salts) : RecordsBResult s tree salts xs r n := by
  induction n generalizing r s with
  | zero => exact ⟨Runs.refl _,by simpa only [runRecordsB,Nat.add_zero] using pc,anchor,BWritten.empty _ _⟩
  | succ n ih =>
    have lt : r<128 := by omega
    rw [if_pos lt] at pc
    have size : xs.length ≤ LENGTH := by rw [card]; decide
    have h := record_b s tree salts xs r pc anchor (by omega) card src
    have tail := ih (recordB s) (r+1) h.pc h.anchor (by omega)
      (src.afterB size _ _ h.bytes.outside (by unfold bRecAddr; omega))
    have plus : r+1+n=r+(n+1) := by omega
    have next : bRecAddr r+(batchRecord tree salts (ix xs r)).length = bRecAddr (r+1) := by
      rw [batch_record_size]; unfold bRecAddr; omega
    refine ⟨?_,by simpa only [runRecordsB,plus] using tail.pc,by simpa only [runRecordsB,plus] using tail.anchor,?_⟩
    · exact (show 703+703*n=703*(n+1) by omega) ▸ h.run.trans tail.run
    · rw [recordsB_cons]
      exact h.bytes.append (next.symm ▸ tail.data) (by rw [next]; unfold bRecAddr proofBase MEMORY_BYTES; omega)

/-! ### Cap slots -/

def capBaseB := proofBase+65280
def slotB (p : Nat) := capBaseB+30*p
def SlotB (s : MachineState) (p : Nat) (v : Digest) := HasBytes s (slotB p) (bytes (n:=30) (low240 v))

theorem slotB_bounds (p : Nat) (hi : p<128) : capBaseB≤slotB p ∧ slotB p+30≤capBaseB+3840 ∧
    slotB p%2=0 ∧ slotB p+30≤MEMORY_BYTES ∧ proofBase ≤ slotB p := by
  unfold slotB capBaseB proofBase MEMORY_BYTES;omega

theorem node_low_bytes (s : MachineState) {xs tree salts} (input : Sources s xs tree salts)
    (d j : Nat) (depth : d≤LOG_LENGTH) (ix : j<levelCount d) :
    HasBytes s (nodeAddress d j) (bytes (n:=30) (low240 (node tree d j))) :=
  (read_bytes s _ 32 _ (input.node d depth j ix)).low

structure PairFrameB (s : MachineState) (p : Nat) : Prop where
  source : s.getReg .x23=W (nodeAddress 17 (2*p))
  dest : s.getReg .x25=W (slotB (2*p))
  left : s.getReg .x28=W (64-p)

def capPairB (s : MachineState) :=
  Test.bMoreCap.after (Part.bCapNext.after (hcopy .capSecond (Part.bCapMid.after (hcopy .capFirst s))))

structure PairResultB (s : MachineState) (tree : Levels) (p : Nat) : Prop where
  run : Runs s (capPairB s) 66 66
  pc : (capPairB s).pc = pcAt (if p+1<64 then 271 else 337)
  frame : PairFrameB (capPairB s) (p+1)
  outside : BOut s (capPairB s) (slotB (2*p)) 60
  left : SlotB (capPairB s) (2*p) (node tree 17 (2*p))
  right : SlotB (capPairB s) (2*p+1) (node tree 17 (2*p+1))

theorem pair_b (s : MachineState) {xs tree salts} (input : Sources s xs tree salts) (size : xs.length≤LENGTH)
    (p : Nat) (lt : p<64) (pc : s.pc=pcAt 271) (fr : PairFrameB s p) : PairResultB s tree p := by
  let a := hcopy .capFirst s
  let b := Part.bCapMid.after a
  let c := hcopy .capSecond b
  let u := Part.bCapNext.after c
  have lo : 2*p < 128 := by omega
  have hi : 2*p+1 < 128 := by omega
  have trail : slotB (2*p+1)=slotB (2*p)+30 := by unfold slotB;omega
  have addr := (children_contiguous 17 p).1
  have nb1 := node_ok 17 (2*p) lo
  have nb2 := node_ok 17 (2*p+1) hi
  have sl1 := slotB_bounds (2*p) lo
  have sl2 := slotB_bounds (2*p+1) hi
  have hc1 := hcopy_run .capFirst s pc _ _ fr.source fr.dest _ (by simp [bytes,HSite.count])
    (node_low_bytes s input 17 (2*p) (by decide) lo) (by have := nb1.2.2; omega) sl1.2.2.1
    (by have := nb1.2.1; unfold indexBase at this; unfold MEMORY_BYTES; simp only [HSite.count]; omega)
    (by simp only [HSite.count]; omega)
    (Or.inl (by have := nb1.2.1; unfold indexBase at this; have := sl1.2.2.2.2; unfold proofBase at this; simp only [HSite.count]; omega))
  have mid := no_load .bCapMid a hc1.pc rfl
  have inputB := (input.afterB size _ _ hc1.data.outside sl1.2.2.2.2).same_mem mid.mem
  have srcB := mid.regs .x23; change b.getReg .x23=a.getReg .x23+32 at srcB
  have dstB := mid.regs .x25; change b.getReg .x25=a.getReg .x25+30 at dstB
  rw [hc1.regs _ (by decide),fr.source] at srcB
  rw [hc1.regs _ (by decide),fr.dest] at dstB
  have sb : b.getReg .x23=W (nodeAddress 17 (2*p+1)) := srcB.trans ((BitVec.ofNat_add _ 32).symm.trans (congrArg W addr.symm))
  have db : b.getReg .x25=W (slotB (2*p+1)) := dstB.trans ((BitVec.ofNat_add _ 30).symm.trans (congrArg W trail.symm))
  have hc2 := hcopy_run .capSecond b mid.pc _ _ sb db _ (by simp [bytes,HSite.count])
    (node_low_bytes b inputB 17 (2*p+1) (by decide) hi) (by have := nb2.2.2; omega) sl2.2.2.1
    (by have := nb2.2.1; unfold indexBase at this; unfold MEMORY_BYTES; simp only [HSite.count]; omega)
    (by simp only [HSite.count]; omega)
    (Or.inl (by have := nb2.2.1; unfold indexBase at this; have := sl2.2.2.2.2; unfold proofBase at this; simp only [HSite.count]; omega))
  have bump := no_load .bCapNext c hc2.pc rfl
  have latch := test_run .bMoreCap u bump.pc
  have left0 : c.getReg .x28 = W (64-p) :=
    (hc2.regs _ (by decide)).trans ((mid.keep _ rfl).trans ((hc1.regs _ (by decide)).trans fr.left))
  have left := bump.regs .x28;change u.getReg .x28=c.getReg .x28+18446744073709551615 at left
  rw [left0,W,decrement (64-p) (by omega), show 64-p-1=64-(p+1) by omega] at left
  have taken : Test.bMoreCap.taken u=decide (p+1<64) := by
    change (u.getReg .x28 != 0)=_
    rw [left,count_test (64-(p+1)) (by omega)]
    by_cases h:p+1<64 <;> simp [h] <;> omega
  have srcC := (hc2.regs _ (by decide) : c.getReg .x23 = b.getReg .x23).trans sb
  have dstC := (hc2.regs _ (by decide) : c.getReg .x25 = b.getReg .x25).trans db
  have srcU := bump.regs .x23;change u.getReg .x23=c.getReg .x23+64 at srcU
  have dstU := bump.regs .x25;change u.getReg .x25=c.getReg .x25+30 at dstU
  rw [srcC] at srcU;rw [dstC] at dstU
  have endMem : (capPairB s).mem = c.mem := (test_mem _ u).trans bump.mem
  have written := hc2.data.congr_mem (s' := a) mid.mem.symm endMem
  have out2 : BOut a (capPairB s) (slotB (2*p+1)) 30 := by simpa only [bytes,List.length_ofFn] using written.outside
  have out1 : BOut s a (slotB (2*p)) 30 := by simpa only [bytes,List.length_ofFn] using hc1.data.outside
  refine ⟨(((hc1.run.trans mid.runs).trans hc2.run).trans bump.runs).trans latch,?_,⟨?_,?_,?_⟩,?_,?_,written.data⟩
  · change pcAt (if Test.bMoreCap.taken u then _ else _)=_
    rw [taken];by_cases e:p+1<64 <;> simp [e,Test.target,Test.start]
  · apply MachineState.getReg_setPC.trans (srcU.trans _)
    exact (BitVec.ofNat_add _ 64).symm.trans (congrArg W (by unfold nodeAddress gapOffset;omega))
  · apply MachineState.getReg_setPC.trans (dstU.trans _)
    exact (BitVec.ofNat_add _ 30).symm.trans (congrArg W (by unfold slotB;omega))
  · exact MachineState.getReg_setPC.trans left
  · exact (out1.weaken _ _ le_rfl (by omega)).chain (out2.weaken _ _ (by omega) (by omega))
  · apply hc1.data.data.frame out2
    · simp only [bytes,List.length_ofFn]; exact sl1.2.2.2.1
    · left;simp only [bytes,List.length_ofFn,trail];omega

def fillCapB : Nat → MachineState → MachineState
  | 0,s => s | n+1,s => fillCapB n (capPairB s)

structure FillResultB (s : MachineState) (tree : Levels) (p n : Nat) : Prop where
  run : Runs s (fillCapB n s) (66*n) (66*n)
  pc : (fillCapB n s).pc=pcAt (if p+n<64 then 271 else 337)
  outside : BOut s (fillCapB n s) (slotB (2*p)) (60*n)
  slots : ∀ j, 2*p≤j → j<2*(p+n) → SlotB (fillCapB n s) j (node tree 17 j)

theorem fill_b (s : MachineState) {xs tree salts} (input : Sources s xs tree salts) (size : xs.length≤LENGTH)
    (n p : Nat) (bound : p+n≤64) (pc : s.pc=pcAt (if p<64 then 271 else 337)) (f : PairFrameB s p) :
    FillResultB s tree p n := by
  induction n generalizing p s with
  | zero =>
    exact ⟨Runs.refl _,by simpa only [fillCapB,Nat.add_zero] using pc,fun _ _ _ => rfl,
      fun j a b => False.elim ((Nat.not_lt_of_ge a) b)⟩
  | succ n ih =>
    have lt : p<64 := by omega
    rw [if_pos lt] at pc
    have one := pair_b s input size p lt pc f
    have bd := slotB_bounds (2*p) (by omega)
    have nextInput := input.afterB size (slotB (2*p)) 60 one.outside bd.2.2.2.2
    have rem := ih (capPairB s) nextInput (p+1) (by omega) one.pc one.frame
    have sum : p+1+n=p+(n+1) := by omega
    refine ⟨?_,by simpa only [fillCapB,sum] using rem.pc,?_,?_⟩
    · simpa only [fillCapB,Nat.mul_succ,Nat.add_comm 66 (66*n)] using one.run.trans rem.run
    · exact (one.outside.weaken _ _ le_rfl (by omega)).chain
        (rem.outside.weaken _ _ (by unfold slotB; omega) (by unfold slotB; omega))
    · intro j low high
      by_cases after : 2*(p+1)≤j
      · exact rem.slots j after (by omega)
      have small : j<128 := by omega
      have prior : SlotB (capPairB s) j (node tree 17 j) := by
        rcases (show j=2*p ∨ j=2*p+1 by omega) with rfl|rfl
        · exact one.left
        · exact one.right
      apply prior.frame rem.outside
      · simp only [bytes,List.length_ofFn]; exact (slotB_bounds j small).2.2.2.1
      · left;simp only [bytes,List.length_ofFn,slotB];omega

/-! ### Overrides -/

structure ReverseFrameB (s : MachineState) (n : Nat) : Prop where
  output : s.getReg .x18=W capBaseB
  nodes : s.getReg .x19=W (layerBase 16)
  cursor : s.getReg .x24=W (indexBase+8*n)
  left : s.getReg .x28=W n

def SlotsB (s : MachineState) (tree : Levels) (xs : List Index) :=
  ∀ p < 128, SlotB s p (capSlot tree xs p)

def overrideB (s : MachineState) :=
  Test.bMoreOverrides.after (Part.bReverseNext.after (hcopy .override (Part.bOverrideSource.after s)))

structure OverrideResultB (s : MachineState) (xs : List Index) (tree : Levels) (r : Nat) : Prop where
  run : Runs s (overrideB s) 45 45
  pc : (overrideB s).pc=pcAt (if r=0 then 400 else 355)
  frame : ReverseFrameB (overrideB s) r
  outside : BOut s (overrideB s) capBaseB 3840
  slots : SlotsB (overrideB s) tree (xs.drop r)

private theorem back8B (base r : Nat) :
    W (base+8*(r+1))+18446744073709551608=W (base+8*r) := by
  rw [show base+8*(r+1)=base+8*r+8 by omega]
  unfold W; rw [BitVec.ofNat_add (base+8*r) 8,BitVec.add_assoc]
  exact BitVec.add_zero _

private theorem mask_bucketB (i : Index) :
    ((W i.val >>> 16) &&& 255) = W (i.val/65536) := by
  have hi := i.isLt;change i.val<16777216 at hi
  rw [show W i.val=BitVec.ofNat 64 i.val by rfl,shr _ 16 (by omega)]
  change BitVec.ofNat 64 (i.val/65536) &&& BitVec.ofNat 64 (2^8-1) = _
  rw [←BitVec.ofNat_and,Nat.and_two_pow_sub_one_eq_mod,Nat.mod_eq_of_lt (by change i.val/65536<256;omega)]
  rfl

private theorem thirty (n : Nat) (small : n < 2^32) :
    (W n <<< 5) - (W n <<< 1) = W (30*n) := by
  unfold W; rw [shifted,shifted]
  rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]
  apply congrArg (BitVec.ofNat 64); omega

private theorem obtain_srcB (s : MachineState) (i : Index) (r : Nat) (f : ReverseFrameB s (r+1))
    (loaded : s.getMem (W (indexBase+8*r))=W i.val) (block : BlockResult .bOverrideSource s) :
    let a := Part.bOverrideSource.after s
    a.getReg .x23=W (nodeAddress 16 (mate i 16)) ∧ a.getReg .x25=W (slotB (i.val/131072)) ∧
    a.getReg .x24=W (indexBase+8*r) := by
  let a := Part.bOverrideSource.after s
  let load := s.getMem ((s.getReg .x24 + 18446744073709551608)+0)
  let bucket := (load >>> 16) &&& 255
  have cur : s.getReg .x24 +18446744073709551608=W (indexBase+8*r) := by rw [f.cursor,back8B]
  have reduced : bucket = W (i.val/65536) := by
    unfold bucket load
    rw [cur,show W (indexBase+8*r)+(0:Word)=W (indexBase+8*r) from BitVec.add_zero _,loaded,mask_bucketB]
  have sb := block.regs .x23; change a.getReg .x23 = s.getReg .x19 + (((bucket ^^^ 1)+(bucket >>> 1)) <<< 5) at sb
  rw [f.nodes,reduced] at sb
  have db := block.regs .x25
  change a.getReg .x25 = s.getReg .x18 + (((bucket >>> 1) <<< 5) - ((bucket >>> 1) <<< 1)) at db
  rw [f.output,reduced] at db
  have h := i.isLt;change i.val < 16777216 at h
  have small : i.val/65536<2^64 := by omega
  refine ⟨sb.trans (sibling_ptr _ _ small),db.trans ?_,(block.regs .x24).trans cur⟩
  rw [show W (i.val/65536) >>> 1 = W (i.val/65536/2^1) from shr _ _ small,
    thirty _ (by omega)]
  unfold W; rw [←BitVec.ofNat_add]
  apply congrArg (BitVec.ofNat 64); unfold slotB; omega

theorem override_b (s : MachineState) {xs tree salts} (input : Sources s xs tree salts) (k : xs.length=128)
    (r : Nat) (lt : r<128) (pc : s.pc=pcAt 355) (f : ReverseFrameB s (r+1))
    (table : SlotsB s tree (xs.drop (r+1))) : OverrideResultB s xs tree r := by
  let i := ix xs r; let p := i.val/131072
  let a := Part.bOverrideSource.after s;let c := hcopy .override a;let u := Part.bReverseNext.after c
  have loc : s.getReg .x24+18446744073709551608=W (indexBase+8*r) := by rw [f.cursor,back8B]
  have head := block_result .bOverrideSource s pc (by
    intro e mem; change e∈[_] at mem; rcases List.mem_singleton.mp mem with rfl
    change accessValid ((s.getReg .x24+18446744073709551608)+0) 8=true
    rw [loc,show W (indexBase+8*r)+(0:Word)=W (indexBase+8*r) from BitVec.add_zero _]
    apply access_at <;> simp only [indexBase,MEMORY_BYTES] <;> omega)
  obtain ⟨sp,dp,idx⟩ := obtain_srcB s i r f (input.index r (by omega)) head
  have sb : p<128 := by have h:=i.isLt;change i.val<16777216 at h;unfold p;omega
  have mb := mate_bound i 16 (by decide)
  have nb := node_ok 16 (mate i 16) mb
  have sl := slotB_bounds (i.val/131072) sb
  have copied := hcopy_run .override a head.pc _ _ sp dp _ (by simp [bytes,HSite.count])
    (node_low_bytes a (input.same_mem head.mem) 16 (mate i 16) (by decide) mb) (by have := nb.2.2; omega) sl.2.2.1
    (by have := nb.2.1; unfold indexBase at this; unfold MEMORY_BYTES; simp only [HSite.count]; omega)
    (by simp only [HSite.count]; omega)
    (Or.inl (by have := nb.2.1; unfold indexBase at this; have := sl.2.2.2.2; unfold proofBase at this; simp only [HSite.count]; omega))
  have next := no_load .bReverseNext c copied.pc rfl
  have latch := test_run .bMoreOverrides u next.pc
  have reg (x : Reg) (ok : x≠.x6) (saved : Part.bOverrideSource.equation x=original x) :
      c.getReg x=s.getReg x := (copied.regs x ok).trans (head.keep x saved)
  have left := next.regs .x28
  change u.getReg .x28=c.getReg .x28+18446744073709551615 at left
  rw [reg _ (by decide) rfl,f.left,W,decrement (r+1) (by omega),Nat.add_sub_cancel] at left
  have take : Test.bMoreOverrides.taken u=decide (r≠0) := by
    change (u.getReg .x28 != 0)=_
    rw [left];exact count_test r (by omega)
  have endMem : (overrideB s).mem = c.mem := (test_mem _ u).trans next.mem
  have data := copied.data.congr_mem head.mem.symm endMem
  have save : BOut s (overrideB s) (slotB p) 30 := by simpa only [bytes,List.length_ofFn] using data.outside
  have keep (x : Reg) (ok : Part.bReverseNext.equation x=original x) :
      (overrideB s).getReg x = c.getReg x := MachineState.getReg_setPC.trans (next.keep x ok)
  refine ⟨((head.runs.trans copied.run).trans next.runs).trans latch,?_,
    ⟨(keep _ rfl).trans ((reg _ (by decide) rfl).trans f.output),
     (keep _ rfl).trans ((reg _ (by decide) rfl).trans f.nodes),
     (keep _ rfl).trans ((copied.regs _ (by decide)).trans idx),MachineState.getReg_setPC.trans left⟩,
    save.weaken _ _ sl.1 sl.2.1,?_⟩
  · change pcAt (if Test.bMoreOverrides.taken u then _ else _)=_
    rw [take];by_cases z:r=0 <;> simp [z,Test.target,Test.start]
  · intro q hq
    have hi : r<xs.length := by omega
    have drop : xs.drop r=i::xs.drop (r+1) := by
      rw [List.drop_eq_getElem_cons hi];simp only [i,ix,List.getElem?_eq_getElem hi,Option.getD_some]
    rw [drop];by_cases hit : q=p
    · subst q
      have eq : capSlot tree (i::xs.drop (r+1)) p=node tree 16 (mate i 16) := by simp [capSlot,p,mate,indexAbove]
      rw [eq];exact data.data
    · have ne : i.val/2^17≠q := Ne.symm hit
      have eq : capSlot tree (i::xs.drop (r+1)) q=capSlot tree (xs.drop (r+1)) q := by
        unfold capSlot;rw [List.find?_cons_of_neg (p:=fun z : Index => z.val/2^17 == q) (a:=i) (show ¬ ((i.val/2^17 == q)=true) from fun h => ne (beq_iff_eq.mp h))]
      rw [eq]
      apply (table q hq).frame save
      · simp only [bytes,List.length_ofFn]; exact (slotB_bounds q hq).2.2.2.1
      · simp only [bytes,List.length_ofFn,slotB]; omega

def reversePassB : Nat → MachineState → MachineState
  | 0,s => s | n+1,s => reversePassB n (overrideB s)

structure ReverseResultB (s : MachineState) (xs : List Index) (tree : Levels) (n : Nat) : Prop where
  run : Runs s (reversePassB n s) (45*n) (45*n)
  pc : (reversePassB n s).pc=pcAt 400
  outside : BOut s (reversePassB n s) capBaseB 3840
  table : SlotsB (reversePassB n s) tree xs

theorem reverse_b (s : MachineState) {xs tree salts} (input : Sources s xs tree salts) (card : xs.length=128)
    (n : Nat) (le : n≤128) (pc : s.pc=pcAt (if n=0 then 400 else 355)) (fr : ReverseFrameB s n)
    (table : SlotsB s tree (xs.drop n)) : ReverseResultB s xs tree n := by
  induction n generalizing s with
  | zero => exact ⟨Runs.refl _,pc,fun _ _ _ => rfl,table⟩
  | succ n ih =>
    have one := override_b s input card n (by omega) (by simpa only [Nat.succ_ne_zero,if_false] using pc) fr table
    have nextInput := input.afterB (by rw [card]; decide) capBaseB 3840 one.outside (by unfold capBaseB; omega)
    have rem := ih (overrideB s) nextInput (by omega) one.pc one.frame one.slots
    refine ⟨?_,rem.pc,one.outside.chain rem.outside,rem.table⟩
    simpa only [reversePassB,Nat.mul_succ,Nat.add_comm 45 (45*n)] using one.run.trans rem.run

private theorem slotsB_bytes (s : MachineState) (tree : Levels) (xs : List Index) (slots : SlotsB s tree xs)
    (n j : Nat) (bound : j+n≤128) :
    HasBytes s (slotB j) ((List.range' j n).flatMap fun p => bytes (n:=30) (low240 (capSlot tree xs p))) := by
  induction n generalizing j with
  | zero => intro k hk;simp at hk
  | succ n ih =>
    rw [List.range'_succ,List.flatMap_cons]
    apply HasBytes.append (slots j (by omega))
    have next : slotB j+(bytes (n:=30) (low240 (capSlot tree xs j))).length=slotB (j+1) := by simp [slotB,bytes];omega
    rw [next];exact ih (j+1) (by omega)

def capBytesB (tree : Levels) (xs : List Index) :=
  (List.range 128).flatMap fun p => bytes (n:=30) (low240 (capSlot tree xs p))

theorem capBytesB_len (tree : Levels) (xs : List Index) : (capBytesB tree xs).length = 3840 := by
  simp [capBytesB,List.length_flatMap,bytes,List.sum_replicate]

theorem slotsB_payload (s : MachineState) (tree : Levels) (xs : List Index) (h : SlotsB s tree xs) :
    HasBytes s capBaseB (capBytesB tree xs) := by
  simpa only [slotB,Nat.mul_zero,Nat.add_zero,capBytesB,List.range_eq_range'] using slotsB_bytes s tree xs h 128 0 (by decide)

def finalCapB (s : MachineState) :=
  reversePassB 128 (Part.bReverseStart.after (fillCapB 64 (Part.bCapStart.after s)))

structure CapResultB (s : MachineState) (xs : List Index) (tree : Levels) : Prop where
  run : Runs s (finalCapB s) 10008 10008
  pc : (finalCapB s).pc=pcAt 400
  bytes : BWritten s (finalCapB s) capBaseB (capBytesB tree xs)

theorem cap_b (s : MachineState) {xs tree salts} (src : Sources s xs tree salts) (card : xs.length=128)
    (pc : s.pc=pcAt 265) (dst : s.getReg .x25=W capBaseB) : CapResultB s xs tree := by
  let a := Part.bCapStart.after s
  let b := fillCapB 64 a
  let c := Part.bReverseStart.after b
  have ha := no_load .bCapStart s pc rfl
  have inputA := src.same_mem ha.mem
  have start : PairFrameB a 0 := ⟨ha.regs .x23,(ha.keep .x25 rfl).trans dst,ha.regs .x28⟩
  have size : xs.length≤LENGTH := by rw [card];decide
  have fill := fill_b a inputA size 64 0 (by decide) ha.pc start
  have hb : b.pc=pcAt 337 := fill.pc
  have out : BOut s b capBaseB 3840 := by
    have before : BOut s a capBaseB 3840 := BOut.of_mem ha.mem _ _
    exact before.chain (fill.outside.weaken _ _ (by unfold slotB; omega) (by unfold slotB; omega))
  have inputB := src.afterB size capBaseB 3840 out (by unfold capBaseB; omega)
  have setup := no_load .bReverseStart b hb rfl
  have inputC := inputB.same_mem setup.mem
  have fr : ReverseFrameB c 128 := ⟨setup.regs .x18,setup.regs .x19,setup.regs .x24,setup.regs .x28⟩
  have initialSlots : SlotsB c tree (xs.drop 128) := by
    rw [←card,List.drop_length]
    intro p hp
    have f := fill.slots p (by omega) hp
    change HasBytes c (slotB p) (bytes (n:=30) (low240 (node tree 17 p)))
    exact f.same_mem setup.mem
  have rev := reverse_b c inputC card 128 le_rfl setup.pc fr initialSlots
  refine ⟨((ha.runs.trans fill.run).trans setup.runs).trans rev.run,rev.pc,⟨?_,slotsB_payload _ tree xs rev.table⟩⟩
  have middle : BOut b c capBaseB 3840 := BOut.of_mem setup.mem _ _
  rw [capBytesB_len]
  exact (out.chain middle).chain rev.outside

end CommitGolfCandidate.Late.Open
