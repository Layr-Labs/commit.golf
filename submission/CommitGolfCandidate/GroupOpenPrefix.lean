import CommitGolfCandidate.GroupOpenWholeFlow

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open PackedOpening (ByteCopy)
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

def firstSource (i : Index) (b : Nat) : Nat :=
  if b<16 then nonceAddress i+b else
    leafAddress (i.val ^^^ ((b-16)/32+1)) + (b-16)%32

theorem first_source_before (i : Index) (b : Nat) (bound : b<112) : firstSource i b < proofBase := by
  unfold firstSource
  split
  · have ix := i.isLt
    have tail := nonces_end_at_indices
    have endIx := indices_before_records
    unfold nonceAddress
    omega
  · let j : Fin 3 := ⟨(b-16)/32,by omega⟩
    have before := (leaf_address_inside _ (sibling_in_message i j)).2.2
    have tail := nonces_end_at_indices
    have endIx := indices_before_records
    change leafAddress (i.val ^^^ ((b-16)/32+1))+32 ≤ nonceBase at before
    omega

theorem source_quartet (i : Index) (j : Fin 3) (b : Nat) (inside : b<32) :
    firstSource i (16+32*j.val+b) = leafAddress (i.val ^^^ (j.val+1))+b := by
  unfold firstSource
  rw [if_neg (by omega)]
  have q : (16+32*j.val+b-16)/32=j.val := by omega
  have r : (16+32*j.val+b-16)%32=b := by omega
  rw [q,r]

structure PrefixWrites (before after : MachineState) (i : Index) (ordinal first last : Nat) : Prop where
  bytes : ∀ b, first ≤ b → b<last → after.getByte (BitVec.ofNat 64 (recordBase ordinal+b)) =
    before.getByte (BitVec.ofNat 64 (firstSource i b))
  frame : ∀ a, a<2^64 → a<recordBase ordinal+first ∨ recordBase ordinal+last≤a →
    after.getByte (BitVec.ofNat 64 a) = before.getByte (BitVec.ofNat 64 a)
  input : ∀ a<proofBase, after.getMem (BitVec.ofNat 64 a) = before.getMem (BitVec.ofNat 64 a)

theorem PrefixWrites.of_copy {s u : MachineState} {i : Index} {ordinal first count src : Nat}
    (copy : ByteCopy s u src (recordBase ordinal+first) count)
    (fits : recordBase ordinal+first+count ≤ MEMORY_BYTES)
    (source : ∀ b, b<count → firstSource i (first+b) = src+b)
    (input : ∀ a<proofBase, u.getMem (BitVec.ofNat 64 a)=s.getMem (BitVec.ofNat 64 a)) :
    PrefixWrites s u i ordinal first (first+count) := by
  constructor
  · intro b lo hi
    have add : first+(b-first)=b := by omega
    have matchSource := source (b-first) (by omega)
    rw [add] at matchSource
    rw [matchSource]
    simpa only [Nat.add_assoc,add] using copy.copied (b-first) (by omega)
  · intro a valid outside
    have ram : MEMORY_BYTES<2^64 := by decide
    exact field_outside copy a valid (by omega) (by simpa only [Nat.add_assoc] using outside)
  · exact input

theorem PrefixWrites.join {s u v : MachineState} {i : Index} {o a b c : Nat}
    (left : PrefixWrites s u i o a b) (right : PrefixWrites u v i o b c)
    (ends : c ≤ 112) (fit : o<LENGTH) (order : a ≤ b ∧ b ≤ c := by omega) :
    PrefixWrites s v i o a c := by
  have ram : MEMORY_BYTES < 2^64 := by decide
  have last := all_record_ends_fit o fit
  have endBytes : recordBase (o+1) = recordBase o+534 := by
    unfold recordBase recordBytes; omega
  have base : proofBase ≤ recordBase o := by unfold recordBase; omega
  constructor
  · intro j lo hi
    by_cases old : j<b
    · exact (right.frame _ (by omega) (Or.inl (by omega))).trans (left.bytes j lo old)
    · exact (right.bytes j (by omega) hi).trans (left.frame _ (by
        have z := first_source_before i j (by omega); omega) (Or.inl (by
        have z := first_source_before i j (by omega); omega)))
  · intro address valid outside
    exact (right.frame _ valid (outside.imp (by omega) id)).trans
        (left.frame _ valid (outside.imp id (by omega)))
  · intro address below
    exact (right.input _ below).trans (left.input _ below)

theorem PrefixWrites.move {s u s' u' : MachineState} {i : Index} {o a b : Nat}
    (writes : PrefixWrites s u i o a b) (initial : s'.mem=s.mem) (final : u'.mem=u.mem) :
    PrefixWrites s' u' i o a b := by
  constructor
  · intro j lo hi
    simpa only [MachineState.getByte,MachineState.getMem,initial,final] using writes.bytes j lo hi
  · intro j fit outside
    simpa only [MachineState.getByte,MachineState.getMem,initial,final] using writes.frame j fit outside
  · intro j below
    simpa only [MachineState.getMem,initial,final] using writes.input j below

def prefixScratch : List Reg := [.x6,.x7,.x10,.x21,.x28,.x29,.x31]

def Keeps (s u : MachineState) : Prop := ∀ r, r ∉ prefixScratch → u.getReg r=s.getReg r

theorem Keeps.next {s u v : MachineState} (head : Keeps s u) (tail : Keeps u v) : Keeps s v :=
  fun r hr => (tail r hr).trans (head r hr)

structure PrefixStart (s : MachineState) (i : Index) (o : Nat) : Prop where
  pc : s.pc=Whole.setupPC o
  heap : s.getReg .x9=BitVec.ofNat 64 trapdoorBase
  slots : s.getReg .x24=BitVec.ofNat 64 groupSlots
  nonce : s.getReg .x22=BitVec.ofNat 64 nonceBase
  groups : s.getReg .x19=BitVec.ofNat 64 4194304
  output : s.getReg .x21=BitVec.ofNat 64 (recordBase o)
  index : s.getMem (s.getReg .x8)=BitVec.ofNat 64 i.val
  readable : accessValid (s.getReg .x8) 8 = true

open Whole (pcAt)

structure GroupCursor (s : MachineState) (i : Index) (o j : Nat) : Prop where
  pc : s.pc=pcAt (Whole.row (Whole.pageClass o) (2+j))
  heap : s.getReg .x9=BitVec.ofNat 64 trapdoorBase
  groups : s.getReg .x19=BitVec.ofNat 64 4194304
  group : s.getReg .x7=BitVec.ofNat 64 (groupSlots+1024*(i.val/4)+584)
  low : s.getReg .x10=BitVec.ofNat 64 (i.val%4)
  index : s.getReg .x6=BitVec.ofNat 64 i.val
  output : s.getReg .x21=BitVec.ofNat 64 (recordBase o)

theorem Whole.beforeProof {s u : MachineState} {S T n cost word : Nat}
    (d : CapCopy.Done s u S T n cost word) (a : Nat) (low : a<proofBase) (bound : proofBase≤T) :
    u.getMem (BitVec.ofNat 64 a)=s.getMem (BitVec.ofNat 64 a) := by
  apply d.below
  have al : proofBase%8=0 := by decide
  rw [BitVec.toNat_ofNat]; have := Nat.mod_le a (2^64);omega

def saltStart (c : Nat) (s : MachineState) := Whole.fixedSlot (Whole.copy c 0 (Whole.dispatch (nonceSetup s)))

theorem run_salt_start (s : MachineState) (i : Index) (o : Nat) (fit : o<LENGTH) (start : PrefixStart s i o) :
    let c := Whole.pageClass o
    let u := saltStart c s
    RunsOpeningBlock s u ((3+Whole.firstCost o)+(Whole.row c 2-Whole.row c 0)) ∧ GroupCursor u i o 0 ∧
      PrefixWrites s u i o 0 16 ∧ Keeps s u := by
  let c : Fin 4 := ⟨Whole.pageClass o,Whole.class_lt o⟩
  let n := nonceSetup s
  let t := Whole.dispatch n
  let v := Whole.copy c 0 t
  have h:=nonce_setup_post s
  have z:=Whole.fixedSlot_post v
  have shape:=Whole.prefix_layout c
  obtain ⟨_,_,apart,room⟩ := all_nonce_copies_fit i o fit
  have sa : nonceAddress i%8=0 := by
    have a : nonceBase%8=0 := by decide
    unfold nonceAddress;omega
  have output : n.getReg .x21=BitVec.ofNat 64 (recordBase o) := (h.2.2.2.2 _ (by decide) (by decide)).trans start.output
  obtain ⟨entered,pcT,memT,keepT⟩:=Whole.enter_run s o start.pc start.readable
  have rr : recordBase o%8=Whole.destResidue c 0 := by
    rw [Whole.class_residue o]; change 2*c.val = (2*c.val+0)%8
    have := c.isLt;omega
  have field:=Whole.field_copy c 0 t (nonceAddress i) (recordBase o) pcT
    ((keepT _ (by decide) (by decide)).trans (physical_nonce_source s i start.nonce start.index))
    (by change t.getReg .x21+BitVec.ofNat 64 0=_;rw [show t.getReg .x21=_ from keepT .x21 (by decide) (by decide),output,←BitVec.ofNat_add];rfl)
    sa rr apart room
  have fieldPC : v.pc=pcAt (Whole.row c 1) := by rw [←shape.1];exact field.pc
  have rd : v.getReg .x6=BitVec.ofNat 64 i.val := (field.regs _ (by decide)).trans
    ((keepT _ (by decide) (by decide)).trans (h.2.2.2.1.trans start.index))
  have fixed (r : Reg) (a : r≠.x31) (b : r≠.x29) (cc : r≠.x6) (d : r≠.x7) : v.getReg r=s.getReg r :=
    (field.regs r a).trans ((keepT r a b).trans (h.2.2.2.2 r cc d))
  have stable : Keeps s (Whole.fixedSlot v) := by
    intro r free
    apply (z.2.2.2.2.2 r ?_ ?_ ?_).trans (fixed r ?_ ?_ ?_ ?_)
    all_goals intro e;subst r; simp [prefixScratch] at free
  have sourceBytes : PrefixWrites t v i o 0 16 := by
    apply PrefixWrites.of_copy (src:=nonceAddress i) (count:=16) field.bytes (by simpa using room)
    · intro b hb; simp [firstSource,hb]
    · intro a ha;exact Whole.beforeProof field a ha (by unfold recordBase;omega)
  have total := (entered.next field.run).next (Whole.slot_run c v fieldPC)
  have price : ∀ a : Fin 4, (Whole.shape a 0).cycles+5=Whole.row a 2-Whole.row a 0 := by decide
  change RunsOpeningBlock s (Whole.fixedSlot v) ((3+Whole.firstCost o)+(Whole.shape c 0).cycles+5) at total
  rw [Nat.add_assoc,price c] at total
  refine ⟨total,⟨?_,(stable .x9 (by decide)).trans start.heap,(stable .x19 (by decide)).trans start.groups,
    ?_,?_,?_,?_⟩,sourceBytes.move (memT.trans h.2.1).symm z.2.1,stable⟩
  · change (Whole.fixedSlot v).pc=_
    rw [z.1,fieldPC]; exact (ofNat_step _ 5).trans (congrArg pcAt shape.2.1)
  · change (Whole.fixedSlot v).getReg .x7=_
    rw [show (Whole.fixedSlot v).getReg .x7=_ from z.2.2.2.1,rd,masked_group,
      (fixed .x24 (by decide) (by decide) (by decide) (by decide)),start.slots,←BitVec.ofNat_add]
    change BitVec.ofNat 64 (1024*(i.val/4)+groupSlots)+BitVec.ofNat 64 584=_
    rw [←BitVec.ofNat_add,Nat.add_comm (1024*(i.val/4))]
  · change (Whole.fixedSlot v).getReg .x10=_
    rw [show (Whole.fixedSlot v).getReg .x10=_ from z.2.2.2.2.1,rd,low_selector]
  · exact (z.2.2.2.2.2 _ (by decide) (by decide) (by decide)).trans rd
  · change (Whole.fixedSlot v).getReg .x21=_
    have dv : v.getReg .x21=BitVec.ofNat 64 (recordBase o) :=
      (field.regs _ (by decide)).trans ((keepT _ (by decide) (by decide)).trans output)
    exact z.2.2.1.trans dv

def groupStep (c : Nat) (j : Fin 3) (s : MachineState) := Whole.copy c (1+j.val) (quartetHead j s)

theorem run_group_step (s : MachineState) (i : Index) (o : Nat) (j : Fin 3) (fit : o<LENGTH)
    (start : GroupCursor s i o j.val) :
    let c:=Whole.pageClass o
    let u:=groupStep c j s
    RunsOpeningBlock s u (Whole.row c (3+j.val)-Whole.row c (2+j.val)) ∧ GroupCursor u i o (j.val+1) ∧
      PrefixWrites s u i o (16+32*j.val) (16+32*j.val+32) ∧ Keeps s u := by
  let c : Fin 4 := ⟨Whole.pageClass o,Whole.class_lt o⟩
  let f : Fin 18 := ⟨1+j.val,by have:=j.isLt;omega⟩
  let t:=quartetHead j s
  let S:=leafAddress (i.val ^^^ (j.val+1))
  let T:=recordBase o+(16+32*j.val)
  have head:=quartet_head_post j s
  have bounds:=leaf_address_inside _ (sibling_in_message i j)
  have endRec:=all_record_ends_fit o fit
  have endIx:=indices_before_records
  have endSalt:=nonces_end_at_indices
  have small:=j.isLt
  have room : T+32≤MEMORY_BYTES := by unfold T recordBase recordBytes at *;omega
  have srcBound : S+32≤nonceBase := bounds.2.2
  have apart : S+32≤T := by unfold T recordBase;omega
  have specs : Whole.source f=.x28 ∧ Whole.offset f=16+32*j.val ∧ Whole.width f=32 ∧ Whole.destResidue c f=2*c.val := by
    have tab : ∀ a : Fin 4, ∀ j : Fin 3, Whole.source (1+j.val)=.x28 ∧ Whole.offset (1+j.val)=16+32*j.val ∧
      Whole.width (1+j.val)=32 ∧ Whole.destResidue a (1+j.val)=2*a.val := by decide
    exact tab c j
  have pos:=(Whole.prefix_layout c).2.2.2.2.2 j
  have pc : t.pc=pcAt (Whole.rawStart c f) := by
    rw [show t.pc=_ from head.1,start.pc,pos.1];exact ofNat_step _ 3
  have src : t.getReg (Whole.source f)=BitVec.ofNat 64 S := by
    rw [specs.1];exact quartet_physical_source s i j start.group start.low
  have dst : t.getReg .x21+BitVec.ofNat 64 (Whole.offset f)=BitVec.ofNat 64 T := by
    rw [specs.2.1,head.2.2.2 .x21 (by decide),start.output,←BitVec.ofNat_add]
  have rr : T%8=Whole.destResidue c f := by
    rw [specs.2.2.2];have q:=Whole.class_residue o;unfold T;change _=2*Whole.pageClass o;omega
  have copy:=Whole.field_copy c f t S T pc src dst bounds.1 rr (specs.2.2.1 ▸ apart) (specs.2.2.1 ▸ room)
  have headRun:=Whole.mate_run c j s start.pc
  have stable (r : Reg) (a : r≠.x31) (b : r≠.x28) :
      (groupStep c j s).getReg r=s.getReg r := (copy.regs r a).trans (head.2.2.2 r b)
  have writes : PrefixWrites t (groupStep c j s) i o (16+32*j.val) (16+32*j.val+32) := by
    apply PrefixWrites.of_copy (src:=S) (count:=32) (by have bb:=copy.bytes;rw [specs.2.2.1] at bb;exact bb) room (source_quartet i j)
    intro a ha; exact Whole.beforeProof copy a ha (by unfold T recordBase;omega)
  have total:=headRun.next copy.run
  have eq : 3+(Whole.shape c f).cycles = Whole.row c (3+j.val)-Whole.row c (2+j.val) := by
    change 3+(Whole.shape c (1+j.val)).cycles=_
    omega
  rw [eq] at total
  refine ⟨total, ⟨?_,(stable _ (by decide) (by decide)).trans start.heap,(stable _ (by decide) (by decide)).trans start.groups,
    (stable _ (by decide) (by decide)).trans start.group,(stable _ (by decide) (by decide)).trans start.low,
    (stable _ (by decide) (by decide)).trans start.index,(stable _ (by decide) (by decide)).trans start.output⟩,
    writes.move head.2.1.symm rfl,?_⟩
  · change (groupStep c j s).pc=_
    have dstpc:=copy.pc
    rw [show Whole.rawStart c f+(Whole.shape c f).cycles = _ from pos.2.1] at dstpc
    exact dstpc.trans (congrArg (fun q => pcAt (Whole.row c q)) (by omega))
  · intro r free
    apply stable r <;> intro e <;> subst r <;> simp [prefixScratch] at free

def recordPrefix (c : Nat) (s : MachineState) :=
  Whole.preload (Whole.fixedExit (groupStep c 2 (groupStep c 1 (groupStep c 0 (saltStart c s)))))

structure WholeCursor (s : MachineState) (i : Index) (o l : Nat) : Prop where
  pc : s.pc=(if l=14 then pcAt (Whole.row (Whole.pageClass o) 22) else pcAt (Whole.row (Whole.pageClass o) (7+l)))
  heap : s.getReg .x9=BitVec.ofNat 64 trapdoorBase
  node : s.getReg .x6=BitVec.ofNat 64 (upperNode i l)
  dest : s.getReg .x21=BitVec.ofNat 64 (recordBase o + (if l=14 then 534 else 0))

theorem execute_record_prefix (s : MachineState) (i : Index) (o : Nat) (fit : o<LENGTH) (start : PrefixStart s i o) :
    let c:=Whole.pageClass o
    let u:=recordPrefix c s
    RunsOpeningBlock s u ((3+Whole.firstCost o)+(Whole.row c 7-Whole.row c 0)) ∧ WholeCursor u i o 0 ∧
      PrefixWrites s u i o 0 112 ∧ Keeps s u ∧
      u.getReg .x7=BitVec.ofNat 64 (groupSlots+1024*(i.val/4)+584) ∧
      u.getReg .x10=(u.getHalfword (BitVec.ofNat 64 (siblingAddress i 13+28))).zeroExtend 64 := by
  let c : Fin 4 := ⟨Whole.pageClass o,Whole.class_lt o⟩
  have ⟨salt,g0,w0,k0⟩ := run_salt_start s i o fit start
  have ⟨s0,g1,w1,k1⟩ := run_group_step _ i o 0 fit g0
  have ⟨s1,g2,w2,k2⟩ := run_group_step _ i o 1 fit g1
  have ⟨s2,g3,w3,k3⟩ := run_group_step _ i o 2 fit g2
  let last:=groupStep c 2 (groupStep c 1 (groupStep c 0 (saltStart c s)))
  let ex:=Whole.fixedExit last
  have e:=Whole.fixedExit_post last
  have past : Keeps s last := ((k0.next k1).next k2).next k3
  have kept : Keeps last ex := by
    intro r free;apply e.2.2.2.2 <;> intro h <;> subst r <;> simp [prefixScratch] at free
  have writes : PrefixWrites s last i o 0 112 := ((w0.join w1 (by decide) fit).join w2 (by decide) fit).join w3 (by decide) fit
  have pos:=Whole.prefix_layout c
  have atExit : last.pc=pcAt (Whole.row c 5) := g3.pc
  have pcEx : ex.pc=pcAt (Whole.row c 6) := by
    rw [show ex.pc=_ from e.1,atExit];exact (ofNat_step _ 2).trans (congrArg pcAt pos.2.2.1)
  have heap : ex.getReg .x9=BitVec.ofNat 64 trapdoorBase := (kept _ (by decide)).trans g3.heap
  have node : ex.getReg .x6=BitVec.ofNat 64 (upperNode i 0) := by
    rw [show ex.getReg .x6=_ from e.2.2.2.1,show last.getReg .x6=_ from g3.index,quarter_shift,
      show last.getReg .x19=_ from g3.groups,←BitVec.ofNat_add,upper_node_zero,Nat.add_comm]
  obtain ⟨top,pcEnd,memEnd,loaded,regEnd⟩:=Whole.preload_run c ex i pcEx heap node
  have finalKeep : Keeps ex (Whole.preload ex) := by
    intro r free;apply regEnd <;> intro h <;> subst r <;> simp [prefixScratch] at free
  have all := (((((salt.next s0).next s1).next s2).next (Whole.exit_run c last atExit)).next top)
  have price : ∀ c : Fin 4, (Whole.row c 2-Whole.row c 0)+(Whole.row c 3-Whole.row c 2)+
      (Whole.row c 4-Whole.row c 3)+(Whole.row c 5-Whole.row c 4)+2+5=Whole.row c 7-Whole.row c 0 := by decide
  let initCost:=3+Whole.firstCost o
  change RunsOpeningBlock s (recordPrefix c s) (initCost+(Whole.row c 2-Whole.row c 0)+(Whole.row c 3-Whole.row c 2)+(Whole.row c 4-Whole.row c 3)+(Whole.row c 5-Whole.row c 4)+2+5) at all
  have p:=price c
  rw [show initCost+(Whole.row c 2-Whole.row c 0)+(Whole.row c 3-Whole.row c 2)+(Whole.row c 4-Whole.row c 3)+(Whole.row c 5-Whole.row c 4)+2+5=initCost+(Whole.row c 7-Whole.row c 0) by omega] at all
  refine ⟨all,⟨pcEnd,(regEnd _ (by decide) (by decide)).trans heap,(regEnd _ (by decide) (by decide)).trans node,?_⟩,
    writes.move rfl (memEnd.trans e.2.1), (past.next kept).next finalKeep,
    (regEnd _ (by decide) (by decide)).trans ((e.2.2.2.2 _ (by decide) (by decide)).trans g3.group),?_⟩
  · exact (regEnd .x21 (by decide) (by decide)).trans (e.2.2.1.trans g3.output)
  · change (Whole.preload ex).getReg .x10=_
    exact loaded.trans (congrArg (BitVec.zeroExtend 64) (get_half_congr memEnd _).symm)

end TwoPermutationPrototype.GroupedOpening
