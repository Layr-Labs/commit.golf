import CommitGolfCandidate.GroupOpenStep

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.Grouped (msgWord saltHead sliceByte)
open CommitGolfCandidate.Permutation.CounterSalt (coord)
set_option maxRecDepth 22000
set_option maxHeartbeats 1800000
attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC pc_of_set mem_of_set mem_of_reg open_zero
attribute [local irreducible] wordAddress

theorem place_spec (s v : MachineState) (i : Index) (pt : Point s v 750)
    (v6 : v.getReg .x6=BitVec.ofNat 64 i.val) (v28 : v.getReg .x28=BitVec.ofNat 64 (loopHead i.val))
    (v30 : v.getReg .x30=BitVec.ofNat 64 (i.val%2)) :
    let w:=walkRows v placeRows
    legal placeRows v ∧ Point s w 761 ∧ w.getReg .x6=BitVec.ofNat 64 i.val ∧
      w.getReg .x28=BitVec.ofNat 64 (loopHead i.val) ∧ w.getReg .x31=BitVec.ofNat 64 (184*(i.val%2)) := by
  refine ⟨⟨pt.pc,rfl,?_,rfl,?_,rfl,trivial⟩,⟨?_,?_,?_⟩,?_,?_,?_⟩
  · simp [execInstrBr,pt.pc,address]
  · simp [execInstrBr,pt.pc,address]
  · simp [walkRows,placeRows,execInstrBr,pt.pc,address];decide
  · simp [walkRows,placeRows,execInstrBr,pt.mem]
  · intro k ⟨a,b,c,d,e⟩;simp [walkRows,placeRows,execInstrBr,Ne.symm e];exact pt.keep k ⟨a,b,c,d,e⟩
  · simp [walkRows,placeRows,execInstrBr,v6]
  · simp [walkRows,placeRows,execInstrBr,v28]
  · simp [walkRows,placeRows,execInstrBr,v30,show signExtend12 184#12=184#64 by decide]
    exact place_word _ (by omega)

def offsetOps : List Row := [(753,.SLLI .x31 .x7 5),(754,.SLLI .x30 .x30 4),(755,.ADD .x31 .x31 .x30),
  (756,.ADDI .x31 .x31 (-16)),(757,.ADDI .x30 .x0 160)]
theorem offset_parts : offsetRows=offsetOps++[(758,.BNE .x31 .x30 12)] := rfl

theorem offset_legal (s v : MachineState) (pt : Point s v 753) : legal offsetRows v := by
  refine ⟨pt.pc,rfl,?_,rfl,?_,rfl,?_,rfl,?_,rfl,?_,rfl,trivial⟩
  all_goals simp [execInstrBr,pt.pc,address]

theorem offset_x31 (v : MachineState) (i : Index) (k0 : loopK i.val≠0) (v7 : v.getReg .x7=BitVec.ofNat 64 (loopK i.val))
    (v30 : v.getReg .x30=BitVec.ofNat 64 (i.val%2)) :
    (walkRows v offsetOps).getReg .x31=BitVec.ofNat 64 (copyOff i.val) := by
  have kb := loop_k_lt i.val
  simp [walkRows,offsetOps,execInstrBr,v7,v30]
  rw [shl_word,shl_word,add_word,minus_word _ 16 (by omega) (by omega) _ (by decide)];unfold copyOff
  exact congrArg (BitVec.ofNat 64) (by omega)

theorem offset_x30 (v : MachineState) : (walkRows v offsetOps).getReg .x30=BitVec.ofNat 64 160 := by
  simp [walkRows,offsetOps,execInstrBr];decide

theorem offset_walk (v : MachineState) : walkRows v offsetRows=execInstrBr (walkRows v offsetOps) (.BNE .x31 .x30 12) := by
  rw [offset_parts,walk_join,single_walk]

theorem offset_pc (s v : MachineState) (i : Index) (pt : Point s v 753) (k0 : loopK i.val≠0)
    (v7 : v.getReg .x7=BitVec.ofNat 64 (loopK i.val)) (v30 : v.getReg .x30=BitVec.ofNat 64 (i.val%2)) :
    (walkRows v offsetRows).pc=address (if copyOff i.val=160 then 759 else 761) := by
  have kb := loop_k_lt i.val
  have p0 : (walkRows v offsetOps).pc=address 758 := by
    simp only [walkRows,offsetOps,List.foldl_cons,List.foldl_nil,execInstrBr,pc_of_set,pt.pc];unfold address;simp
  rw [offset_walk,bne_form];simp only [pc_of_set]
  rw [offset_x31 v i k0 v7 v30,offset_x30 v,p0,bne_word _ _ (by unfold copyOff;omega) (by decide)]
  by_cases c : copyOff i.val=160 <;> simp only [c,decide_true,decide_false,Bool.not_true,Bool.not_false,ite_true,ite_false,
    Bool.false_eq_true] <;> decide

theorem offset_ops_keep (v : MachineState) (k : Reg) (d : k≠.x30) (e : k≠.x31) :
    (walkRows v offsetOps).getReg k=v.getReg k := by
  simp [walkRows,offsetOps,execInstrBr,Ne.symm d,Ne.symm e]

theorem offset_ops_mem (v : MachineState) : (walkRows v offsetOps).mem=v.mem := by
  simp [walkRows,offsetOps,execInstrBr]

theorem offset_spec (s v : MachineState) (i : Index) (pt : Point s v 753) (k0 : loopK i.val≠0)
    (v6 : v.getReg .x6=BitVec.ofNat 64 i.val) (v7 : v.getReg .x7=BitVec.ofNat 64 (loopK i.val))
    (v28 : v.getReg .x28=BitVec.ofNat 64 (loopHead i.val)) (v30 : v.getReg .x30=BitVec.ofNat 64 (i.val%2)) :
    legal offsetRows v ∧ Point s (walkRows v offsetRows) (if copyOff i.val=160 then 759 else 761) ∧
      (walkRows v offsetRows).getReg .x6=BitVec.ofNat 64 i.val ∧
      (walkRows v offsetRows).getReg .x28=BitVec.ofNat 64 (loopHead i.val) ∧
      (walkRows v offsetRows).getReg .x31=BitVec.ofNat 64 (copyOff i.val) := by
  have set (r : Reg) : (walkRows v offsetRows).getReg r=(walkRows v offsetOps).getReg r := by
    rw [offset_walk,bne_form,MachineState.getReg_setPC]
  refine ⟨offset_legal s v pt,⟨offset_pc s v i pt k0 v7 v30,?_,?_⟩,?_,?_,?_⟩
  · rw [offset_walk,bne_form,mem_of_set,offset_ops_mem];exact pt.mem
  · intro k ck;rw [set,offset_ops_keep v k ck.2.2.2.1 ck.2.2.2.2];exact pt.keep k ck
  · rw [set,offset_ops_keep v _ (by decide) (by decide)];exact v6
  · rw [set,offset_ops_keep v _ (by decide) (by decide)];exact v28
  · rw [set];exact offset_x31 v i k0 v7 v30

theorem twelfth_spec (s w : MachineState) (i : Index) (pt : Point s w 759) (k0 : loopK i.val≠0) (t : copyOff i.val=160)
    (v6 : w.getReg .x6=BitVec.ofNat 64 i.val) (v28 : w.getReg .x28=BitVec.ofNat 64 (loopHead i.val)) :
    let x:=walkRows w (twelfthRows true)
    legal (twelfthRows true) w ∧ Point s x 761 ∧ x.getReg .x6=BitVec.ofNat 64 i.val ∧
      x.getReg .x28=BitVec.ofNat 64 (loopHead i.val-5) ∧ x.getReg .x31=BitVec.ofNat 64 144 := by
  have hb := twelfth_head i.val k0 t
  have hi : i.val<16777216 := i.isLt
  have hl : loopHead i.val ≤ i.val := by unfold loopHead;omega
  refine ⟨⟨pt.pc,rfl,?_,rfl,trivial⟩,⟨?_,?_,?_⟩,?_,?_,?_⟩
  · simp [twelfthRows,execInstrBr,pt.pc,address]
  · simp [walkRows,twelfthRows,execInstrBr,pt.pc,address]
  · simp [walkRows,twelfthRows,execInstrBr,pt.mem]
  · intro k ⟨a,b,c,d,e⟩;simp [walkRows,twelfthRows,execInstrBr,Ne.symm c,Ne.symm e];exact pt.keep k ⟨a,b,c,d,e⟩
  · simp [walkRows,twelfthRows,execInstrBr,v6]
  · simp [walkRows,twelfthRows,execInstrBr,v28];exact minus_word _ 5 (by omega) hb _ (by decide)
  · simp [walkRows,twelfthRows,execInstrBr];decide

theorem slot_spec (s v : MachineState) (i : Index) (pt : Point s v (if loopK i.val=0 then 750 else 753))
    (v6 : v.getReg .x6=BitVec.ofNat 64 i.val) (v7 : v.getReg .x7=BitVec.ofNat 64 (loopK i.val))
    (v28 : v.getReg .x28=BitVec.ofNat 64 (loopHead i.val)) (v30 : v.getReg .x30=BitVec.ofNat 64 (i.val%2)) :
    let w:=walkRows v (slotRows (inPlace i.val) (twelfth i.val))
    legal (slotRows (inPlace i.val) (twelfth i.val)) v ∧ Point s w 761 ∧ w.getReg .x6=BitVec.ofNat 64 i.val ∧
      w.getReg .x28=BitVec.ofNat 64 (loopOut i.val).1 ∧ w.getReg .x31=BitVec.ofNat 64 (loopOut i.val).2 := by
  by_cases z : loopK i.val=0
  · rw [if_pos z] at pt
    have ip : inPlace i.val=true := by simp [inPlace,z]
    rw [ip];simp only [slotRows,ite_true]
    obtain ⟨l,p,a,b,c⟩:=place_spec s v i pt v6 v28 v30
    refine ⟨l,p,a,?_,?_⟩
    · rw [b];unfold loopOut;rw [if_pos z]
    · rw [c];unfold loopOut;rw [if_pos z]
  · rw [if_neg z] at pt
    have ip : inPlace i.val=false := by simp [inPlace,z]
    rw [ip];simp only [slotRows,Bool.false_eq_true,ite_false]
    obtain ⟨l,p,a,b,c⟩:=offset_spec s v i pt z v6 v7 v28 v30
    by_cases t : copyOff i.val=160
    · have tw : twelfth i.val=true := by simp [twelfth,t]
      rw [if_pos t] at p;rw [tw,walk_join]
      obtain ⟨l2,p2,a2,b2,c2⟩:=twelfth_spec s _ i p z t a b
      refine ⟨legal_append _ _ _ l l2,p2,a2,?_,?_⟩
      · rw [b2];unfold loopOut;rw [if_neg z,if_pos t]
      · rw [c2];unfold loopOut;rw [if_neg z,if_pos t]
    · have tw : twelfth i.val=false := by simp [twelfth,t]
      rw [if_neg t] at p;rw [tw];simp only [twelfthRows,Bool.false_eq_true,ite_false,List.append_nil]
      refine ⟨l,p,a,?_,?_⟩
      · rw [b];unfold loopOut;rw [if_neg z,if_neg t]
      · rw [c];unfold loopOut;rw [if_neg z,if_neg t]

theorem counter_spec (s w : MachineState) (pt : Point s w 761) (h : Nat) (hb : h<2^40)
    (v28 : w.getReg .x28=BitVec.ofNat 64 h) (input : s.getReg .x10=1024) (base : s.getReg .x26=4096) :
    let z:=walkRows w counterRows
    legal counterRows w ∧ z.pc=address 765 ∧ z.mem=(s.setMem 1024 (BitVec.ofNat 64 (512*h+4352))).mem ∧
      (∀ k, k≠.x28 → z.getReg k=w.getReg k) := by
  have i10 : w.getReg .x10=1024 := (pt.keep _ (by unfold Clob;decide)).trans input
  have i26 : w.getReg .x26=4096 := (pt.keep _ (by unfold Clob;decide)).trans base
  have val : ((BitVec.ofNat 64 h) <<< (9 : Nat))+4096#64+signExtend12 256#12=BitVec.ofNat 64 (512*h+4352) := by
    rw [shl_word,show signExtend12 256#12=BitVec.ofNat 64 256 by decide,show 4096#64=BitVec.ofNat 64 4096 from rfl,add_word,
      add_word];congr 1;omega
  refine ⟨⟨pt.pc,rfl,?_,rfl,?_,rfl,?_,?_,trivial⟩,?_,?_,?_⟩
  · simp [execInstrBr,pt.pc,address]
  · simp [execInstrBr,pt.pc,address]
  · simp [execInstrBr,pt.pc,address]
  · rw [ord_iff _ _ rfl];simp [memoryArgumentsValid,memAccess,execInstrBr,i10,show signExtend12 0#12=0#64 by decide]
    exact (by decide : accessValid (1024#64) 8=true)
  · simp [walkRows,counterRows,execInstrBr,pt.pc,address]
  · simp [walkRows,counterRows,execInstrBr,i10,i26,v28,pt.mem,show signExtend12 0#12=0#64 by decide]
    rw [val];simp only [mem_of_store,mem_of_set,mem_of_reg,pt.mem]
  · intro k e;simp [walkRows,counterRows,execInstrBr,Ne.symm e]

/-! ### The whole pre-call walk (words 739-764) -/

def preFor (i : Index) := preRows (groupB i.val) (inPlace i.val) (twelfth i.val)
def beforeCall (s : MachineState) (i : Index) := walkRows s (preFor i)

theorem loop_out_fst_le (i : Nat) : (loopOut i).1 ≤ i/2 := by
  have := loop_k_le i
  unfold loopOut loopHead;split
  · simp only;omega
  · split <;> simp only <;> omega

theorem ctr_value (i : Index) : BitVec.ofNat 64 (512*(loopOut i.val).1+4352)=ctrAt i := by
  rw [loop_out_eq i.val i.isLt];unfold ctrAt wordAddress msgWord
  exact congrArg (BitVec.ofNat 64) (by simp only;omega)

theorem off_value (i : Index) : (loopOut i.val).2=offAt i := by
  rw [loop_out_eq i.val i.isLt];rfl

theorem pre_spec (s : MachineState) (i : Index) (ord left : Nat) (r : Input s i ord left) :
    legal (preFor i) s ∧ (beforeCall s i).pc=address 765 ∧ (beforeCall s i).getReg .x6=BitVec.ofNat 64 i.val ∧
      (beforeCall s i).getReg .x31=BitVec.ofNat 64 (offAt i) ∧ (beforeCall s i).mem=(s.setMem 1024 (ctrAt i)).mem ∧
      (∀ k, Clob k → (beforeCall s i).getReg k=s.getReg k) := by
  have hi : i.val<16777216 := i.isLt
  obtain ⟨l1,p1,a1,b1,c1⟩ := head_spec s i ord left r
  obtain ⟨l2,p2,a2,b2,c2⟩ := group_spec s _ i p1 a1 b1 c1
  obtain ⟨l3,p3,a3,b3,c3,d3⟩ := parity_spec s _ i p2 a2 b2 c2
  obtain ⟨l4,p4,a4,b4,c4⟩ := slot_spec s _ i p3 a3 b3 c3 d3
  have hb : (loopOut i.val).1<2^40 := by have := loop_out_fst_le i.val;omega
  obtain ⟨l5,pc5,m5,k5⟩ := counter_spec s _ p4 _ hb b4 r.input r.base
  have walk : beforeCall s i=walkRows (walkRows (walkRows (walkRows (walkRows s headRows) (groupRows (groupB i.val)))
      parityRows) (slotRows (inPlace i.val) (twelfth i.val))) counterRows := by
    unfold beforeCall preFor preRows;simp only [walk_join]
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · unfold preFor preRows
    have L1 := legal_append _ _ _ l1 l2
    have L2 := legal_append _ _ _ L1 (by simp only [walk_join];exact l3)
    have L3 := legal_append _ _ _ L2 (by simp only [walk_join];exact l4)
    exact legal_append _ _ _ L3 (by simp only [walk_join];exact l5)
  · rw [walk];exact pc5
  · rw [walk,k5 _ (by decide)];exact a4
  · rw [walk,k5 _ (by decide),c4,off_value]
  · rw [walk,m5,ctr_value]
  · intro k ck;rw [walk,k5 _ ck.2.2.1];exact p4.keep k ck

theorem before_regs (s : MachineState) (i : Index) (ord left : Nat) (r : Input s i ord left) :
    Registers (beforeCall s i) ord left := by
  have keep := (pre_spec s i ord left r).2.2.2.2.2
  have c (k : Reg) (h : Clob k := by unfold Clob;decide) := keep k h
  exact ⟨(c .x10).trans r.input,(c .x12).trans r.output,(c .x5).trans r.selector,(c .x11).trans r.width,
    (c .x13).trans r.primitive,(c .x14).trans r.index,(c .x17).trans r.leftReg,(c .x22).trans r.salt,
    (c .x26).trans r.base,(c .x29).trans r.divReg⟩

theorem pre_run (i : Index) (s : MachineState) (ord left fuel : Nat) (r : Input s i ord left) :
    execute openingImage ((preFor i).length+fuel) s true =
      (do let z ← execute openingImage fuel (beforeCall s i) true; return z.charge (price (preFor i)) 0) :=
  walk_rows_run s (preFor i) (pre_spec s i ord left r).1 (pre_row_fetch _ _ _) fuel true

theorem pre_price (i : Index) : price (preFor i)=(preFor i).length+3 := by
  unfold preFor;cases groupB i.val <;> cases inPlace i.val <;> cases twelfth i.val <;> decide

theorem pre_length (i : Index) : (preFor i).length ≤ 23 := by
  unfold preFor;cases groupB i.val <;> cases inPlace i.val <;> cases twelfth i.val <;> decide

end TwoPermutationPrototype.GroupedOpening
