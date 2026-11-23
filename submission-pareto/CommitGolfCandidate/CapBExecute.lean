import CommitGolfCandidate.CapBMachine
namespace CommitGolfCandidate.CapB
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp Layout2Helpers
set_option maxHeartbeats 1100000
set_option maxRecDepth 10000

private theorem assign {s t a m} (tr : Tracks s t a m) (r : Reg) (nz : r≠.x0)
    (x : Expr) (v newPC : Word) (eq : v=val s a x) :
    Tracks s ((t.setReg r v).setPC newPC) a (regSet m r x) := by
  have mem : ((t.setReg r v).setPC newPC).mem=t.mem := by cases r <;> rfl
  refine ⟨?_,?_,?_⟩
  · intro k
    by_cases same : r=k
    · subst k;simpa [regSet,MachineState.getReg_setReg_eq nz] using eq
    · simp [regSet,same,MachineState.getReg_setReg_ne t _ _ v same,tr.reg]
  · intro j hj;simpa only [MachineState.getMem,mem,regSet] using tr.out j hj
  · intro w hw;simpa only [MachineState.getMem,mem] using tr.frame w hw

private theorem unique {a : Areas} (safe : Safe a) (b : Area) (i j : Nat) (hi : i<a.words b) (hj : j<a.words b) :
    a.key b i=a.key b j ↔ i=j := by
  have m:=safe.room b;have lim : MEMORY_BYTES<2^64 := by decide
  constructor
  · intro e;have n:=congrArg BitVec.toNat e
    simp only [Areas.key,addr,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show a.start b+8*i<2^64 by omega),
      Nat.mod_eq_of_lt (show a.start b+8*j<2^64 by omega)] at n;omega
  · rintro rfl;rfl

private theorem store {s t a m} (tr : Tracks s t a m) (safe : Safe a) (j : Nat) (hj : j<a.dstWords)
    (x : Expr) (v newPC : Word) (eq : v=val s a x) :
    Tracks s ((t.setMem (a.key .dst j) v).setPC newPC) a (outSet m j x) := by
  refine ⟨tr.reg,?_,?_⟩
  · intro i hi
    change (t.setMem _ v).getMem _=val s a (if j=i then x else m.out i)
    by_cases same : j=i
    · subst i;simpa only [ite_true,MachineState.getMem_setMem_eq] using eq
    · rw [if_neg same,MachineState.getMem_setMem_ne (fun h=>same ((unique safe .dst i j hi hj).mp h).symm)];exact tr.out i hi
  · intro w away
    change (t.setMem _ v).getMem w=_
    rw [MachineState.getMem_setMem_ne (away j hj)];exact tr.frame w away

private theorem get {s t a m} (tr : Tracks s t a m) (safe : Safe a) (b : Area) (j : Nat) (hj : j<a.words b) :
    t.getMem (a.key b j)=val s a (read m b j) := by
  cases b with
  | dst => exact tr.out j hj
  | src =>
    apply tr.frame
    intro k hk eq
    have lim : MEMORY_BYTES<2^64 := by decide
    have sr : a.src+8*a.srcWords≤MEMORY_BYTES := safe.room .src
    have dr : a.dst+8*a.dstWords≤MEMORY_BYTES := safe.room .dst
    change j<a.srcWords at hj
    have ne:=congrArg BitVec.toNat eq
    simp only [Areas.key,Areas.start,addr,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show a.src+8*j<2^64 by omega),
      Nat.mod_eq_of_lt (show a.dst+8*k<2^64 by omega)] at ne
    have apart:=safe.disjoint;omega

private theorem imm : ∀ j : Fin 256, signExtend12 (BitVec.ofNat 12 (8*j.val))=addr (8*j.val) := by decide +kernel

theorem step {s t a l m} (tr : Tracks s t a m) (safe : Safe a)
    (base : ∀ r,val s a (l.base r)=addr (a.start r)) (counts : ∀r,l.count r=a.words r)
    (r : Row) (ok : valid l m r) :
    memoryArgumentsValid t (op r)=true ∧ Tracks s (execInstrBr t (op r)) a (advance m r) := by
  have key (reg : Reg) (b : Area) (j : Nat) (eq : m.reg reg=l.base b) (bound : j<256) :
      t.getReg reg+signExtend12 (BitVec.ofNat 12 (8*j))=a.key b j := by
    rw [tr.reg,eq,base,imm ⟨j,bound⟩,←BitVec.ofNat_add];rfl
  have permitted (b : Area) (j : Nat) (bound : j<l.count b) : accessValid (a.key b j) 8=true := by
    apply access_ok <;> have:=safe.alg b <;> have:=safe.room b <;> rw [counts] at bound <;> omega
  cases r with
  | addi d b n =>
    refine ⟨rfl,assign tr d ok _ _ _ ?_⟩
    simp only [val,tr.reg,addr,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  | lui d n =>
    refine ⟨rfl,assign tr d ok _ _ _ ?_⟩;simp only [val,addr,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  | add d b c | bor d b c | mul d b c =>
    all_goals refine ⟨rfl,assign tr d ok _ _ _ ?_⟩;simp only [val,tr.reg]
  | shl d b n | shr d b n =>
    all_goals refine ⟨rfl,assign tr d ok.1 _ _ _ ?_⟩;simp only [val,tr.reg,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show n<64 from ok.2)]
  | ld d b region j =>
    obtain ⟨nz,eq,hj,lim⟩:=ok
    have loc:=key b region j eq lim
    refine ⟨?_,assign tr d nz _ _ _ ?_⟩
    · change accessValid _ 8=true;rw [loc];exact permitted _ _ hj
    · change t.getMem (t.getReg b+signExtend12 (BitVec.ofNat 12 (8*j)))=_
      rw [loc];apply get tr safe;simpa only [←counts] using hj
  | sd b reg j =>
    obtain ⟨eq,hj,lim⟩:=ok
    have loc:=key reg .dst j eq lim
    refine ⟨?_,?_⟩
    · change accessValid _ 8=true;rw [loc];exact permitted _ _ hj
    · simp only [op,execInstrBr,loc]
      exact store tr safe j (by simpa only [counts,Areas.words] using hj) _ _ _ (tr.reg b)

theorem run {I s a l} (safe : Safe a)
    (base : ∀ r,val s a (l.base r)=addr (a.start r)) (counts : ∀r,l.count r=a.words r)
    (rs : List Row) (w : Nat) (t : MachineState) (m : Model) (tr : Tracks s t a m)
    (here : t.pc=pc w) (lim : w+rs.length<2^40) (code : CodeAt I w (rs.map op))
    (ok : checked l m rs=true) :
    ∃ u, Run I t u rs.length (price rs) ∧ u.pc=pc (w+rs.length) ∧ Tracks s u a (rs.foldl advance m) := by
  induction rs generalizing w t m with
  | nil => exact ⟨t,Run.zero I t,here,tr⟩
  | cons r rs ih =>
    simp only [checked,Bool.and_eq_true,decide_eq_true_eq] at ok
    obtain ⟨accessible,next⟩:=step tr safe base counts r ok.1
    have ord : ordinaryStep t (.base (op r))=some (execInstrBr t (op r)) := by
      cases r <;> simp only [op] at accessible ⊢ <;> simp only [ordinaryStep,accessible,ite_true]
    have head:=one (by omega : w<2^40) here (by simpa using code ⟨0,by simp⟩) ord
    have nPC : (execInstrBr t (op r)).pc=pc (w+1) := by
      have direct : (execInstrBr t (op r)).pc=t.pc+4 := by cases r <;> rfl
      rw [direct,here,pc_add]
    have rest : CodeAt I (w+1) (rs.map op) := by
      intro i;simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using code ⟨i.val+1,by simpa using i.isLt⟩
    obtain ⟨u,ran,last,post⟩:=ih (w+1) _ _ next nPC (by simp only [List.length_cons] at lim;omega) rest ok.2
    refine ⟨u,by simpa only [price,List.length_cons,List.map_cons,List.sum_cons,Nat.add_comm 1] using head.thenDo ran,?_,post⟩
    simpa only [List.length_cons,show w+1+rs.length=w+(rs.length+1) by omega] using last

end CommitGolfCandidate.CapB
