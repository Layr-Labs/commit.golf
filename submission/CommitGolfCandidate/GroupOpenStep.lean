import CommitGolfCandidate.GroupOpenLoop
import CommitGolfCandidate.GroupedPacket
import CommitGolfCandidate.TwoPermutationSyscall

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.Grouped (msgWord saltHead sliceByte)
open CommitGolfCandidate.Permutation.CounterSalt (coord)
set_option maxRecDepth 22000
set_option maxHeartbeats 1800000

def indexAt (j : Nat) := BitVec.ofNat 64 (7247761440+8*j)
def destAt (i : Index) := BitVec.ofNat 64 (6979325984+16*i.val)
def countWord (n : Nat) := BitVec.ofNat 64 n
/-- Byte offset of leaf `i`'s salt in its generator reply. -/
def offAt (i : Index) := sliceByte (coord i).2.val
def readAt (i : Index) := BitVec.ofNat 64 (1536+offAt i)
/-- Counter word of leaf `i`'s reply: the odd entry of its salt's head pair. -/
def ctrAt (i : Index) := wordAddress (msgWord (2*saltHead i.val+1))

structure Registers (s : MachineState) (ord left : Nat) : Prop where
  input : s.getReg .x10=1024
  output : s.getReg .x12=1536
  selector : s.getReg .x5=0
  width : s.getReg .x11=200
  primitive : s.getReg .x13=1
  index : s.getReg .x14=indexAt ord
  leftReg : s.getReg .x17=countWord left
  salt : s.getReg .x22=6979325984
  base : s.getReg .x26=4096
  divReg : s.getReg .x29=11
  mult : s.getReg .x4=368

structure Input (s : MachineState) (i : Index) (ord left : Nat) extends Registers s ord left where
  pc : s.pc=address 739
  loaded : s.getMem (indexAt ord)=BitVec.ofNat 64 i.val
  access : accessValid (indexAt ord) 8=true

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC
attribute [local irreducible] wordAddress

@[local simp] theorem pc_of_set (s : MachineState) (p : Word) : (s.setPC p).pc=p := rfl
@[local simp] theorem mem_of_set (s : MachineState) (p : Word) : (s.setPC p).mem=s.mem := rfl
@[local simp] theorem mem_of_reg (s : MachineState) (r : Reg) (v : Word) : (s.setReg r v).mem=s.mem := by cases r <;> rfl
@[local simp] theorem mem_of_store (s : MachineState) (a v : Word) : (s.setMem a v).mem=fun w => if w==a then v else s.mem w := rfl
@[local simp] theorem open_zero (s : MachineState) : s.getReg .x0=0 := rfl

/-! ### Word arithmetic of the loop (all values are far below 2^64) -/

theorem shr_word (n : Nat) : BitVec.ofNat 64 n >>> 1=BitVec.ofNat 64 (n%2^64/2) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  omega
theorem mask_word (n : Nat) (h : n<2^64) : BitVec.ofNat 64 n &&& 2047#64=BitVec.ofNat 64 (n%2048) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and,BitVec.toNat_ofNat,Nat.mod_eq_of_lt h]
  rw [show (2047%2^64 : Nat)=2^11-1 by decide,Nat.and_two_pow_sub_one_eq_mod]
  omega
theorem remu_word (n : Nat) (h : n<2^64) : rv64_remu (BitVec.ofNat 64 n) 11#64=BitVec.ofNat 64 (n%11) := by
  unfold rv64_remu
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_umod]
  omega
theorem sub_word (a b : Nat) (h : a<2^64) (le : b ≤ a) : BitVec.ofNat 64 a-BitVec.ofNat 64 b=BitVec.ofNat 64 (a-b) :=
  BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) le
theorem add_word (a b : Nat) : BitVec.ofNat 64 a+BitVec.ofNat 64 b=BitVec.ofNat 64 (a+b) := (BitVec.ofNat_add a b).symm
theorem parity_word (n : Nat) (h : n<2^64) : BitVec.ofNat 64 n &&& 1#64=BitVec.ofNat 64 (n%2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and,BitVec.toNat_ofNat,Nat.mod_eq_of_lt h]
  rw [show (1%2^64 : Nat)=2^1-1 by decide,Nat.and_two_pow_sub_one_eq_mod]
  omega
theorem shl_word (n k : Nat) : BitVec.ofNat 64 n <<< k=BitVec.ofNat 64 (n*2^k) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq]
theorem place_word (n : Nat) (h : n<2) : (-BitVec.ofNat 64 n) &&& 184#64=BitVec.ofNat 64 (184*n) := by
  rcases (show n=0 ∨ n=1 by omega) with e|e <;> subst e <;> decide
theorem minus_word (a k : Nat) (h : a<2^64) (le : k ≤ a) (e : BitVec 64) (he : e=-BitVec.ofNat 64 k) :
    BitVec.ofNat 64 a+e=BitVec.ofNat 64 (a-k) := by
  rw [he,←BitVec.sub_eq_add_neg];exact sub_word a k h le
theorem ult_word (a b : Nat) (ha : a<2^64) (hb : b<2^64) : BitVec.ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 b)=decide (a<b) := by
  simp [BitVec.ult];omega
theorem bne_word (a b : Nat) (ha : a<2^64) (hb : b<2^64) : (BitVec.ofNat 64 a != BitVec.ofNat 64 b)=!decide (a=b) := by
  by_cases e : a=b
  · subst e;simp
  · have : BitVec.ofNat 64 a≠BitVec.ofNat 64 b := by
      intro h;have := congrArg BitVec.toNat h;simp at this;omega
    simp [this,e]

/-! ### Branches as `setPC` -/

theorem bltu_form (u : MachineState) (a b : Reg) (off : BitVec 13) :
    execInstrBr u (.BLTU a b off)=u.setPC (if BitVec.ult (u.getReg a) (u.getReg b) then u.pc+signExtend13 off else u.pc+4) := by
  by_cases c : BitVec.ult (u.getReg a) (u.getReg b) <;> simp [execInstrBr,c]
theorem bne_form (u : MachineState) (a b : Reg) (off : BitVec 13) :
    execInstrBr u (.BNE a b off)=u.setPC (if (u.getReg a != u.getReg b) then u.pc+signExtend13 off else u.pc+4) := by
  by_cases c : (u.getReg a != u.getReg b) <;> simp only [execInstrBr,c] <;> rfl
theorem jal_form (u : MachineState) (off : BitVec 21) : execInstrBr u (.JAL .x0 off)=u.setPC (u.pc+signExtend21 off) := rfl

/-! ### Segment specs. `Point s t n`: `t` is at word `n`, with `s`'s memory and every register outside x6,x7,x28,x30,x31. -/

def Clob (k : Reg) := k≠.x6 ∧ k≠.x7 ∧ k≠.x28 ∧ k≠.x30 ∧ k≠.x31

structure Point (s t : MachineState) (n : Nat) : Prop where
  pc : t.pc=address n
  mem : t.mem=s.mem
  keep : ∀ k, Clob k → t.getReg k=s.getReg k

def headOps : List Row := [(739,.LD .x6 .x14 0),(740,.SRLI .x28 .x6 1),(741,.ANDI .x7 .x28 2047),
  (742,.REMU .x7 .x7 .x29),(743,.SUB .x28 .x28 .x7),(744,.ADDI .x30 .x0 5)]
theorem head_parts : headRows=headOps++[(745,.BLTU .x7 .x30 12)] := rfl

theorem single_walk (s : MachineState) (row : Row) : walkRows s [row]=execInstrBr s row.2 := rfl

theorem head_spec (s : MachineState) (i : Index) (ord left : Nat) (r : Input s i ord left) :
    let t:=walkRows s headRows
    legal headRows s ∧ Point s t (if loopR i.val<5 then 748 else 746) ∧ t.getReg .x6=BitVec.ofNat 64 i.val ∧
      t.getReg .x7=BitVec.ofNat 64 (loopR i.val) ∧ t.getReg .x28=BitVec.ofNat 64 (i.val/2-loopR i.val) := by
  have hi : i.val<16777216 := i.isLt
  have rl : loopR i.val=i.val/2%2048%11 := rfl
  let t0:=walkRows s headOps
  have z12 : signExtend12 0#12=0#64 := by decide
  have v6 : t0.getReg .x6=BitVec.ofNat 64 i.val := by
    simp [t0,walkRows,headOps,execInstrBr,r.index,z12,r.loaded]
  have v7 : t0.getReg .x7=BitVec.ofNat 64 (loopR i.val) := by
    simp [t0,walkRows,headOps,execInstrBr,r.index,z12,r.loaded,r.divReg,show signExtend12 2047#12=2047#64 by decide]
    rw [shr_word,mask_word _ (by omega),remu_word _ (by omega),rl,Nat.mod_eq_of_lt (show i.val<2^64 by omega)]
  have v28 : t0.getReg .x28=BitVec.ofNat 64 (i.val/2-loopR i.val) := by
    simp [t0,walkRows,headOps,execInstrBr,r.index,z12,r.loaded,r.divReg,show signExtend12 2047#12=2047#64 by decide]
    rw [shr_word,mask_word _ (by omega),remu_word _ (by omega),rl,Nat.mod_eq_of_lt (show i.val<2^64 by omega),
      sub_word _ _ (by omega) (by omega)]
  have v30 : t0.getReg .x30=BitVec.ofNat 64 5 := by
    simp [t0,walkRows,headOps,execInstrBr];decide
  have pc0 : t0.pc=address 745 := by
    simp [t0,walkRows,headOps,execInstrBr,r.pc,address]
  have mem0 : t0.mem=s.mem := by simp [t0,walkRows,headOps,execInstrBr]
  have keep0 : ∀ k, Clob k → t0.getReg k=s.getReg k := by
    intro k ⟨a,b,c,d,_⟩;simp [t0,walkRows,headOps,execInstrBr,Ne.symm a,Ne.symm b,Ne.symm c,Ne.symm d]
  have legal0 : legal headOps s := by
    have first : memoryArgumentsValid s (.LD .x6 .x14 0)=true := by
      simpa [memoryArgumentsValid,memAccess,r.index,signExtend12] using r.access
    simp [headOps,legal,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,r.pc,address,r.index,r.access,signExtend12] <;> decide
  have walk : walkRows s headRows=t0.setPC (address (if loopR i.val<5 then 748 else 746)) := by
    rw [head_parts,walk_join,single_walk];dsimp only
    rw [bltu_form,v7,v30,pc0,ult_word _ _ (by have := loop_r_lt i.val;omega) (by decide)]
    by_cases c : loopR i.val<5 <;> simp only [c,decide_true,decide_false,ite_true,ite_false,Bool.false_eq_true] <;>
      exact congrArg _ (by decide)
  refine ⟨?_,⟨?_,?_,?_⟩,?_,?_,?_⟩
  · rw [head_parts];exact legal_append _ _ _ legal0 ⟨pc0,rfl,trivial⟩
  · rw [walk];rfl
  · rw [walk];exact mem0
  · intro k ck;rw [walk,MachineState.getReg_setPC];exact keep0 k ck
  · rw [walk,MachineState.getReg_setPC];exact v6
  · rw [walk,MachineState.getReg_setPC];exact v7
  · rw [walk,MachineState.getReg_setPC];exact v28

theorem point_set (s t : MachineState) (n : Nat) (p : Word) (pt : Point s t n) (e : p=address n) : Point s (t.setPC p) n :=
  ⟨e,pt.mem,fun k ck => (MachineState.getReg_setPC).trans (pt.keep k ck)⟩

theorem group_spec (s t : MachineState) (i : Index) (pt : Point s t (if loopR i.val<5 then 748 else 746))
    (v6 : t.getReg .x6=BitVec.ofNat 64 i.val) (v7 : t.getReg .x7=BitVec.ofNat 64 (loopR i.val))
    (v28 : t.getReg .x28=BitVec.ofNat 64 (i.val/2-loopR i.val)) :
    let u:=walkRows t (groupRows (groupB i.val))
    legal (groupRows (groupB i.val)) t ∧ Point s u 748 ∧ u.getReg .x6=BitVec.ofNat 64 i.val ∧
      u.getReg .x7=BitVec.ofNat 64 (loopK i.val) ∧ u.getReg .x28=BitVec.ofNat 64 (loopHead i.val) := by
  have hi : i.val<16777216 := i.isLt
  have rb := loop_r_lt i.val
  have rle : loopR i.val ≤ i.val/2 := by unfold loopR;omega
  by_cases c : loopR i.val<5
  · have g : groupB i.val=false := by simp [groupB,c]
    rw [g];simp only [groupRows,Bool.false_eq_true,ite_false]
    rw [if_pos c] at pt
    refine ⟨trivial,pt,v6,?_,?_⟩
    · change t.getReg .x7=_;rw [v7];unfold loopK;rw [if_pos c]
    · change t.getReg .x28=_;rw [v28];unfold loopHead loopK;rw [if_pos c]
  · have g : groupB i.val=true := by simp [groupB,c]
    rw [g];simp only [groupRows,ite_true]
    rw [if_neg c] at pt
    have k : loopK i.val=loopR i.val-5 := by unfold loopK;rw [if_neg c]
    refine ⟨⟨pt.pc,rfl,?_,rfl,trivial⟩,⟨?_,?_,?_⟩,?_,?_,?_⟩
    · simp [execInstrBr,pt.pc,address]
    · simp [walkRows,execInstrBr,pt.pc,address]
    · simp [walkRows,execInstrBr,pt.mem]
    · intro k ⟨a,b,c,d,e⟩;simp [walkRows,execInstrBr,Ne.symm b,Ne.symm c];exact pt.keep k ⟨a,b,c,d,e⟩
    · simp [walkRows,execInstrBr,v6]
    · simp [walkRows,execInstrBr,v7]
      rw [minus_word _ 5 (by omega) (by omega) _ (by decide),k]
    · simp [walkRows,execInstrBr,v28,show signExtend12 5#12=BitVec.ofNat 64 5 by decide]
      rw [add_word];unfold loopHead;rw [k];congr 1;omega

theorem parity_spec (s u : MachineState) (i : Index) (pt : Point s u 748)
    (v6 : u.getReg .x6=BitVec.ofNat 64 i.val) (v7 : u.getReg .x7=BitVec.ofNat 64 (loopK i.val))
    (v28 : u.getReg .x28=BitVec.ofNat 64 (loopHead i.val)) :
    let v:=walkRows u parityRows
    legal parityRows u ∧ Point s v (if loopK i.val=0 then 750 else 753) ∧ v.getReg .x6=BitVec.ofNat 64 i.val ∧
      v.getReg .x7=BitVec.ofNat 64 (loopK i.val) ∧ v.getReg .x28=BitVec.ofNat 64 (loopHead i.val) ∧
      v.getReg .x30=BitVec.ofNat 64 (i.val%2) := by
  have hi : i.val<16777216 := i.isLt
  have kb := loop_k_lt i.val
  let v0:=execInstrBr u (.ANDI .x30 .x6 1)
  have walk : walkRows u parityRows=execInstrBr v0 (.BNE .x7 .x0 16) := rfl
  have w6 : v0.getReg .x6=BitVec.ofNat 64 i.val := by simp [v0,execInstrBr,v6]
  have w7 : v0.getReg .x7=BitVec.ofNat 64 (loopK i.val) := by simp [v0,execInstrBr,v7]
  have w28 : v0.getReg .x28=BitVec.ofNat 64 (loopHead i.val) := by simp [v0,execInstrBr,v28]
  have w30 : v0.getReg .x30=BitVec.ofNat 64 (i.val%2) := by
    simp [v0,execInstrBr,v6,show signExtend12 1#12=1#64 by decide];exact parity_word _ (by omega)
  have p0 : v0.pc=address 749 := by simp [v0,execInstrBr,pt.pc,address]
  have pc : (walkRows u parityRows).pc=address (if loopK i.val=0 then 750 else 753) := by
    rw [walk,bne_form];simp only [pc_of_set]
    rw [w7,open_zero,p0,show (0 : Word)=BitVec.ofNat 64 0 from rfl,bne_word _ _ (by omega) (by decide)]
    by_cases c : loopK i.val=0 <;> simp only [c,decide_true,decide_false,Bool.not_true,Bool.not_false,ite_true,ite_false,
      Bool.false_eq_true] <;> decide
  refine ⟨⟨pt.pc,rfl,p0,rfl,trivial⟩,⟨pc,?_,?_⟩,?_,?_,?_,?_⟩
  · rw [walk,bne_form];simp [v0,execInstrBr,pt.mem]
  · intro k ⟨a,b,c,d,_⟩;rw [walk,bne_form];simp [v0,execInstrBr,Ne.symm d,pt.keep k ⟨a,b,c,d,‹_›⟩]
  all_goals rw [walk,bne_form,MachineState.getReg_setPC]
  exacts [w6,w7,w28,w30]

end TwoPermutationPrototype.GroupedOpening
