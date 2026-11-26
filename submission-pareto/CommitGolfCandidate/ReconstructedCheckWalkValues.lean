import CommitGolfCandidate.ReconstructedCheckLayout

namespace CommitGolfCandidate.Reconstruction.CheckWalkValues
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding CheckParentGeometry CheckPairPhysical CheckLowerRound CheckLayout
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
set_option maxRecDepth 18000
set_option maxHeartbeats 1500000
abbrev W:=BitVec.ofNat 64

structure View where
  cursor : Nat
  header : List Nat
  node : Binding.Digest

def heap (idx : Index) (d : Nat):=(2^24+idx.val)/2^(24-d)
def side (idx : Index) (d : Nat):=idx.val.testBit (24-d)
def bounded (xs : List Nat) := ∀ v∈xs,v<2^32

def Ready (v : View) (hi : Nat) := v.cursor+240*(hi-9)≤70000000000 ∧ bounded v.header ∧ Canonical hi v.node

structure At (s : MachineState) (idx : Index) (hi : Nat) (v : View) : Prop where
  pc : s.pc=CommitBlocks.addr (if hi=9 then 381 else 280)
  sp : s.getReg .x2=W CheckLayout.sp
  fp : s.getReg .x8=W CheckLayout.fp
  proof : s.getReg .x19=W proofBase
  widthPtr : s.getReg .x9=W (2097160+8*hi)
  basePtr : s.getReg .x22=wordAddress (262170+hi)
  parentDepth : s.getReg .x21=W (hi-1)
  childDepth : s.getReg .x26=W hi
  route : s.getReg .x23=W (heap idx hi)
  bit : s.getReg .x24=W v.cursor
  head : CheckRecordHeader.limbs s=v.header
  node : child s CheckPair.current v.node

def prep (o : Oracle) (idx : Index) (stream : Nat) (i : Fin 15) (v : View) :=
  let d:=depth i
  let separated:=CheckMixed.out i v.header
  let sib:=CheckLowerInput.sibling stream v.cursor (CheckMixed.width i) separated.2
  let p:=sides (side idx (d.val+1)) v.node sib
  let rows:=CheckParentExecution.rows o (pairKey (d.val+1) p.1 p.2) 0 (work d)
  ((⟨v.cursor+CheckMixed.width i,separated.1,parent (oracleCompression o) d p.1 p.2⟩ : View),rows)

private theorem digits (b r : Nat) (xs : List Nat) : bounded (HonestDivision.divide b r xs).1 := by
  induction xs generalizing r with
  | nil=>intro x h;cases h
  | cons x xs ih=>
    intro z hz
    change z∈_::(HonestDivision.divide b _ xs).1 at hz
    rcases List.mem_cons.mp hz with eq|inside
    · subst z;exact Nat.mod_lt _ (by decide)
    · exact ih _ _ inside

theorem remains (o : Oracle) (idx : Index) (stream : Nat) (i : Fin 15) (v : View) (good : Ready v ((depth i).val+1)) :
    Ready (prep o idx stream i v).1 (depth i) := by
  obtain ⟨room,head,canonical⟩:=good
  have w : CheckMixed.width i≤240:=(by decide : ∀ j : Fin 15,CheckMixed.width j≤240) i
  have dv : (depth i).val=9+i.val:=rfl
  refine ⟨?_,?_,canonical_project _ _⟩
  · change (v.cursor+CheckMixed.width i)+240*((depth i).val-9)≤70000000000;omega
  · change bounded (CheckMixed.out i v.header).1;unfold CheckMixed.out;split
    · exact digits (CheckMixed.base i) 0 v.header
    · exact head

theorem four (s : MachineState) (xs : List Nat) (same : CheckRecordHeader.limbs s=xs) (bound : bounded xs) :
    ∃ a b c d : Fin (2^32), xs=[a.val,b.val,c.val,d.val] ∧ CheckMixed.typed s a b c d := by
  rw [←same] at bound ⊢
  let a : Fin (2^32):=⟨(s.getReg .x27).toNat,bound _ (by simp [CheckRecordHeader.limbs])⟩
  let b : Fin (2^32):=⟨(s.getReg .x18).toNat,bound _ (by simp [CheckRecordHeader.limbs])⟩
  let c : Fin (2^32):=⟨(s.getReg .x20).toNat,bound _ (by simp [CheckRecordHeader.limbs])⟩
  let d : Fin (2^32):=⟨(s.getReg .x25).toNat,bound _ (by simp [CheckRecordHeader.limbs])⟩
  exact ⟨a,b,c,d,rfl,by simp [CheckMixed.typed,a,b,c,d,W]⟩

private theorem oddWord (n : Nat) : W n &&& 1#64=(if n.testBit 0 then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and,BitVec.toNat_ofNat,Nat.testBit_eq_decide_div_mod_eq]
  change n%2^64 &&& (2^1-1)=_
  rw [Nat.and_two_pow_sub_one_eq_mod]
  rcases Nat.mod_two_eq_zero_or_one n with z|z <;> simp [z] <;> omega

theorem parity (idx : Index) (i : Fin 15) :
    W (heap idx ((depth i).val+1)) &&& 1#64=(if side idx ((depth i).val+1) then 1 else 0) := by
  rw [oddWord];unfold heap side;rw [Nat.testBit_div_two_pow,Nat.zero_add,Nat.testBit_two_pow_add_gt (by change 24-(9+i.val+1)<24;omega)]

theorem shift (idx : Index) (i : Fin 15) : W (heap idx ((depth i).val+1)) >>> (1 : Nat)=W (heap idx (depth i)) := by
  let d:=depth i
  have b : idx.val<2^24:=idx.isLt
  have h (k : Nat) : (2^24+idx.val)/2^k<2^64:=Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have next : 24-d.val=(24-(d.val+1))+1:=by dsimp [d,depth];have:=i.isLt;omega
  change W (heap idx (d.val+1)) >>> (1 : Nat)=W (heap idx d)
  apply BitVec.eq_of_toNat_eq
  simp only [heap,BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (h _),Nat.shiftRight_eq_div_pow]
  rw [Nat.div_div_eq_div_mul,next,Nat.pow_succ 2 (24-(d.val+1))]

theorem direction (idx : Index) (i : Fin 15) : side idx ((depth i).val+1)::CheckPath.dirs idx (depth i)=CheckPath.dirs idx ((depth i).val+1) := by
  unfold CheckPath.dirs side
  rw [List.range'_succ,List.map_cons]
  have h : 24-((depth i).val+1)+1=24-(depth i).val:=by change 24-(9+i.val+1)+1=24-(9+i.val);have:=i.isLt;omega
  rw [h]

end CommitGolfCandidate.Reconstruction.CheckWalkValues
