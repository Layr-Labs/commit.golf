import CommitGolfCandidate.GroupOpenWalk
import CommitGolfCandidate.GroupedPacket
import CommitGolfCandidate.TwoPermutationSyscall

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.Grouped (rank msgWord)
set_option maxRecDepth 22000
set_option maxHeartbeats 1800000

def indexAt (j : Nat) := BitVec.ofNat 64 (7247761440+8*j)
def destAt (i : Index) := BitVec.ofNat 64 (6979325984+16*i.val)
def countWord (n : Nat) := BitVec.ofNat 64 n
def offAt (i : Index) := if rank i.val=0 then 184 else 16*(rank i.val-1)
def readAt (i : Index) := BitVec.ofNat 64 (1536+offAt i)
/-- The pass loop's base register: `slli rank,4; add +1536` gives `readAt + 16` for every
rank (rank 0 takes the `200 + 1536` fixup), and the salt loads use `-16`/`-8`. -/
def saltBase (i : Index) := readAt i + 16
def ctrAt (i : Index) := wordAddress (msgWord (i.val-rank i.val))

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

private theorem masked (i : Index) : rv64_remu (BitVec.ofNat 64 i.val) 4096#64=BitVec.ofNat 64 (i.val%4096) := by
  unfold rv64_remu
  apply BitVec.eq_of_toNat_eq
  have h : i.val<16777216:=i.isLt
  simp [BitVec.toNat_umod,BitVec.toNat_ofNat] <;> omega

theorem decoded_rank (i : Index) : rv64_remu (BitVec.ofNat 64 (i.val%4096)) 11=BitVec.ofNat 64 (rank i.val) := by
  unfold rv64_remu rank
  change BitVec.ofNat 64 _ % 11#64=_
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_umod,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show i.val%4096<2^64 by omega),
    Nat.mod_eq_of_lt (show i.val%4096%11<2^64 by omega)] <;> omega

theorem counter_address (i : Index) :
    ((BitVec.ofNat 64 i.val - BitVec.ofNat 64 (rank i.val)) <<< (8 : Nat))+4096 = ctrAt i := by
  have sub : rank i.val ≤ i.val := by unfold rank;omega
  rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by unfold rank;omega) sub,BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 _*BitVec.ofNat 64 256+BitVec.ofNat 64 4096=_
  rw [←BitVec.ofNat_mul,←BitVec.ofNat_add];unfold ctrAt wordAddress msgWord;congr 1 <;> omega

theorem salt_address (i : Index) : ((BitVec.ofNat 64 i.val) <<< (4 : Nat))+6979325984=destAt i := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 i.val*BitVec.ofNat 64 16+BitVec.ofNat 64 6979325984=_
  rw [←BitVec.ofNat_mul,←BitVec.ofNat_add];unfold destAt;congr 1 <;> omega

theorem output_address (i : Index) (nz : rank i.val≠0) :
    (((BitVec.ofNat 64 (rank i.val))+signExtend12 (-1)) <<< (4 : Nat))+1536=readAt i := by
  have one : 1≤rank i.val := by omega
  rw [show signExtend12 (-1) = -(BitVec.ofNat 64 1) by decide]
  rw [←BitVec.sub_eq_add_neg]
  rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) one,BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 _*BitVec.ofNat 64 16+BitVec.ofNat 64 1536=_
  rw [←BitVec.ofNat_mul,←BitVec.ofNat_add];unfold readAt offAt;rw [if_neg nz];congr 1 <;> omega

theorem salt_base_zero (i : Index) (z : rank i.val=0) : saltBase i = 1736#64 := by
  unfold saltBase readAt offAt
  rw [if_pos z, show (1536+184 : Nat) = 1720 by omega]
  decide

theorem salt_base_pos (i : Index) (nz : rank i.val≠0) :
    saltBase i = ((BitVec.ofNat 64 (rank i.val)) <<< (4 : Nat))+1536#64 := by
  have one : 1≤rank i.val := by omega
  have small : rank i.val<11 := by unfold rank; omega
  unfold saltBase readAt offAt
  rw [if_neg nz, BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 (1536+16*(rank i.val-1))+BitVec.ofNat 64 16=
    BitVec.ofNat 64 (rank i.val)*BitVec.ofNat 64 16+BitVec.ofNat 64 1536
  rw [←BitVec.ofNat_add,←BitVec.ofNat_mul,←BitVec.ofNat_add]
  congr 1
  omega

theorem salt_base_sub16 (i : Index) : saltBase i+signExtend12 (-16) = readAt i := by
  rw [show signExtend12 (-16) = -(BitVec.ofNat 64 16) by decide, ←BitVec.sub_eq_add_neg]
  unfold saltBase
  exact BitVec.add_sub_cancel _ _

theorem salt_base_sub8 (i : Index) : saltBase i+signExtend12 (-8) = readAt i+8 := by
  rw [show signExtend12 (-8) = signExtend12 (-16 : BitVec 12)+BitVec.ofNat 64 8 by decide]
  rw [←BitVec.add_assoc, salt_base_sub16]
  rfl

def beforeCall (s : MachineState) := walkRows s preRows

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
private theorem room_input (i : Index) (s : MachineState) (ord left : Nat) (r : Input s i ord left) :
    legal preRows s := by
  have first : memoryArgumentsValid s (.LD .x6 .x14 0)=true := by
    simpa [memoryArgumentsValid,memAccess,r.index,signExtend12] using r.access
  simp [preRows,legal,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,
    r.pc,address,r.index,r.access,r.input,signExtend12] <;> decide

theorem pre_run (i : Index) (s : MachineState) (ord left fuel : Nat) (r : Input s i ord left) :
    execute openingImage (7+fuel) s true =
      (do let z ← execute openingImage fuel (beforeCall s) true; return z.charge 13 0) :=
  walk_rows_run s preRows (room_input i s ord left r) pre_row_fetch fuel true

theorem before_regs (s : MachineState) (i : Index) (ord left : Nat) (r : Input s i ord left) :
    let t:=beforeCall s
    Registers t ord left ∧ t.getReg .x6=BitVec.ofNat 64 i.val ∧
      t.getReg .x28=BitVec.ofNat 64 (rank i.val) ∧ t.pc=address 746 ∧
      t.mem=(s.setMem 1024 (ctrAt i)).mem := by
  dsimp only
  have simple (k : Reg) (a : k≠.x6) (b : k≠.x7) (c : k≠.x28) :
      (beforeCall s).getReg k=s.getReg k := by
    simp [beforeCall,walkRows,preRows,execInstrBr,Ne.symm a,Ne.symm b,Ne.symm c]
  refine ⟨⟨(simple _ (by decide) (by decide) (by decide)).trans r.input,
    (simple _ (by decide) (by decide) (by decide)).trans r.output,
    (simple _ (by decide) (by decide) (by decide)).trans r.selector,
    (simple _ (by decide) (by decide) (by decide)).trans r.width,
    (simple _ (by decide) (by decide) (by decide)).trans r.primitive,
    (simple _ (by decide) (by decide) (by decide)).trans r.index,
    (simple _ (by decide) (by decide) (by decide)).trans r.leftReg,
    (simple _ (by decide) (by decide) (by decide)).trans r.salt,
    (simple _ (by decide) (by decide) (by decide)).trans r.base,
    (simple _ (by decide) (by decide) (by decide)).trans r.divReg,
    (simple _ (by decide) (by decide) (by decide)).trans r.mult⟩,?_,?_,?_,?_⟩
  all_goals simp [beforeCall,walkRows,preRows,execInstrBr,r.pc,r.index,r.input,r.divReg,r.base,r.loaded,
    masked,decoded_rank,counter_address,address,show signExtend12 0=0#64 by decide,MachineState.getMem_setPC,MachineState.getMem_setReg]
  all_goals simp only [show signExtend12 0#12=0#64 by decide,BitVec.add_zero,r.loaded]
  all_goals simp only [show rv64_remu (BitVec.ofNat 64 i.val) 4096#64=BitVec.ofNat 64 (i.val%4096) from masked i,
    show rv64_remu (BitVec.ofNat 64 (i.val%4096)) 11#64=BitVec.ofNat 64 (rank i.val) from decoded_rank i,
    show ((BitVec.ofNat 64 i.val-BitVec.ofNat 64 (rank i.val)) <<< (8:Nat))+4096#64=ctrAt i from counter_address i]

end TwoPermutationPrototype.GroupedOpening
