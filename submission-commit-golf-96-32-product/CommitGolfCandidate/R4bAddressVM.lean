import CommitGolfCandidate.R4bChunk
import CommitGolfCandidate.S4Address
set_option Elab.async false
namespace CommitGolfCandidate.R4b
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open CommitGolfCandidate.S4
open Machine (W Safe)
abbrev NRegs := Reg→Option Nat
def number (v : NRegs) (r : Reg) := (v r).getD 0
def Agree (v : NRegs) (s : MachineState) := ∀ r n,v r=some n → s.getReg r=W n
theorem Agree.read {v : NRegs} {s : MachineState} (a : Agree v s) (r : Reg) (h : (v r).isSome=true) :
    s.getReg r=W (number v r) := by
  cases e:v r with
  | none=>simp [e] at h
  | some n=>simpa [number,e] using a r n e

structure Reads where
  address : Nat→Nat
  value : Nat→Nat

inductive Op where
  | add (d a b : Reg) | mul (d a b : Reg)
  | shl (d a : Reg) (k : Nat) | shr (d a : Reg) (k : Nat)
  | mask (d a : Reg) (k : Nat)
  | div3 (d a : Reg) | mod3 (d a : Reg)
  | ld (d a : Reg) (off key : Nat)
deriving DecidableEq
def Op.dest : Op→Reg
  | .add d .. | .mul d .. | .shl d .. | .shr d .. | .mask d .. | .div3 d .. | .mod3 d .. | .ld d ..=>d
def Op.inputs : Op→List Reg
  | .add _ a b | .mul _ a b=>[a,b]
  | .shl _ a _ | .shr _ a _ | .mask _ a _ | .ld _ a ..=>[a]
  | .div3 _ a | .mod3 _ a=>[a,.x27]
def Op.code : Op→Instr
  | .add d a b=>.ADD d a b | .mul d a b=>.MUL d a b
  | .shl d a k=>.SLLI d a (imm6 k) | .shr d a k=>.SRLI d a (imm6 k)
  | .mask d a k=>.ANDI d a (imm12 (2^k-1))
  | .div3 d a=>.DIVU d a .x27 | .mod3 d a=>.REMU d a .x27
  | .ld d a off _=>.LD d a (imm12 off)
def Op.val (op : Op) (x : Reads) (v : NRegs) : Nat := match op with
  | .add _ a b=>number v a+number v b | .mul _ a b=>number v a*number v b
  | .shl _ a k=>number v a*2^k | .shr _ a k=>number v a/2^k | .mask _ a k=>number v a%2^k
  | .div3 _ a=>number v a/3 | .mod3 _ a=>number v a%3 | .ld _ _ _ k=>x.value k
def Op.ok (op : Op) (x : Reads) (v : NRegs) : Prop :=
  op.dest≠.x0 ∧ (∀ r∈op.inputs,(v r).isSome=true) ∧ (match op with
  | .add .. | .mul ..=>True
  | .shl _ _ k=>k<64
  | .shr _ a k=>k<64 ∧ number v a<2^64
  | .mask _ a k=>(k=1 ∨ k=7) ∧ number v a<2^64
  | .div3 _ a | .mod3 _ a=>number v .x27=3 ∧ number v a<2^64
  | .ld _ a off k=>off<2048 ∧ number v a+off=x.address k)
def Op.put (op : Op) (x : Reads) (v : NRegs) : NRegs :=
  fun r=>if r=op.dest then some (op.val x v) else v r

private theorem maskW (a k : Nat) (small : a<2^64) (width : k=1 ∨ k=7) :
    W a &&& signExtend12 (imm12 (2^k-1))=W (a%2^k) := by
  rw [sextSmall ⟨_,by rcases width with rfl|rfl <;> decide⟩]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show 2^k-1<2^64 by rcases width with rfl|rfl <;> decide),
    Nat.and_two_pow_sub_one_eq_mod,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.mod_le _ _) small)]

theorem oneOp (s : MachineState) (op : Op) (x : Reads) (v : NRegs) (a : Agree v s) (ok : op.ok x v)
    (read : ∀ k,Safe (x.address k) 8 ∧ s.getMem (W (x.address k))=W (x.value k)) :
    let t:=alu s op.dest (W (op.val x v))
    Straight s [op.code] t ∧ Agree (op.put x v) t := by
  obtain ⟨nz,known,condition⟩:=ok
  constructor
  · have get (r : Reg) (h : r∈op.inputs) := a.read r (known _ h)
    cases op with
    | add d i j =>
      apply Straight.one _ rfl
      change some (alu s d (s.getReg i+s.getReg j))=_
      rw [get i (by simp [Op.inputs]),get j (by simp [Op.inputs]),←BitVec.ofNat_add]
      rfl
    | mul d i j =>
      apply Straight.one _ rfl
      change some (alu s d (s.getReg i*s.getReg j))=_
      rw [get i (by simp [Op.inputs]),get j (by simp [Op.inputs]),←BitVec.ofNat_mul]
      rfl
    | shl d i k =>
      have h:=shiftL s d i k condition
      rw [get i (by simp [Op.inputs]),Machine.shifted] at h
      exact h
    | shr d i k =>
      have h:=shiftR s d i k condition.1
      rw [get i (by simp [Op.inputs]),Machine.shr _ _ condition.2] at h
      exact h
    | mask d i k =>
      apply Straight.one _ rfl
      change some (alu s d (s.getReg i &&& signExtend12 (imm12 (2^k-1))))=_
      rw [get i (by simp [Op.inputs]),maskW _ _ condition.2 condition.1];rfl
    | div3 d i =>
      apply Straight.one _ rfl
      change some (alu s d (rv64_divu (s.getReg i) (s.getReg .x27)))=_
      rw [get i (by simp [Op.inputs]),get .x27 (by simp [Op.inputs]),condition.1,show W 3=(3 : Word) from rfl,Machine.divThree _ condition.2];rfl
    | mod3 d i =>
      apply Straight.one _ rfl
      change some (alu s d (rv64_remu (s.getReg i) (s.getReg .x27)))=_
      rw [get i (by simp [Op.inputs]),get .x27 (by simp [Op.inputs]),condition.1,show W 3=(3 : Word) from rfl,Machine.modThree _ condition.2];rfl
    | ld d i off k =>
      have addr := (smallAddr s i (number v i) off (get i (by simp [Op.inputs])) condition.1).trans (congrArg W condition.2)
      have h:=justLoad s d i off _ addr (read k).1
      rw [(read k).2] at h;exact h
  · intro r n eqv
    unfold Op.put at eqv
    split at eqv
    next eq=>subst r;cases eqv;exact aluGet _ _ _ nz
    next ne=>exact (aluKeep _ _ _ _ (Ne.symm ne)).trans (a _ _ eqv)

def okList (x : Reads) (v : NRegs) : List Op→Prop
  | []=>True
  | op::ops=>op.ok x v ∧ okList x (op.put x v) ops
def finalRegs (x : Reads) (v : NRegs) : List Op→NRegs
  | []=>v
  | op::ops=>finalRegs x (op.put x v) ops

theorem runAddress (s : MachineState) (ops : List Op) (x : Reads) (v : NRegs) (a : Agree v s) (ok : okList x v ops)
    (read : ∀ k,Safe (x.address k) 8 ∧ s.getMem (W (x.address k))=W (x.value k)) :
    ∃ t,Straight s (ops.map Op.code) t ∧ t.mem=s.mem ∧ Agree (finalRegs x v ops) t ∧
      ∀ r,r∉ops.map Op.dest → t.getReg r=s.getReg r := by
  induction ops generalizing s v with
  | nil=>exact ⟨s,.nil _,rfl,a,fun _ _=>rfl⟩
  | cons op ops ih=>
    let u:=alu s op.dest (W (op.val x v))
    obtain ⟨step,ag⟩:=oneOp s op x v a ok.1 read
    have same : u.mem=s.mem:=by dsimp [u,alu,MachineState.setPC];cases op.dest <;> rfl
    obtain ⟨t,run,mem,post,regs⟩:=ih u (op.put x v) ag ok.2 (by intro k;refine ⟨(read k).1,?_⟩;simpa only [MachineState.getMem,same] using (read k).2)
    refine ⟨t,step.append run,mem.trans same,post,?_⟩
    intro r ne;have avoid : r≠op.dest ∧ r∉ops.map Op.dest:=by simpa using ne
    exact (regs r avoid.2).trans (aluKeep _ _ _ _ avoid.1.symm)
end CommitGolfCandidate.R4b
