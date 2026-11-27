import CommitGolfCandidate.RungAExec
import CommitGolfCandidate.R4bAddressVM
set_option Elab.async false
namespace CommitGolfCandidate.RungA
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open S4.Machine (W Safe Code Runs)
open R4b (NRegs Agree number Straight alu aluGet aluKeep imm12 imm6)
open Late (pcAt)
abbrev image := Code.opening.image
theorem liftRun (o : Oracle) {s t : MachineState} {n c : Nat} (h : Runs .opening s t n c) :
    DetRun o image s n t c 0 := by
  intro k
  rw [Nat.add_comm n k,h k true]
  have map : (do let e←execute image k t true;pure (e.charge c 0)) = (fun e : Execution=>e.charge c 0) <$> execute image k t true:=by
    rw [map_eq_bind_pure_comp];rfl
  rw [map,oracle_run_map];simp only [Nat.zero_add]

inductive Op where
  | add (d a b : Reg) | sub (d a b : Reg) | mul (d a b : Reg) | div (d a b : Reg)
  | pos (d a : Reg) (k : Nat) | neg (d a : Reg) (k : Nat) | hi (d : Reg) (n : Nat)
  | shr (d a : Reg) (k : Nat) | shl (d a : Reg) (k : Nat)
deriving DecidableEq
def Op.dst : Op→Reg
  | .add d .. | .sub d .. | .mul d .. | .div d .. | .pos d .. | .neg d .. | .hi d .. | .shr d .. | .shl d ..=>d
def Op.inputs : Op→List Reg
  | .add _ a b | .sub _ a b | .mul _ a b | .div _ a b=>[a,b]
  | .pos _ a _ | .neg _ a _ | .shr _ a _ | .shl _ a _=>[a] | .hi ..=>[]
def Op.code : Op→Instr
  | .add d a b=>.ADD d a b | .sub d a b=>.SUB d a b | .mul d a b=>.MUL d a b | .div d a b=>.DIVU d a b
  | .pos d a n=>.ADDI d a (imm12 n) | .neg d a n=>.ADDI d a (imm12 (4096-n))
  | .hi d n=>.LUI d (BitVec.ofNat 20 n) | .shr d a k=>.SRLI d a (imm6 k) | .shl d a k=>.SLLI d a (imm6 k)
def Op.val (op : Op) (v : NRegs) := match op with
  | .add _ a b=>number v a+number v b | .sub _ a b=>number v a-number v b
  | .mul _ a b=>number v a*number v b | .div _ a b=>number v a/number v b
  | .pos _ a k=>number v a+k | .neg _ a k=>number v a-k | .hi _ n=>4096*n
  | .shr _ a k=>number v a/2^k | .shl _ a k=>number v a*2^k
def Op.ok (op : Op) (v : NRegs) : Prop := op.dst≠.x0 ∧ (∀ r∈op.inputs,(v r).isSome=true) ∧ (match op with
  | .add .. | .mul ..=>True | .sub _ a b=>number v b≤number v a
  | .div _ a b=>0<number v b ∧ number v a<2^64 ∧ number v b<2^64
  | .pos _ _ k=>k<2048 | .neg _ a k=>0<k ∧ k≤2048 ∧ k≤number v a
  | .hi _ n=>(((BitVec.ofNat 20 n).zeroExtend 32 <<< (12 : Nat)).signExtend 64)=W (4096*n)
  | .shl _ _ k=>k<64 | .shr _ a k=>k<64 ∧ number v a<2^64)
def Op.put (op : Op) (v : NRegs) : NRegs:=fun r=>if r=op.dst then some (op.val v) else v r
private theorem subW (n k : Nat) (h : k≤n) : W n-W k=W (n-k) := by
  rw [show W n=W (n-k)+W k from (congrArg W (show n=n-k+k by omega)).trans (BitVec.ofNat_add ..),BitVec.add_sub_cancel]
set_option maxRecDepth 9000 in
private theorem negImm : ∀ k : Fin 2049,0<k.val → signExtend12 (imm12 (4096-k.val))= -W k.val:=by decide +kernel
private theorem divW (n k : Nat) (h : 0<k) (bn:n<2^64) (bk:k<2^64) : rv64_divu (W n) (W k)=W (n/k) := by
  have ne : W k≠0#64 := by intro eq;have:=S4.Machine.wordNumber bk (by decide : 0<2^64) (show W k=W 0 from eq);omega
  unfold rv64_divu;rw [if_neg (by simpa only [beq_iff_eq] using ne)];apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_udiv,W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt bn,Nat.mod_eq_of_lt bk,Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self ..) bn)]

theorem mathOne (s : MachineState) (op : Op) (v : NRegs) (ag : Agree v s) (ok : op.ok v) :
    let t:=alu s op.dst (W (op.val v))
    Straight s [op.code] t ∧ Agree (op.put v) t := by
  obtain ⟨nz,known,c⟩:=ok
  constructor
  · have get (r : Reg) (m:r∈op.inputs) := ag.read r (known _ m)
    cases op with
    | add d a b=>
      apply Straight.one _ rfl
      change some (alu s d (s.getReg a+s.getReg b))=_
      rw [get a (by simp [Op.inputs]),get b (by simp [Op.inputs]),←BitVec.ofNat_add];rfl
    | sub d a b=>
      apply Straight.one _ rfl
      change some (alu s d (s.getReg a-s.getReg b))=_
      rw [get a (by simp [Op.inputs]),get b (by simp [Op.inputs]),subW _ _ c];rfl
    | mul d a b=>
      apply Straight.one _ rfl
      change some (alu s d (s.getReg a*s.getReg b))=_
      rw [get a (by simp [Op.inputs]),get b (by simp [Op.inputs]),←BitVec.ofNat_mul];rfl
    | div d a b=>
      apply Straight.one _ rfl
      change some (alu s d (rv64_divu (s.getReg a) (s.getReg b)))=_
      rw [get a (by simp [Op.inputs]),get b (by simp [Op.inputs]),divW _ _ c.1 c.2.1 c.2.2];rfl
    | pos d a k=>
      apply Straight.one _ rfl
      change some (alu s d (s.getReg a+signExtend12 (imm12 k)))=_
      rw [get a (by simp [Op.inputs]),R4b.sextSmall ⟨k,c⟩,←BitVec.ofNat_add];rfl
    | neg d a k=>
      apply Straight.one _ rfl
      change some (alu s d (s.getReg a+signExtend12 (imm12 (4096-k))))=_
      rw [get a (by simp [Op.inputs]),negImm ⟨k,by have:=c.2.1;omega⟩ c.1,BitVec.add_neg_eq_sub,subW _ _ c.2.2];rfl
    | hi d n=>
      apply Straight.one _ rfl
      change some (alu s d _) = _;rw [c];rfl
    | shr d a k=>
      have h:=R4b.shiftR s d a k c.1;rw [get a (by simp [Op.inputs]),S4.Machine.shr _ _ c.2] at h;exact h
    | shl d a k=>
      have h:=R4b.shiftL s d a k c;rw [get a (by simp [Op.inputs]),S4.Machine.shifted] at h;exact h
  · intro r n eq;unfold Op.put at eq;split at eq
    next same=>subst r;cases eq;exact aluGet _ _ _ nz
    next ne=>exact (aluKeep _ _ _ _ (Ne.symm ne)).trans (ag _ _ eq)
def okList (v : NRegs) : List Op→Prop
  | []=>True | o::os=>o.ok v ∧ okList (o.put v) os
def finalRegs (v : NRegs) : List Op→NRegs
  | []=>v | o::os=>finalRegs (o.put v) os

theorem arith (s : MachineState) (ops : List Op) (v : NRegs) (ag : Agree v s) (ok : okList v ops):
    ∃ t,Straight s (ops.map Op.code) t ∧ t.mem=s.mem ∧ Agree (finalRegs v ops) t ∧
      ∀ r,r∉ops.map Op.dst → t.getReg r=s.getReg r := by
  induction ops generalizing s v with
  | nil=>exact ⟨s,.nil _,rfl,ag,fun _ _=>rfl⟩
  | cons op ops ih=>
    let u:=alu s op.dst (W (op.val v))
    obtain ⟨a,b⟩:=mathOne s op v ag ok.1
    have mem : u.mem=s.mem:=by dsimp [u,alu];cases op.dst <;> rfl
    obtain ⟨t,f,m,j,k⟩:=ih u (op.put v) b ok.2
    refine ⟨t,a.append f,m.trans mem,j,?_⟩
    intro r no;have out : r≠op.dst ∧ r∉ops.map Op.dst:=by simpa using no
    exact (k _ out.2).trans (aluKeep _ _ _ _ out.1.symm)

def Site (pc : Nat) (ops : List Op) (steps cost : Nat) : Prop :=
   S4.Machine.listed .opening pc (ops.map Op.code) ∧ ops.length=steps ∧ R4b.clocks (ops.map Op.code)=cost ∧ pc+steps≤Code.opening.count
instance (p ops n c) : Decidable (Site p ops n c) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem arithRun (o : Oracle) (p n c : Nat) (ops : List Op) (v : NRegs) (s : MachineState) (pc:s.pc=pcAt p)
    (ag : Agree v s) (ok:okList v ops) (site:Site p ops n c) :
    ∃ t,DetRun o image s n t c 0 ∧ t.pc=pcAt (p+n) ∧ t.mem=s.mem ∧ Agree (finalRegs v ops) t ∧
      ∀ r,r∉ops.map Op.dst → t.getReg r=s.getReg r := by
  obtain ⟨a,len,cost,limit⟩:=site
  obtain ⟨t,path,mem,j,k⟩:=arith s ops v ag ok
  obtain ⟨run,endPC⟩:=path.exec p pc (by simpa only [List.length_map,len] using limit) (S4.Machine.matchesListed a)
  rw [List.length_map,len,cost] at run;rw [List.length_map,len] at endPC
  exact ⟨t,liftRun o run,endPC,mem,j,k⟩
end CommitGolfCandidate.RungA
