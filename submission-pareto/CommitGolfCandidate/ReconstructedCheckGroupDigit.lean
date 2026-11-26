import CommitGolfCandidate.ReconstructedCheckGroupRadix
import CommitGolfCandidate.ReconstructedCheckMemoryOps
import CommitGolfCandidate.ReconstructedCheckRecordHeader

namespace CommitGolfCandidate.Reconstruction.CheckGroupDigit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningOps CheckRecorded CommitBlocks CheckGroupRadix
open TwoPermutationPrototype TwoPermutationPrototype.RV64
set_option maxRecDepth 14000
set_option maxHeartbeats 2000000

def ops (id : Nat) : List Op := [
  .reg .x5 (.addi .x17 0),.reg .x17 (.mulhu .x17 .x26),.reg .x17 (.srli .x17 6),
  .reg .x6 (.slli .x6 5),.reg .x6 (.add .x6 .x23),.ld .x7 .x6 24 (top id),
  .reg .x28 (.mul .x17 .x21),.reg .x28 (.subw .x5 .x28),.reg .x28 (.slli .x28 32),
  .reg .x7 (.or .x7 .x28),.sd .x6 .x7 24 (top id),.reg .x15 (.addi .x15 1),.reg .x16 (.addi .x16 4)]
def after (m : Model) (id : Nat) := (ops id).foldl (fun a op=>op.apply a) m

private theorem listed (id : Nat) : CheckStraight.Listed 578 ((ops id).map Op.instr) :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩

def changed := [Reg.x5,.x6,.x7,.x15,.x16,.x17,.x28]

private def writes : Op→List Reg
  | .reg r _ | .ld r ..=>[r]
  | .sd ..=>[]

private theorem untouched (os : List Op) (m : Model) (r : Reg) (h : r∉os.flatMap writes) :
    (os.foldl (fun p i=>i.apply p) m).reg r=m.reg r := by
  induction os generalizing m with
  | nil=>rfl
  | cons x xs ih=>
    simp only [List.flatMap_cons,List.mem_append,not_or] at h
    rw [List.foldl_cons,ih _ h.2]
    cases x with
    | reg a e=>simp only [writes,List.mem_singleton] at h;simp [Op.apply,Model.set,Ne.symm h.1]
    | ld a b c d=>simp only [writes,List.mem_singleton] at h;simp [Op.apply,Model.set,Ne.symm h.1]
    | sd=>rfl

theorem positive (o : Oracle) (s : MachineState) (base j id v k : Nat)
    (pos : s.pc=addr 577) (ptr : s.getReg .x16=CheckCapSlots.address base j)
    (load : CheckCapSlots.read (memoryView s) base j=BitVec.ofNat 32 id) (align : base%8=0)
    (space : base+4*j+4≤MEMORY_BYTES) (small : id<1024) (value : s.getReg .x17=W v) (bound : v<2^31)
    (counter : s.getReg .x15=W k) (heap : s.getReg .x23=W cap) (radix : s.getReg .x21=W 211)
    (mult : s.getReg .x26=W magic) :
    ∃ t,Segment o 14 s t [] ∧ t.pc=addr 591 ∧ t.getReg .x5=W v ∧ t.getReg .x17=W (v/211) ∧
      t.getReg .x15=W (k+1) ∧ t.getReg .x16=CheckCapSlots.address base (j+1) ∧
      LeafMemory.Agrees (memoryView t) (fix (memoryView s) id (v%211)) ∧
      (∀ r∉changed,t.getReg r=s.getReg r) := by
  let a:=CheckCapSlots.address base j
  let u:=(s.setReg .x6 ((s.getWord32 a).zeroExtend 64)).setPC (addr 578)
  have enter : Segment o 1 s u []:=CheckMemoryOps.loadU32 o s 577 .x6 .x16 a (by decide +kernel) pos ptr
    (CheckCapSlots.valid base j align space)
  let m:=CheckRecordHeader.model u
  have loaded : m.reg .x6=W id := by
    change (s.getWord32 a).zeroExtend 64=W id
    rw [CheckCapSlots.load_id _ _ _ align,load]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat];omega
  have capreg : m.reg .x23=W cap:=heap
  have slot : m.reg .x6 <<< (5 : Nat) + m.reg .x23+signExtend12 24=wordAddress (top id) := by
    rw [loaded,capreg];exact idAddress id
  have good : Checked m (ops id) := by
    simp only [ops,Checked,Op.Valid,Op.apply,true_and,and_true]
    exact ⟨⟨by unfold top cap;omega,slot⟩,⟨by unfold top cap;omega,slot⟩⟩
  obtain ⟨t,seg,loc,fit⟩:=CheckStraight.block o m (ops id) 578 (by change 578+13≤796;decide) (listed id) good u rfl
    (CheckRecordHeader.fits u)
  have ft : Fits t (after m id):=fit
  have val : m.reg .x17=W v:=value
  have mu : m.reg .x26=W magic:=mult
  have rad : m.reg .x21=W 211:=radix
  have q : rv64_mulhu (m.reg .x17) (m.reg .x26) >>> (6 : Nat)=W (v/211) := by rw [val,mu,quotient v bound]
  have saved : m.reg .x17+signExtend12 0=W v := by change m.reg .x17+0=W v;simpa using val
  have result : (after m id).mem=fix (memoryView s) id (v%211) := by
    let prod := (rv64_mulhu (m.reg .x17) (m.reg .x26) >>> (6 : Nat)) * m.reg .x21
    let dif := (m.reg .x17+signExtend12 0).truncate 32-prod.truncate 32
    change writeWord (memoryView s) (top id) ((memoryView s (top id)) ||| (dif.signExtend 64 <<< (32 : Nat)))=_
    dsimp only [dif,prod]
    rw [q,rad,saved,high];rfl
  refine ⟨t,by simpa only [List.nil_append,show (ops id).length=13 by rfl] using compose enter seg,loc,?_,?_,?_,?_,?_,?_⟩
  · exact (ft.registers .x5).trans saved
  · exact (ft.registers .x17).trans q
  · rw [ft.registers];change s.getReg .x15+W 1=W (k+1);rw [counter];exact (BitVec.ofNat_add ..).symm
  · rw [ft.registers];change s.getReg .x16+W 4=CheckCapSlots.address base (j+1)
    rw [ptr];unfold CheckCapSlots.address;rw [←BitVec.ofNat_add];congr 1
  · intro w hw; rw [ft.memory w hw,result]
  · intro r h
    refine (ft.registers r).trans ((untouched (ops id) m r ?_).trans ?_)
    · simpa [ops,writes,changed,and_comm,and_assoc,and_left_comm] using h
    · change (u.getReg r)=s.getReg r
      have ne : r≠.x6:=fun eq=>h (eq ▸ (by decide : Reg.x6∈changed))
      simp only [u,MachineState.getReg_setPC,TwoPermutationPrototype.Opening.getReg_setReg]
      simp [Ne.symm ne]
end CommitGolfCandidate.Reconstruction.CheckGroupDigit

