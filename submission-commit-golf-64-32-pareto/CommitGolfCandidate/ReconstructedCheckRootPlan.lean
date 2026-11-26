import CommitGolfCandidate.ReconstructedCheckBranch
import CommitGolfCandidate.ReconstructedCheckDecode
import CommitGolfCandidate.ReconstructedCheckParentRun

namespace CommitGolfCandidate.Reconstruction.CheckRootPlan
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding Binding.Machine CheckValues CheckRecorded CheckLink CheckParentRun
set_option maxRecDepth 18000
set_option maxHeartbeats 1100000

def cap := 4194336
def commitment := 4294971392

def code : Fin 4→List Op := ![
  [.plain (.basic (.arith (.lui .x11 256))),.plain (.basic (.arith (.addiw .x11 .x11 1))),
   .plain (.basic (.arith (.slli .x11 .x11 12))),.plain (.basic (.arith (.lui .x12 1024))),
   .plain (.basic (.ld .x13 .x12 32)),.plain (.basic (.ld .x14 .x11 0))],
  [.plain (.basic (.arith (.addiw .x12 .x12 32))),.plain (.basic (.ld .x13 .x12 8)),.plain (.basic (.ld .x14 .x11 8))],
  [.plain (.basic (.ld .x13 .x12 16)),.plain (.basic (.ld .x14 .x11 16))],
  [.plain (.basic (.ld .x11 .x11 24)),.plain (.basic (.ld .x12 .x12 24))]]

def begin : Fin 4→Nat := ![640,647,651,654]
def guardAt : Fin 4→Nat := ![646,650,653,656]
def offset : Fin 4→BitVec 13 := ![5836,5820,5808,5796]
def left (i : Fin 4) : Reg := if i.val=3 then .x12 else .x13
def right (i : Fin 4) : Reg := if i.val=3 then .x11 else .x14

def table : Tables where
  allowed:=fun a=>decide (a.region=0 ∧ a.offset.toNat%8=0 ∧
    ((cap≤a.offset.toNat ∧ a.offset.toNat<cap+32) ∨ (commitment≤a.offset.toNat ∧ a.offset.toNat<commitment+32)))
  initial:=fun _=>none

def start (i : Fin 4) : State where
  pc:=CommitBlocks.addr (begin i)
  regs := fun r => match r with
    | .x11 => if i.val = 0 then .reg r else .lit (BitVec.ofNat 64 commitment)
    | .x12 => if i.val = 0 then .reg r else .lit (BitVec.ofNat 64 (if i.val=1 then cap-32 else cap))
    | _ => .reg r
  writes:=[]

def run (i : Fin 4) := CheckLink.run table (CommitBlocks.addr (begin i)) (code i) (start i)
def done (i : Fin 4) := (run i).getD (start i)

def keep : List Reg := [.x2,.x8,.x10,.x24]

def receipt (i : Fin 4) : Prop := CheckDecode.checked (begin i) (code i)=true ∧ (run i).isSome=true ∧
    (done i).pc=CommitBlocks.addr (guardAt i) ∧ (done i).writes=[] ∧
    (done i).get (left i)=.old (loc 0 (cap+8*i.val)) ∧ (done i).get (right i)=.old (loc 0 (commitment+8*i.val)) ∧
    (∀ r ∈ keep, (done i).get r = .reg r) ∧
    (i.val<3 → (done i).get .x11=.lit (BitVec.ofNat 64 commitment) ∧
      (done i).get .x12=.lit (BitVec.ofNat 64 (if i.val=0 then cap-32 else cap)))
deriving instance Decidable for receipt

theorem checked : ∀ i : Fin 4,receipt i := by decide +kernel

private theorem words : ∀ i : Fin 4, CheckDecode.same (CheckStraight.actualAt (guardAt i))
    (.base (CheckBranch.branch .ne (left i) (right i) (offset i)))=true := by decide

private theorem targets : ∀ i : Fin 4, guardAt i<796 ∧
    CommitBlocks.addr (guardAt i)+signExtend13 (offset i)=CommitBlocks.addr 57 := by decide

theorem positive (o : Oracle) (env : Env) (layout : Layout env table) (i : Fin 4) (s : MachineState)
    (h : Matches env (start i) s) :
    ∃ t, Segment o ((code i).length+1) s t [] ∧
      t.pc=(if env.initial.getMem (BitVec.ofNat 64 (cap+8*i.val))=env.initial.getMem (BitVec.ofNat 64 (commitment+8*i.val))
        then CommitBlocks.addr (guardAt i+1) else CommitBlocks.addr 57) ∧
      (∀ p,t.getMem p=s.getMem p) ∧
      (∀ r ∈ keep, t.getReg r=env.initial.getReg r) ∧
      (i.val<3 → t.getReg .x11=BitVec.ofNat 64 commitment ∧ t.getReg .x12=BitVec.ofNat 64 (if i.val=0 then cap-32 else cap)) := by
  obtain ⟨read,existsRun,pc,empty,leftWord,rightWord,kept,next⟩:=checked i
  have runOk : run i=some (done i) := by unfold done;cases e:run i <;> simp_all
  obtain ⟨u,sg,hu,_⟩:=CheckLink.run_sound o env table layout (code i) _ (start i) (done i) s h (fun _ mem=>by cases mem)
    (CheckDecode.sound _ _ read) runOk
  have a:=CheckBranch.event o u (guardAt i) 57 .ne (left i) (right i) (offset i)
    (targets i).1 (hu.pc.trans pc) (CheckDecode.same_sound (words i)) (targets i).2
  have l : u.getReg (left i)=env.initial.getMem (BitVec.ofNat 64 (cap+8*i.val)) := by
    rw [hu.regs,leftWord];simp [Term.val,physical,loc,env.zero]
  have r : u.getReg (right i)=env.initial.getMem (BitVec.ofNat 64 (commitment+8*i.val)) := by
    rw [hu.regs,rightWord];simp [Term.val,physical,loc,env.zero]
  refine ⟨_,by simpa using compose sg a,?_,?_,?_,?_⟩
  · change (if CheckOrdinary.Cond.test .ne _ _ then _ else _)=_
    rw [l,r];by_cases yes : env.initial.getMem (BitVec.ofNat 64 (cap+8*i.val))=env.initial.getMem (BitVec.ofNat 64 (commitment+8*i.val)) <;>
      simp [CheckOrdinary.Cond.test,yes]
  · intro p;change u.getMem p=s.getMem p;rw [hu.mem,empty,h.mem];rfl
  · intro r member;change u.getReg r=_;rw [hu.regs,kept _ member];rfl
  · intro earlier
    simp only [MachineState.getReg_setPC]
    rw [hu.regs .x11,hu.regs .x12,(next earlier).1,(next earlier).2];exact ⟨rfl,rfl⟩

end CommitGolfCandidate.Reconstruction.CheckRootPlan
