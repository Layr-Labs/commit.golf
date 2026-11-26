import CommitGolfCandidate.ReconstructedCheckDecode
import CommitGolfCandidate.ReconstructedCheckParent

namespace CommitGolfCandidate.Reconstruction.CheckLowerFinish
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding Binding.Machine CheckValues CheckRecorded CheckParentRun
set_option maxRecDepth 16000
set_option maxHeartbeats 1100000

def code : List CheckLink.Op := [
  .plain (.basic (.ld .x12 .x8 3784)),
  .plain (.basic (.ld .x13 .x8 3792)),
  .plain (.basic (.ld .x14 .x8 3800)),
  .plain (.basic (.ld .x11 .x8 3808)),
  .plain (.basic (.arith (.addi .x22 .x22 4088))),
  .plain (.basic (.arith (.addiw .x21 .x21 4095))),
  .plain (.basic (.arith (.addi .x9 .x9 4088))),
  .plain (.basic (.arith (.addi .x10 .x0 9))),
  .plain (.basic (.branch .ge .x10 .x26 408))]

theorem decoded : CheckLink.Decoded code (CommitBlocks.addr 271) :=
  CheckDecode.sound _ _ (by decide)

def table : Tables where
  allowed:=fun a=>decide (a.region=1 ∧ a.offset.toNat%8=0 ∧ a.offset.toNat<32)
  initial:=fun _=>none

def start (d : Nat) : State where
  regs:=fun r=>match r with
    | .x8=>ptr 1 312
    | .x26=>.lit (BitVec.ofNat 64 d)
    | _=>.reg r
  writes:=[]
  pc:=CommitBlocks.addr 271

def result (d : Nat) := CheckLink.run table (CommitBlocks.addr 271) code (start d)
def done (d : Nat) := (result d).getD (start d)

def stateFacts (d : Nat) : Prop :=
  let m:=done d
  m.pc=CommitBlocks.addr (if d≤9 then 381 else 280) ∧ m.writes=[] ∧
  m.get .x12=.old (loc 1 0) ∧ m.get .x13=.old (loc 1 8) ∧
  m.get .x14=.old (loc 1 16) ∧ m.get .x11=.old (loc 1 24) ∧ m.get .x23=.reg .x23 ∧
  m.get .x9=.bin .add (.reg .x9) (.lit (-8)) ∧ m.get .x22=.bin .add (.reg .x22) (.lit (-8)) ∧
  m.get .x21=.bin .add32 (.reg .x21) (.lit (-1))
deriving instance Decidable for stateFacts

theorem receipt : ∀ d : Fin 24, (result d).isSome=true ∧ decide (stateFacts d)=true := by decide +kernel

theorem positive (o : Oracle) (env : Env) (layout : Layout env table) (d : Fin 24)
    (s : MachineState) (h : Matches env (start d) s) :
    ∃ t, Segment o 9 s t [] ∧ Matches env (done d) t ∧ stateFacts d := by
  have ok : result d=some (done d) := by have k:=(receipt d).1;unfold done;cases e:result d <;> simp_all
  obtain ⟨t,seg,ht,st⟩:=CheckLink.run_sound o env table layout code _ (start d) (done d) s h (fun _ h=>by cases h) decoded ok
  exact ⟨t,seg,ht,of_decide_eq_true (receipt d).2⟩

end CommitGolfCandidate.Reconstruction.CheckLowerFinish
