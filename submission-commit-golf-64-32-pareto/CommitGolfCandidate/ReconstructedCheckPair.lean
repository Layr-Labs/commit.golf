import CommitGolfCandidate.ReconstructedCheckDecode
import CommitGolfCandidate.ReconstructedCheckParent

namespace CommitGolfCandidate.Reconstruction.CheckPair
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding Binding.Machine CheckValues CheckRecorded CheckParentRun
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

def code : List CheckLink.Op := [
  .plain (.basic (.arith (.slli .x5 .x15 5))),
  .plain (.basic (.arith (.addi .x7 .x8 2048))),
  .plain (.basic (.arith (.addi .x7 .x7 3784))),
  .plain (.basic (.arith (.rr .add .x5 .x7 .x5))),
  .plain (.basic (.sd .x5 .x12 0)),
  .plain (.basic (.sd .x5 .x13 8)),
  .plain (.basic (.sd .x5 .x14 16)),
  .plain (.basic (.sd .x5 .x11 24)),
  .xori .x11 .x15 1,
  .plain (.basic (.arith (.slli .x11 .x11 5))),
  .plain (.basic (.arith (.rr .add .x11 .x7 .x11))),
  .plain (.basic (.sd .x11 .x10 0)),
  .plain (.basic (.sd .x11 .x16 8)),
  .plain (.basic (.sd .x11 .x17 16)),
  .plain (.basic (.sd .x11 .x6 24)),
  .plain (.basic (.arith (.srli .x23 .x23 1))),
  .plain (.basic (.arith (.addi .x26 .x26 4095))),
  .plain (.basic (.arith (.addi .x10 .x8 3784))),
  .plain (.basic (.arith (.addi .x12 .x8 2048))),
  .plain (.basic (.arith (.addi .x12 .x12 3784))),
  .plain (.basic (.arith (.addi .x11 .x21 0))),
  .auipc .x1 0,
  .jalr .x1 .x1 1620]

theorem decoded : CheckLink.Decoded code (CommitBlocks.addr 248) :=
  CheckDecode.sound _ _ (by decide)

def table : Tables where
  allowed:=fun a=>decide (a.region=1 ∧ a.offset.toNat%8=0 ∧ a.offset.toNat<64)
  initial:=fun _=>none

def start (side : Bool) : State where
  regs:=fun r=>match r with
    | .x15=>.lit (if side then 1 else 0)
    | .x8=>ptr 1 2360
    | _=>.reg r
  writes:=[]
  pc:=CommitBlocks.addr 248

def result (side : Bool) := CheckLink.run table (CommitBlocks.addr 248) code (start side)
def done (side : Bool) := (result side).getD (start side)

def current : Fin 4→Reg:=![.x12,.x13,.x14,.x11]
def sibling : Fin 4→Reg:=![.x10,.x16,.x17,.x6]

def fields (side : Bool) : Prop :=
  let m:=done side
  m.pc=CommitBlocks.addr 674 ∧ m.get .x1=.lit (CommitBlocks.addr 271) ∧ m.get .x2=.reg .x2 ∧
    m.get .x8=ptr 1 2360 ∧ m.get .x10=ptr 1 2048 ∧ m.get .x11=.reg .x21 ∧ m.get .x12=ptr 1 0 ∧
    m.get .x23=.bin .shr (.reg .x23) (.lit 1) ∧
    (∀ i : Fin 4,look table (loc 1 (8*i.val)) m.writes=.reg (if side then sibling i else current i)) ∧
    (∀ i : Fin 4,look table (loc 1 (32+8*i.val)) m.writes=.reg (if side then current i else sibling i))
deriving instance Decidable for fields

theorem receipt : ∀ side, (result side).isSome=true ∧ decide (fields side)=true := by decide +kernel

theorem positive (o : Oracle) (env : Env) (layout : Layout env table) (side : Bool) (s : MachineState) (h : Matches env (start side) s) :
    ∃ t, Segment o 23 s t [] ∧ Matches env (done side) t ∧ Safe table (done side).writes ∧ fields side := by
  have ok : result side=some (done side) := by have k:=(receipt side).1; unfold done;cases e:result side <;> simp_all
  obtain ⟨t,seg,ht,st⟩:=CheckLink.run_sound o env table layout code _ (start side) (done side) s h (fun _ h=>by cases h) decoded ok
  exact ⟨t,seg,ht,st,of_decide_eq_true (receipt side).2⟩

end CommitGolfCandidate.Reconstruction.CheckPair
