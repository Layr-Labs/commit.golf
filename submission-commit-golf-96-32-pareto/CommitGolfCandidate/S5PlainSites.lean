import CommitGolfCandidate.S5PhaseTable
import CommitGolfCandidate.S5TileSites
namespace CommitGolfCandidate.S5Machine
open CommitGolfCandidate.Chained
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 20000
set_option maxHeartbeats 15000000

def decoded (pc : Nat) := decodeInstruction (commitWord pc)
theorem decoded_site {pc : Nat} {op : Instr} (inside : pc<18492) (ok : decoded pc=some (.base op)) : Site .commit pc op := by
  apply site (p:=.commit) inside
  unfold decoded commitWord at ok;rw [dif_pos inside] at ok;exact ok

def fromDisp (j : Nat) := BitVec.ofNat 12 (2048+96*(j%42))
def toDisp (j : Nat) := BitVec.ofNat 12 (2048+Late.gapOffset (j%84))
def Mask238Sites (h : Height) (n : Nat) := wireWidth h=238 →
  decoded n=some (.base (.LHU .x31 .x12 28)) ∧ decoded (n+1)=some (.base (.AND .x31 .x31 .x30)) ∧
  decoded (n+2)=some (.base (.SW .x12 .x31 28))
instance (h n) : Decidable (Mask238Sites h n) := by unfold Mask238Sites;infer_instance
def MainSites (h : Height) (j : Nat) : Prop :=
  let n:=mainLane h j
  n+3<18492 ∧ decoded n=some (.base (.ADDI .x10 .x21 (fromDisp j))) ∧
  decoded (n+1)=some (.base (.ADDI .x12 .x22 (toDisp j))) ∧ decoded (n+2)=some (.base .ECALL) ∧
  (mask240 h=true → decoded (n+3)=some (.base (.SH .x12 .x0 30))) ∧ Mask238Sites h (n+3)
instance (h : Height) (j : Nat) : Decidable (MainSites h j) := by unfold MainSites;infer_instance

theorem main_table : ∀ h : Height, ¬chained h → ∀ j : Fin 252, j.val<tileSize h → MainSites h j.val := by decide +kernel

def TailSites (h : Height) : Prop :=
  let n:=tailPC h
  n+2<18492 ∧ decoded n=some (.base (.ADDI .x10 .x21 0)) ∧ decoded (n+1)=some (.base (.ADDI .x12 .x22 0)) ∧
    decoded (n+2)=some (.base .ECALL) ∧ (mask240 h=true → decoded (n+3)=some (.base (.SH .x12 .x0 30))) ∧ Mask238Sites h (n+3)
instance (h : Height) : Decidable (TailSites h) := by unfold TailSites;infer_instance

theorem tail_table : ∀ h : Height, ¬chained h → 0<remainder h → TailSites h := by decide +kernel

theorem source_disp : ∀ j : Fin 252, 2048#64+signExtend12 (fromDisp j.val)=BitVec.ofNat 64 (96*(j.val%42)) := by decide +kernel
theorem target_disp : ∀ j : Fin 252, 2048#64+signExtend12 (toDisp j.val)=BitVec.ofNat 64 (Late.gapOffset (j.val%84)) := by decide +kernel
end CommitGolfCandidate.S5Machine
