import CommitGolfCandidate.S4MixedFill
import CommitGolfCandidate.S4Compression
import CommitGolfCandidate.S4Wire
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
def pathLevels (b : Bool) := if b then 15 else 24
def nodeLength (b : Bool) (h : Nat) := fieldBytes b h
def extraLoad (h : Nat) := if h=0 then loadCode 384 32 else []
def nodeParts (b : Bool) (h : Nat) : List (List Instr) :=
  [loadCode 352 (nodeLength b h),extraLoad h,(segments (decide (h=0))).flatten,
   compressCode .x0 512 256 (projected (h+1))]
def nodeCode (b : Bool) (h : Nat) := (nodeParts b h).flatten
def firstNode (b : Bool) := (if b then 2668 else 21)+140
def nodePC (b : Bool) : Nat→Nat
  | 0=>firstNode b
  | h+1=>nodePC b h+(nodeCode b h).length
def siblingPtr (b : Bool) (r h : Nat) := proofBase+recordBytes b*r+fieldOffset b h
def pathPrice (b : Bool) : Nat→Nat | 0=>0 | h+1=>pathPrice b h+(nodeCode b h).length

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem sizes : ∀ b : Bool,∀ h : Fin 24,h.val<pathLevels b →
    (nodeLength b h=30 ∨ nodeLength b h=32) ∧
    fieldOffset b h+nodeLength b h+(if h.val=0 then 32 else 0)=fieldOffset b (h.val+1) ∧
    (nodeCode b h).length=fieldSteps (nodeLength b h)+(if h.val=0 then fieldSteps 32 else 0)+
      fillSize (decide (h.val=0))+(2+callSteps (projected (h.val+1))) ∧
    nodePC b (h.val+1)≤22492 ∧
    fieldOffset b h+nodeLength b h+(if h.val=0 then 32 else 0)≤recordBytes b :=by decide

theorem nodeSize (b : Bool) (h : Nat) (bh : h<pathLevels b) :
    (nodeLength b h=30 ∨ nodeLength b h=32) ∧
    fieldOffset b h+nodeLength b h+(if h=0 then 32 else 0)=fieldOffset b (h+1) ∧
    (nodeCode b h).length=fieldSteps (nodeLength b h)+(if h=0 then fieldSteps 32 else 0)+
      fillSize (decide (h=0))+(2+callSteps (projected (h+1))) ∧ nodePC b (h+1)≤22492 ∧
    fieldOffset b h+nodeLength b h+(if h=0 then 32 else 0)≤recordBytes b :=
  sizes b ⟨h,by unfold pathLevels at bh;split at bh <;> omega⟩ bh

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2500000 in
theorem pathEnd : nodePC false 24=2634 ∧ nodePC true 15=4343 ∧ pathPrice false 24≤2600 ∧ pathPrice true 15≤1600 := by decide
end CommitGolfCandidate.S4.Machine
