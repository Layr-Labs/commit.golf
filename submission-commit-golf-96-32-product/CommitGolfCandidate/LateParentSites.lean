import CommitGolfCandidate.LatePacked
import CommitGolfCandidate.LateParents
namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def parentHeaderPC (d : Nat) := ([933, 1047, 1165, 1315, 1465, 1615, 1765, 1915, 2065, 2215, 2363, 2511, 2659, 2807, 2955, 3103, 3251, 3399, 3515, 3631, 3692, 3728, 3752, 3770] : List Nat)[d]?.getD 0
def parentBodyPC (d : Nat) := ([947, 1065, 1183, 1333, 1483, 1633, 1783, 1933, 2083, 2231, 2379, 2527, 2675, 2823, 2971, 3119, 3267, 3415, 3531, 3644, 3704, 3740, 3764, 3782] : List Nat)[d]?.getD 0
def parentEndPC (d : Nat) := ([1047, 1165, 1315, 1465, 1615, 1765, 1915, 2065, 2215, 2363, 2511, 2659, 2807, 2955, 3103, 3251, 3399, 3515, 3631, 3692, 3728, 3752, 3770, 3785] : List Nat)[d]?.getD 0
def tileWidth (d : Nat) := min 32 (levelCount (d+1))
/-- Passes `d = 2..16` produce the truncated heights `3..17`: each of their parent sites has a
fourth instruction `SH x0, gapOffset j + 30 (x22)` clearing the top two bytes of the new node. -/
def cutPass (d : Nat) : Bool := decide (CutHeight (d+1))
def siteWidth (d : Nat) := if cutPass d then 4 else 3
def parentBias (d : Nat) := if 32 ≤ levelCount (d+1) then 1536 else 0
def parentSourceOffset (d j : Nat) := (96*j+4096-parentBias d)%4096

def parentPC (d j : Nat) := parentBodyPC d + siteWidth d*j
def cutOp (j : Nat) : Instr := .SH .x22 .x0 (BitVec.ofNat 12 (gapOffset j + 30))

set_option maxRecDepth 5000 in
set_option maxHeartbeats 2000000 in
private theorem parent_words : ∀ d : Fin 24, ∀ j : Fin 32, j.val < tileWidth d →
    packedWord (parentPC d j) = BitVec.ofNat 32 (parentSourceOffset d j.val*2^20 + 21*2^15 + 10*128+19) ∧
    packedWord (parentPC d j+1) = BitVec.ofNat 32 (gapOffset j*2^20 + 22*2^15 + 12*128+19) ∧
    packedWord (parentPC d j+2) = 0x73 ∧
    (cutPass d → packedWord (parentPC d j+3) = BitVec.ofNat 32 ((gapOffset j + 30) / 32 * 2^25 + 22 * 2^15 +
      1 * 2^12 + (gapOffset j + 30) % 32 * 2^7 + 0x23)) := by decide

set_option maxRecDepth 20000 in
theorem parent_sites (d : Fin 24) (j : Fin 32) (bound : j.val < tileWidth d) :
    AtWord (parentPC d j) (.ADDI .x10 .x21 (BitVec.ofNat 12 (parentSourceOffset d j.val))) ∧
    AtWord (parentPC d j+1) (.ADDI .x12 .x22 (BitVec.ofNat 12 (gapOffset j))) ∧
    AtWord (parentPC d j+2) .ECALL ∧
    (cutPass d → AtWord (parentPC d j+3) (cutOp j)) := by
  have allSmall : ∀ d : Fin 24, ∀ j : Fin 32, j.val < tileWidth d → parentPC d j+3 < 3796 := by decide
  have small := allSmall d j bound
  obtain ⟨src,dst,call,cutw⟩ := parent_words d j bound
  refine ⟨decoded_word _ (by omega) _ ?_,decoded_word _ (by omega) _ ?_,
    decoded_word _ (by omega) _ ?_,fun c => decoded_word _ small _ ?_⟩
  · rw [src]; unfold parentSourceOffset parentBias; split <;> fin_cases j <;> rfl
  · rw [dst]; fin_cases j <;> rfl
  · rw [call]; rfl
  · rw [cutw c]; fin_cases j <;> rfl

end CommitGolfCandidate.Late
