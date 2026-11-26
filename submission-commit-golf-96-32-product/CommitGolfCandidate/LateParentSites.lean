import CommitGolfCandidate.LatePacked
import CommitGolfCandidate.LateParents
namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def parentHeaderPC (d : Nat) := ([935, 998, 1065, 1148, 1231, 1314, 1397, 1480, 1563, 1646, 1727, 1808, 1889, 1970, 2051, 2132, 2213, 2294, 2359, 2424, 2489, 2525, 2549, 2567] : List Nat)[d]?.getD 0
def parentBodyPC (d : Nat) := ([946, 1013, 1080, 1163, 1246, 1329, 1412, 1495, 1578, 1659, 1740, 1821, 1902, 1983, 2064, 2145, 2226, 2307, 2372, 2437, 2501, 2537, 2561, 2579] : List Nat)[d]?.getD 0
def parentEndPC (d : Nat) := ([998, 1065, 1148, 1231, 1314, 1397, 1480, 1563, 1646, 1727, 1808, 1889, 1970, 2051, 2132, 2213, 2294, 2359, 2424, 2489, 2525, 2549, 2567, 2582] : List Nat)[d]?.getD 0
def tileWidth (d : Nat) := min 16 (levelCount (d+1))
/-- Passes `d = 2..16` produce the truncated heights `3..17`: each of their parent sites has a
fourth instruction `SH x0, gapOffset j + 30 (x22)` clearing the top two bytes of the new node. -/
def cutPass (d : Nat) : Bool := decide (CutHeight (d+1))
def siteWidth (d : Nat) := if cutPass d then 4 else 3
def parentPC (d j : Nat) := parentBodyPC d + siteWidth d*j
def cutOp (j : Nat) : Instr := .SH .x22 .x0 (BitVec.ofNat 12 (gapOffset j + 30))

set_option maxRecDepth 5000 in
set_option maxHeartbeats 2000000 in
private theorem parent_words : ∀ d : Fin 24, ∀ j : Fin 16, j.val < tileWidth d →
    packedWord (parentPC d j) = BitVec.ofNat 32 (96*j.val*2^20 + 21*2^15 + 10*128+19) ∧
    packedWord (parentPC d j+1) = BitVec.ofNat 32 (gapOffset j*2^20 + 22*2^15 + 12*128+19) ∧
    packedWord (parentPC d j+2) = 0x73 ∧
    (cutPass d → packedWord (parentPC d j+3) = BitVec.ofNat 32 ((gapOffset j + 30) / 32 * 2^25 + 22 * 2^15 +
      1 * 2^12 + (gapOffset j + 30) % 32 * 2^7 + 0x23)) := by decide

theorem parent_sites (d : Fin 24) (j : Fin 16) (bound : j.val < tileWidth d) :
    AtWord (parentPC d j) (.ADDI .x10 .x21 (BitVec.ofNat 12 (96*j.val))) ∧
    AtWord (parentPC d j+1) (.ADDI .x12 .x22 (BitVec.ofNat 12 (gapOffset j))) ∧
    AtWord (parentPC d j+2) .ECALL ∧
    (cutPass d → AtWord (parentPC d j+3) (cutOp j)) := by
  have allSmall : ∀ d : Fin 24, ∀ j : Fin 16, j.val < tileWidth d → parentPC d j+3 < 2593 := by decide
  have small := allSmall d j bound
  obtain ⟨src,dst,call,cutw⟩ := parent_words d j bound
  refine ⟨decoded_word _ (by omega) _ ?_,decoded_word _ (by omega) _ ?_,
    decoded_word _ (by omega) _ ?_,fun c => decoded_word _ small _ ?_⟩
  · rw [src]; fin_cases j <;> rfl
  · rw [dst]; fin_cases j <;> rfl
  · rw [call]; rfl
  · rw [cutw c]; fin_cases j <;> rfl

end CommitGolfCandidate.Late
