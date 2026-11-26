import CommitGolfCandidate.LatePacked
import CommitGolfCandidate.LateParents
namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def parentHeaderPC (d : Nat) := ([935, 998, 1065, 1148, 1231, 1314, 1397, 1480, 1563, 1646, 1727, 1808, 1889, 1970, 2051, 2132, 2213, 2294, 2375, 2456, 2537, 2581, 2609, 2629] : List Nat)[d]?.getD 0
def parentBodyPC (d : Nat) := ([946, 1013, 1080, 1163, 1246, 1329, 1412, 1495, 1578, 1659, 1740, 1821, 1902, 1983, 2064, 2145, 2226, 2307, 2388, 2469, 2549, 2593, 2621, 2641] : List Nat)[d]?.getD 0
def parentEndPC (d : Nat) := ([998, 1065, 1148, 1231, 1314, 1397, 1480, 1563, 1646, 1727, 1808, 1889, 1970, 2051, 2132, 2213, 2294, 2375, 2456, 2537, 2581, 2609, 2629, 2644] : List Nat)[d]?.getD 0
def tileWidth (d : Nat) := min 16 (levelCount (d+1))
def maskedPhase (d : Nat) := 0<23-d ∧ 23-d≤21
instance (d : Nat) : Decidable (maskedPhase d) := inferInstanceAs (Decidable (_ ∧ _))
def laneExtra (d : Nat) := if maskedPhase d then 1 else 0
def laneWidth (d : Nat) := 3+laneExtra d
def backImm (d : Nat) : BitVec 13 := if maskedPhase d then 7924 else 7988
def parentPC (d j : Nat) := parentBodyPC d + laneWidth d*j

set_option maxRecDepth 5000 in
set_option maxHeartbeats 2000000 in
private theorem parent_words : ∀ d : Fin 24, ∀ j : Fin 16, j.val < tileWidth d →
    packedWord (parentPC d j) = BitVec.ofNat 32 (96*j.val*2^20 + 21*2^15 + 10*128+19) ∧
    packedWord (parentPC d j+1) = BitVec.ofNat 32 (gapOffset j*2^20 + 22*2^15 + 12*128+19) ∧
    packedWord (parentPC d j+2) = 0x73 := by decide

theorem parent_sites (d : Fin 24) (j : Fin 16) (bound : j.val < tileWidth d) :
    AtWord (parentPC d j) (.ADDI .x10 .x21 (BitVec.ofNat 12 (96*j.val))) ∧
    AtWord (parentPC d j+1) (.ADDI .x12 .x22 (BitVec.ofNat 12 (gapOffset j))) ∧
    AtWord (parentPC d j+2) .ECALL := by
  have allSmall : ∀ d : Fin 24, ∀ j : Fin 16, j.val < tileWidth d → parentPC d j+2 < 2655 := by decide
  have small := allSmall d j bound
  obtain ⟨src,dst,call⟩ := parent_words d j bound
  refine ⟨decoded_word _ (by omega) _ ?_,decoded_word _ (by omega) _ ?_,
    decoded_word _ small _ ?_⟩
  · rw [src]; fin_cases j <;> rfl
  · rw [dst]; fin_cases j <;> rfl
  · rw [call]; rfl

end CommitGolfCandidate.Late
