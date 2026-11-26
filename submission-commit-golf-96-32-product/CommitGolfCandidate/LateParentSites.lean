import CommitGolfCandidate.LatePacked
import CommitGolfCandidate.LateParents
namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def parentHeaderPC (d : Nat) := ([933, 996, 1063, 1130, 1197, 1264, 1331, 1398, 1465, 1532, 1597, 1662, 1727, 1792, 1857, 1922, 1987, 2052, 2117, 2182, 2247, 2283, 2307, 2325] : List Nat)[d]?.getD 0
def parentBodyPC (d : Nat) := ([944, 1011, 1078, 1145, 1212, 1279, 1346, 1413, 1480, 1545, 1610, 1675, 1740, 1805, 1870, 1935, 2000, 2065, 2130, 2195, 2259, 2295, 2319, 2337] : List Nat)[d]?.getD 0
def parentEndPC (d : Nat) := ([996, 1063, 1130, 1197, 1264, 1331, 1398, 1465, 1532, 1597, 1662, 1727, 1792, 1857, 1922, 1987, 2052, 2117, 2182, 2247, 2283, 2307, 2325, 2340] : List Nat)[d]?.getD 0
def tileWidth (d : Nat) := min 16 (levelCount (d+1))
def parentPC (d j : Nat) := parentBodyPC d + 3*j

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
  have allSmall : ∀ d : Fin 24, ∀ j : Fin 16, j.val < tileWidth d → parentPC d j+2 < 2351 := by decide
  have small := allSmall d j bound
  obtain ⟨src,dst,call⟩ := parent_words d j bound
  refine ⟨decoded_word _ (by omega) _ ?_,decoded_word _ (by omega) _ ?_,
    decoded_word _ small _ ?_⟩
  · rw [src]; fin_cases j <;> rfl
  · rw [dst]; fin_cases j <;> rfl
  · rw [call]; rfl

end CommitGolfCandidate.Late
