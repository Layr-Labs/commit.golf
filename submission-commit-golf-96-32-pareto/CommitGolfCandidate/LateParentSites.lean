import CommitGolfCandidate.LatePacked
import CommitGolfCandidate.LateParents
namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def parentHeaderPC (d : Nat) := ([935, 998, 1065, 1132, 1199, 1266, 1333, 1400, 1467, 1534, 1599, 1664, 1729, 1794, 1859, 1924, 1989, 2054, 2119, 2184, 2249, 2285, 2309, 2327] : List Nat)[d]?.getD 0
def parentBodyPC (d : Nat) := ([946, 1013, 1080, 1147, 1214, 1281, 1348, 1415, 1482, 1547, 1612, 1677, 1742, 1807, 1872, 1937, 2002, 2067, 2132, 2197, 2261, 2297, 2321, 2339] : List Nat)[d]?.getD 0
def parentEndPC (d : Nat) := ([998, 1065, 1132, 1199, 1266, 1333, 1400, 1467, 1534, 1599, 1664, 1729, 1794, 1859, 1924, 1989, 2054, 2119, 2184, 2249, 2285, 2309, 2327, 2342] : List Nat)[d]?.getD 0
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
  have allSmall : ∀ d : Fin 24, ∀ j : Fin 16, j.val < tileWidth d → parentPC d j+2 < 2353 := by decide
  have small := allSmall d j bound
  obtain ⟨src,dst,call⟩ := parent_words d j bound
  refine ⟨decoded_word _ (by omega) _ ?_,decoded_word _ (by omega) _ ?_,
    decoded_word _ small _ ?_⟩
  · rw [src]; fin_cases j <;> rfl
  · rw [dst]; fin_cases j <;> rfl
  · rw [call]; rfl

end CommitGolfCandidate.Late
