import CommitGolfCandidate.LatePacked
import CommitGolfCandidate.LateParents
namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def parentHeaderPC (d : Nat) := ([935, 1016, 1143, 1250, 1377, 1484, 1611, 1718, 1845, 1950, 2075, 2180, 2305, 2410, 2535, 2640, 2765, 2870, 2995, 3100, 3156, 3192, 3216, 3236] : List Nat)[d]?.getD 0
def parentBodyPC (d : Nat) := ([946, 1031, 1158, 1265, 1392, 1499, 1626, 1733, 1858, 1963, 2088, 2193, 2318, 2423, 2548, 2653, 2778, 2883, 3008, 3112, 3168, 3204, 3228, 3248] : List Nat)[d]?.getD 0
def parentEndPC (d : Nat) := ([1016, 1143, 1250, 1377, 1484, 1611, 1718, 1845, 1950, 2075, 2180, 2305, 2410, 2535, 2640, 2765, 2870, 2995, 3100, 3156, 3192, 3216, 3236, 3251] : List Nat)[d]?.getD 0
def tileWidth (d : Nat) := min 16 (levelCount (d+1))
def maskedPhase (d : Nat) := 0<23-d ∧ 23-d≤22
instance (d : Nat) : Decidable (maskedPhase d) := inferInstanceAs (Decidable (_ ∧ _))
def laneExtra (d : Nat) := if maskedPhase d then 1 else 0
def laneWidth (d : Nat) := 3+laneExtra d
def backImm (d : Nat) : BitVec 13 := if maskedPhase d then 7924 else 7988
def parentPC (d j : Nat) := parentBodyPC d + laneWidth d*j

def tailBank (d p : Nat) := decide (16≤levelCount (d+1) ∧ levelCount (d+1)/16≤p/16)
def bankWidth (d : Nat) (tail : Bool) := if tail then levelCount (d+1)%16 else tileWidth d
def bankPC (d : Nat) (tail : Bool) (j : Nat) := parentPC d j+(if tail then laneWidth d*16+4 else 0)
def lanePC (d p : Nat) := bankPC d (tailBank d p) (p%16)
theorem bankFits (d p : Nat) (hi : p<levelCount (d+1)) : p%16<bankWidth d (tailBank d p) := by
  by_cases b : 16≤levelCount (d+1) ∧ levelCount (d+1)/16≤p/16
  · have yes : tailBank d p=true:=decide_eq_true b
    rw [yes];change p%16<levelCount (d+1)%16;omega
  · have no : tailBank d p=false:=decide_eq_false b
    rw [no];change p%16<min 16 (levelCount (d+1));omega

set_option maxRecDepth 5000 in
set_option maxHeartbeats 2000000 in
private theorem parent_words : ∀ d : Fin 24, ∀ tail : Bool, ∀ j : Fin 16, (tail=false ∨ 16≤levelCount (d.val+1)) → j.val < bankWidth d tail →
    packedWord (bankPC d tail j) = BitVec.ofNat 32 (96*j.val*2^20 + 21*2^15 + 10*128+19) ∧
    packedWord (bankPC d tail j+1) = BitVec.ofNat 32 (gapOffset j*2^20 + 22*2^15 + 12*128+19) ∧
    packedWord (bankPC d tail j+2) = 0x73 := by decide

theorem parent_sites (d : Fin 24) (tail : Bool) (j : Fin 16) (has : tail=false ∨ 16≤levelCount (d.val+1)) (bound : j.val < bankWidth d tail) :
    AtWord (bankPC d tail j) (.ADDI .x10 .x21 (BitVec.ofNat 12 (96*j.val))) ∧
    AtWord (bankPC d tail j+1) (.ADDI .x12 .x22 (BitVec.ofNat 12 (gapOffset j))) ∧
    AtWord (bankPC d tail j+2) .ECALL := by
  have allSmall : ∀ d : Fin 24, ∀ tail : Bool, ∀ j : Fin 16, (tail=false ∨ 16≤levelCount (d.val+1)) → j.val < bankWidth d tail → bankPC d tail j+2 < 3262 := by decide
  have small := allSmall d tail j has bound
  obtain ⟨src,dst,call⟩ := parent_words d tail j has bound
  refine ⟨decoded_word _ (by omega) _ ?_,decoded_word _ (by omega) _ ?_,
    decoded_word _ small _ ?_⟩
  · rw [src]; fin_cases j <;> rfl
  · rw [dst]; fin_cases j <;> rfl
  · rw [call]; rfl

theorem hasBank (d : Fin 24) (p : Nat) : tailBank d p=false ∨ 16≤levelCount (d.val+1) := by
  by_cases a : 16≤levelCount (d.val+1)
  · exact Or.inr a
  · left;simp [tailBank,a]
theorem laneLast (d : Fin 24) (p : Nat) (hi : p<levelCount (d.val+1)) (last : p%16=15) :
    lanePC d p=parentBodyPC d+laneWidth d*15 := by
  have no : ¬(16≤levelCount (d.val+1) ∧ levelCount (d.val+1)/16≤p/16):=by omega
  simp [lanePC,bankPC,parentPC,tailBank,no,last]
end CommitGolfCandidate.Late
