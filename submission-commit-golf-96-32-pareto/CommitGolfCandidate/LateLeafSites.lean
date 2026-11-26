import CommitGolfCandidate.LateCalls
import CommitGolfCandidate.LateLayout

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

/-- Index of the first address instruction. Each eighth leaf advances the message
pointer, and each sixteenth leaf also advances the row pointer. -/
def leafPC (slot call : Nat) := 539+12*slot+slot/8+slot/16+3*call

def sourceReg (call : Nat) : Reg := if call = 3 then .x18 else .x8
def targetReg : Nat → Reg
  | 0 => .x8 | 3 => .x23 | _ => .x18

def sourceOffset (slot call : Nat) : Nat :=
  match call with
  | 0 => 256*(slot%8)
  | 1 => 256*(slot%8)+64
  | 2 => 256*(slot%8)+160
  | _ => 96*(slot%16)

def targetOffset (slot call : Nat) : Nat :=
  let content := 96*(slot%16) + 32*(slot%2)
  match call with
  | 0 => 256*(slot%8)+64
  | 1 => content
  | 2 => content+32
  | _ => 32*slot

def sourceInstr (slot call : Nat) : Instr :=
  .ADDI .x10 (sourceReg call) (BitVec.ofNat 12 (sourceOffset slot call))

def targetInstr (slot call : Nat) : Instr :=
  .ADDI .x12 (targetReg call) (BitVec.ofNat 12 (targetOffset slot call))

def sourceWord (slot call : Nat) : BitVec 32 :=
  BitVec.ofNat 32 ((sourceOffset slot call)*2^20 + (if call = 3 then 18 else 8)*2^15 + 10*128 + 19)

def targetWord (slot call : Nat) : BitVec 32 :=
  BitVec.ofNat 32 ((targetOffset slot call)*2^20 + (match call with | 0 => 8 | 3 => 23 | _ => 18)*2^15 + 12*128 + 19)

def leafWords := tail528 ++ (tail656 ++ (tail784 ++ tail912))

theorem smallWord (n : Nat) (lo : 528 ≤ n) (hi : n < 1040) :
    commitImage.code[n]? = leafWords[n-528]? := by
  have hs : setupWords.length = 16 := rfl
  have hr : randomWords.length = 512 := by simp [randomWords]
  change (setupWords ++ (randomWords ++ _))[n]? = _
  rw [List.getElem?_append_right (by rw [hs]; omega), hs,
    List.getElem?_append_right (by rw [hr]; omega),hr, show n-16-512 = n-528 by omega]
  unfold leafWords
  have e₀ : tail528.length = 128 := rfl
  have e₁ : tail656.length = 128 := rfl
  have e₂ : tail784.length = 128 := rfl
  have e₃ : tail912.length = 128 := rfl
  by_cases a : n-528 < 128
  · simp only [List.getElem?_append_left (show n-528 < tail528.length by omega)]
  · simp only [List.getElem?_append_right (show tail528.length ≤ n-528 by omega),e₀]
    by_cases b : n-528-128 < 128
    · simp only [List.getElem?_append_left (show n-528-128 < tail656.length by omega)]
    · simp only [List.getElem?_append_right (show tail656.length ≤ n-528-128 by omega),e₁]
      by_cases c : n-528-128-128 < 128
      · simp only [List.getElem?_append_left (show n-528-128-128 < tail784.length by omega)]
      · simp only [List.getElem?_append_right (show tail784.length ≤ n-528-128-128 by omega),e₂,
          List.getElem?_append_left (show n-528-128-128-128 < tail912.length by omega)]

/- Validate the words as small fixed lists, independently of the machine state. -/
set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
private theorem leaf_words : ∀ i : Fin 32, ∀ j : Fin 4,
    leafWords[leafPC i j - 528]? = some (sourceWord i j) ∧
    leafWords[leafPC i j + 1 - 528]? = some (targetWord i j) ∧
    leafWords[leafPC i j + 2 - 528]? = some 0x73 := by decide

theorem leaf_fetch (i : Fin 32) (j : Fin 4) :
    AtWord (leafPC i j) (sourceInstr i j) ∧ AtWord (leafPC i j+1) (targetInstr i j) ∧
      AtWord (leafPC i j+2) .ECALL := by
  obtain ⟨x,y,z⟩ := leaf_words i j
  have range : 528 ≤ leafPC i j ∧ leafPC i j+2 < 1040 := by
    have := i.isLt; have := j.isLt; unfold leafPC; omega
  have dec (w : BitVec 32) (op : Instr) (n : Nat) (lo : 528 ≤ n) (hi : n < 1040)
      (e : leafWords[n-528]? = some w) (d : decodeInstruction w = some (.base op)) :
      AtWord n op := fun s pc => (fetch_word pc (by omega) ((smallWord n lo hi).trans e)).trans d
  refine ⟨dec _ _ _ (by omega) (by omega) x ?_, dec _ _ _ (by omega) (by omega) y ?_,
    dec _ _ _ (by omega) (by omega) z rfl⟩
  · fin_cases i <;> fin_cases j <;> rfl
  · fin_cases i <;> fin_cases j <;> rfl

end CommitGolfCandidate.Late
