import CommitGolfCandidate.HybWrapKit

/-! Code facts for the wrapper's five tail clears, by splitting `wrapCode` instead of evaluating it. -/

namespace TwoPermutationPrototype.HybWrap
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64

set_option maxRecDepth 100000

theorem wrap_at_mid (P C S : List Instr) (h : wrapCode = P ++ (C ++ S)) : WrapAt P.length C := by
  intro i hi
  rw [h, List.getElem?_append_right (by omega), show P.length + i - P.length = i by omega,
    List.getElem?_append_left hi]

theorem zero_stores_len (b : Reg) (n : Nat) : (zeroStores b n).length = n := by simp [zeroStores]

/-- Everything before the first clear. -/
def tailPre : List Instr :=
  entryCode ++ saveCode ++ tableSetup ++ tableCode ++ hashSetup ++ hashCode ++ expSetup ++ recordCopy ++
    saltCode ++ levelsCode ++ latchCode ++ (liCode .x17 1688 ++ [.MUL .x17 .x16 .x17, .ADD .x6 .x29 .x17])

theorem tail_pre_len : tailPre.length = 3924 := by decide

def zrun : List Instr := zeroStores .x6 255 ++ [.ADDI .x6 .x6 2040]

theorem zrun_len : zrun.length = 256 := by simp [zrun, zero_stores_len]

def tailRest : List Instr :=
  zeroStores .x6 211 ++ liCode .x6 1688 ++ restoreRegs ++ zeroedRegs.map (fun r => .ADDI r .x0 0) ++
    [.JAL .x0 2074548] ++ emptyCode ++ rejectCode

theorem wrap_split :
    wrapCode = tailPre ++ (zrun ++ (zrun ++ (zrun ++ (zrun ++ tailRest)))) := by
  simp only [wrapCode, tailCode, tailPre, zrun, tailRest, List.append_assoc, List.cons_append, List.nil_append]

theorem tail_zero_1 : WrapAt 3924 (zeroStores .x6 255) := by
  have h : wrapCode = tailPre ++ (zeroStores .x6 255 ++ ([.ADDI .x6 .x6 2040] ++ (zrun ++ (zrun ++ (zrun ++ tailRest))))) := by
    rw [wrap_split]; simp only [zrun, List.append_assoc, List.cons_append, List.nil_append]
  rw [← tail_pre_len]; exact wrap_at_mid _ _ _ h

theorem tail_zero_2 : WrapAt 4180 (zeroStores .x6 255) := by
  have h : wrapCode = (tailPre ++ zrun) ++ (zeroStores .x6 255 ++ ([.ADDI .x6 .x6 2040] ++ (zrun ++ (zrun ++ tailRest)))) := by
    rw [wrap_split]; simp only [zrun, List.append_assoc, List.cons_append, List.nil_append]
  have l : (tailPre ++ zrun).length = 4180 := by rw [List.length_append, tail_pre_len, zrun_len]
  rw [← l]; exact wrap_at_mid _ _ _ h

theorem tail_zero_3 : WrapAt 4436 (zeroStores .x6 255) := by
  have h : wrapCode = (tailPre ++ zrun ++ zrun) ++ (zeroStores .x6 255 ++ ([.ADDI .x6 .x6 2040] ++ (zrun ++ tailRest))) := by
    rw [wrap_split]; simp only [zrun, List.append_assoc, List.cons_append, List.nil_append]
  have l : (tailPre ++ zrun ++ zrun).length = 4436 := by rw [List.length_append, List.length_append, tail_pre_len, zrun_len]
  rw [← l]; exact wrap_at_mid _ _ _ h

theorem tail_zero_4 : WrapAt 4692 (zeroStores .x6 255) := by
  have h : wrapCode = (tailPre ++ zrun ++ zrun ++ zrun) ++ (zeroStores .x6 255 ++ ([.ADDI .x6 .x6 2040] ++ tailRest)) := by
    rw [wrap_split]; simp only [zrun, List.append_assoc, List.cons_append, List.nil_append]
  have l : (tailPre ++ zrun ++ zrun ++ zrun).length = 4692 := by
    rw [List.length_append, List.length_append, List.length_append, tail_pre_len, zrun_len]
  rw [← l]; exact wrap_at_mid _ _ _ h

theorem tail_zero_5 : WrapAt 4948 (zeroStores .x6 211) := by
  have h : wrapCode = (tailPre ++ zrun ++ zrun ++ zrun ++ zrun) ++ (zeroStores .x6 211 ++ (liCode .x6 1688 ++ restoreRegs ++
      zeroedRegs.map (fun r => .ADDI r .x0 0) ++ [.JAL .x0 2074548] ++ emptyCode ++ rejectCode)) := by
    rw [wrap_split]; simp only [zrun, tailRest, List.append_assoc, List.cons_append, List.nil_append]
  have l : (tailPre ++ zrun ++ zrun ++ zrun ++ zrun).length = 4948 := by
    rw [List.length_append, List.length_append, List.length_append, List.length_append, tail_pre_len, zrun_len]
  rw [← l]; exact wrap_at_mid _ _ _ h

end TwoPermutationPrototype.HybWrap
