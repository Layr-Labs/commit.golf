import CommitGolfCandidate.LateLinear
import CommitGolfCandidate.LateLeafRun

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def latchStart (i : Fin 32) := leafPC i 0+12

def updates (i : Fin 32) : List Instr :=
  (if i.val%8 = 7 then [.ADD .x8 .x8 .x29] else []) ++
  (if i.val%16 = 15 then [.ADDI .x18 .x18 1536] else []) ++
  (if i.val = 31 then [.ADDI .x23 .x23 1536, .ADDI .x20 .x20 4095] else [])

def updatesState (s : MachineState) (i : Fin 32) := (updates i).foldl execInstrBr s

private theorem words (i : Fin 32) (j : Nat) (hj : j < (updates i).length) :
    (leafWords[latchStart i+j-528]?).bind decodeInstruction = some (.base ((updates i)[j])) := by
  have len : (updates i).length ≤ 4 := by unfold updates; split <;> split <;> split <;> decide
  have hi : j < 4 := hj.trans_le len
  fin_cases i <;> interval_cases j <;> first | rfl | contradiction

private theorem plain (i : Fin 32) (op : Instr) (hm : op ∈ updates i) : straight op := by
  have cases : op = .ADD .x8 .x8 .x29 ∨ op = .ADDI .x18 .x18 1536 ∨
      op = .ADDI .x23 .x23 1536 ∨ op = .ADDI .x20 .x20 4095 := by
    unfold updates at hm
    split at hm <;> split at hm <;> split at hm <;> simp_all <;> tauto
  rcases cases with rfl | rfl | rfl | rfl <;> intro s <;> exact ⟨rfl,rfl,rfl⟩

theorem execute_updates (s : MachineState) (i : Fin 32) (fuel : Nat) (pc : s.pc = pcAt (latchStart i)) :
    execute commitImage (fuel+(updates i).length) s true =
      (do let r ← execute commitImage fuel (updatesState s i) true
          return r.charge (updates i).length 0) := by
  apply execute_linear _ _ _ _ pc (plain i)
  intro j hj t tp
  have len : (updates i).length ≤ 4 := by unfold updates; split <;> split <;> split <;> decide
  have hi := i.isLt
  have off : 528 ≤ latchStart i+j ∧ latchStart i+j < 1040 := by unfold latchStart leafPC; omega
  obtain ⟨w, atw, dec⟩ := Option.bind_eq_some_iff.mp (words i j hj)
  exact (fetch_word tp (by omega) ((smallWord _ off.1 off.2).trans atw)).trans dec

theorem last_branch (s : MachineState) (fuel : Nat) (pc : s.pc = pcAt 931) :
    execute commitImage (fuel+1) s true =
    (do let r ← execute commitImage fuel (execInstrBr s (.BNE .x20 .x0 6624)) true
        return r.charge 1 0) := by
  have w := (smallWord 931 (by decide) (by decide)).trans (show leafWords[931-528]? = some 0x9e0a10e3 by rfl)
  exact execute_ordinary_step _ _ _ _ _ _ ((fetch_word pc (by decide) w).trans (by rfl)) rfl

end CommitGolfCandidate.Late
