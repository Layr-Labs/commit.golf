import CommitGolfCandidate.Stage3cCode
import CommitGolfCandidate.Execution

namespace CommitGolfCandidate.Chained.BinaryMachine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option Elab.async false

/-- One private draw is 40 bytes, five query-words, six cycles. -/
abbrev Draw40 := BitVec 320
def draw40 : OracleComp World Draw40 :=
  liftM ($ᵗ Draw40 : ProbComp Draw40)

theorem fetch_word {s : MachineState} {i : Nat} (ip : s.pc = pcAt i)
    (small : i < 11543) {w : BitVec 32} (atWord : commitImage.code[i]? = some w) :
    fetch commitImage s = decodeInstruction w := by
  have bound : 4096 + 4*i < 2^64 := by omega
  simp only [fetch, ip, pcAt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
  rw [if_pos (by constructor <;> omega)]
  simpa only [Nat.add_sub_cancel_left, Nat.mul_div_cancel_left _ (by decide : 0 < 4), atWord]

private theorem packed_at {n : Nat} (p : CommitGolf.ArtifactEncoding.Packed n) (i : Fin n) :
    (CommitGolf.ArtifactEncoding.decode 32 p)[i.val]?=some (p.get 32 i) := by
  simp only [CommitGolf.ArtifactEncoding.decode,List.getElem?_ofFn,dif_pos i.isLt]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
private theorem random_table : ∀ i : Fin 4096,
    atWord .commit ⟨12+i.val, by have := i.isLt; simp only [words]; omega⟩ =
      if i.val%2=0 then (0x73 : BitVec 32) else 0x0b850513 := by decide +kernel

private theorem random_word (k : Nat) (bound : k<4096) :
    commitImage.code[12+k]?=some (if k%2=0 then 0x73 else 0x0b850513) := by
  have site := random_table ⟨k,bound⟩
  exact (word_delivered .commit ⟨12+k, by simp only [words]; omega⟩).trans (congrArg some site)

def randomStep (s : MachineState) (w : Draw40) : MachineState :=
  execInstrBr (writeBits s (s.getReg .x10) w) (.ADDI .x10 .x10 184)

private theorem random_call (s : MachineState)
    (fetched : fetch commitImage s = some (.base .ECALL))
    (selector : s.getReg .x5 = 2) (length : s.getReg .x11 = 40)
    (valid : randomArgumentsValid s = true) (fuel : Nat) :
    execute commitImage (fuel+1) s true =
      (do let w ← draw40
          let result ← execute commitImage fuel (writeBits s (s.getReg .x10) w) true
          return result.charge 6 0) := by
  have resize (bits : Nat) (eq : bits = 320) :
      (do let w ← (liftM ($ᵗ BitVec bits : ProbComp (BitVec bits)) : OracleComp World _)
          let result ← execute commitImage fuel (writeBits s (s.getReg .x10) w) true
          return result.charge 6 0) =
      (do let w ← draw40
          let result ← execute commitImage fuel (writeBits s (s.getReg .x10) w) true
          return result.charge 6 0) := by subst bits; rfl
  simp only [execute, fetched, selector, show (2 : Word) ≠ 0 by decide,
    show (2 : Word) ≠ 1 by decide, if_false, valid, length]
  exact resize _ (by rw [length]; rfl)

/-- Two fetched machine instructions draw one word, write it in place and advance
the destination pointer. This includes the private draw in the continuation. -/
theorem execute_pair (s : MachineState) (j fuel : Nat) (bound : j < 2048)
    (ip : s.pc = pcAt (12+2*j)) (selector : s.getReg .x5 = 2)
    (length : s.getReg .x11 = 40) (valid : randomArgumentsValid s = true) :
    execute commitImage (fuel+2) s true =
      (do let w ← draw40
          let result ← execute commitImage fuel (randomStep s w) true
          return result.charge 7 0) := by
  have f : fetch commitImage s = some (.base .ECALL) := by
    have e := random_word (2*j) (by omega)
    rw [if_pos (by omega)] at e
    exact fetch_word ip (by omega) e |>.trans (by rfl)
  rw [random_call s f selector length valid]
  apply bind_congr
  intro w
  let t := writeBits s (s.getReg .x10) w
  have tp : t.pc = pcAt (12+(2*j+1)) := by
    change s.pc + 4 = _
    rw [ip]
    simp [pcAt, Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]
  have f' : fetch commitImage t = some (.base (.ADDI .x10 .x10 184)) := by
    have e := random_word (2*j+1) (by omega)
    rw [if_neg (by omega)] at e
    exact fetch_word tp (by omega) e |>.trans (by rfl)
  rw [execute_ordinary_step commitImage _ _ _ _ _ f' (show ordinaryStep t _ =
    some (randomStep s w) by rfl)]
  simp [Execution.charge, instructionCycles, bind_assoc, ← Nat.add_assoc]

end CommitGolfCandidate.Chained.BinaryMachine
