import CommitGolfCandidate.GroupOpenImage
import CommitGolfCandidate.Execution
import CommitGolfCandidate.TwoPermutationOpeningCopy

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000

def address (i : Nat) := BitVec.ofNat 64 (4096+4*i)
abbrev Row := Nat × Instr

def walkRows (s : MachineState) (rows : List Row) := rows.foldl (fun t p => execInstrBr t p.2) s
def price (rows : List Row) := (rows.map fun p => instructionCycles (.base p.2)).sum

def legal : List Row → MachineState → Prop
  | [],_ => True
  | (i,op)::tail,s =>
      s.pc=address i ∧ ordinaryStep s (.base op)=some (execInstrBr s op) ∧ legal tail (execInstrBr s op)

def presentRows (rows : List Row) :=
  ∀ p∈rows, ∀ st : MachineState, st.pc=address p.1 → fetch openingImage st=some (.base p.2)

theorem walk_rows_run (s : MachineState) (rows : List Row) (valid : legal rows s) (code : presentRows rows)
    (fuel : Nat) (coins : Bool) :
    execute openingImage (rows.length+fuel) s coins =
      (do let z ← execute openingImage fuel (walkRows s rows) coins;return z.charge (price rows) 0) := by
  induction rows generalizing s with
  | nil => simp [walkRows,price,Execution.charge]
  | cons p tail ih =>
    rcases p with ⟨i,op⟩
    obtain ⟨pc,ord,more⟩ := valid
    have fetch := code (i,op) (by simp) s pc
    rw [show ((i,op)::tail).length+fuel=(tail.length+fuel)+1 by simp;omega,
      execute_ordinary_step _ _ _ _ _ _ fetch ord,ih _ more (fun p hp => code p (List.mem_cons_of_mem _ hp))]
    simp [walkRows,price,Execution.charge,bind_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

def plain (op : Instr) := match op with
  | .ECALL | .EBREAK | .CSRS .. | .LI .. | .MV .. | .NOP => false
  | _ => true

theorem ord_iff (s : MachineState) (op : Instr) (yes : plain op=true) :
    ordinaryStep s (.base op)=some (execInstrBr s op) ↔ memoryArgumentsValid s op=true := by
  cases op <;> simp_all [plain,ordinaryStep] <;> split <;> simp_all

def preRows : List Row := [(739,.LD .x6 .x14 0),(740,.ANDI .x28 .x6 2047),(741,.REMU .x28 .x28 .x29),
  (742,.SUB .x7 .x6 .x28),(743,.SLLI .x7 .x7 8),(744,.ADD .x7 .x7 .x26),(745,.SD .x10 .x7 0)]

def postRows (direct last : Bool) : List Row :=
  [(747,.ADDI .x7 .x28 (-1)),(748,.SLLI .x7 .x7 4),(749,.BNE .x28 .x0 8)] ++
  (if direct then [(750,.ADDI .x7 .x0 184)] else []) ++
  [(751,.ADD .x7 .x7 .x12),(752,.SLLI .x30 .x6 4),(753,.ADD .x30 .x30 .x22),
   (754,.LD .x31 .x7 0),(755,.SD .x30 .x31 0),(756,.LD .x31 .x7 8),(757,.SD .x30 .x31 8),
   (758,.ADDI .x14 .x14 8),(759,.ADDI .x17 .x17 (-1)),(760,.BNE .x17 .x0 8108)] ++
  (if last then [(761,.JAL .x0 2094168)] else [])

private theorem row_fetch (row : Row) (bounded : row.1<762) (dec : (openingImage.code[row.1]?).bind Opening.decodeBase=some row.2) :
    ∀ st : MachineState, st.pc=address row.1 → fetch openingImage st=some (.base row.2) :=
  fun st pc => packed_fetch_base st _ _ bounded pc dec

theorem pre_row_fetch : presentRows preRows := by
  intro p hp
  apply row_fetch
  · simp only [preRows,List.mem_cons,List.not_mem_nil,or_false] at hp;rcases hp with h|h|h|h|h|h|h <;> subst p <;> decide
  · simp only [preRows,List.mem_cons,List.not_mem_nil,or_false] at hp;rcases hp with h|h|h|h|h|h|h <;> subst p <;> decide +kernel

theorem post_row_fetch (direct last : Bool) : presentRows (postRows direct last) := by
  have raw : ∀ d l : Bool, ∀ i : Fin (postRows d l).length, let row := (postRows d l)[i];
      row.1<762 ∧ (openingImage.code[row.1]?).bind Opening.decodeBase=some row.2 := by decide +kernel
  intro p hp;obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp hp
  subst p
  exact row_fetch _ (raw direct last ⟨i,hi⟩).1 (raw direct last ⟨i,hi⟩).2

end TwoPermutationPrototype.GroupedOpening
