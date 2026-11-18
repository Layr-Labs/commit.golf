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

/-! Pair-heads salt loop (opening words 739-776). The rows before the oracle call branch on the group (A/B),
in place / copy, and the 12th leaf of a 12-leaf group; `preRows b ip tw` is the walk for one choice. -/
def headRows : List Row := [(739,.LD .x6 .x14 0),(740,.SRLI .x28 .x6 1),(741,.ANDI .x7 .x28 2047),
  (742,.REMU .x7 .x7 .x29),(743,.SUB .x28 .x28 .x7),(744,.ADDI .x30 .x0 5),(745,.BLTU .x7 .x30 12)]
def groupRows (b : Bool) : List Row := if b then [(746,.ADDI .x7 .x7 (-5)),(747,.ADDI .x28 .x28 5)] else []
def parityRows : List Row := [(748,.ANDI .x30 .x6 1),(749,.BNE .x7 .x0 16)]
def placeRows : List Row := [(750,.SUB .x31 .x0 .x30),(751,.ANDI .x31 .x31 184),(752,.JAL .x0 36)]
def offsetRows : List Row := [(753,.SLLI .x31 .x7 5),(754,.SLLI .x30 .x30 4),(755,.ADD .x31 .x31 .x30),
  (756,.ADDI .x31 .x31 (-16)),(757,.ADDI .x30 .x0 160),(758,.BNE .x31 .x30 12)]
def twelfthRows (tw : Bool) : List Row := if tw then [(759,.ADDI .x28 .x28 (-5)),(760,.ADDI .x31 .x0 144)] else []
def slotRows (ip tw : Bool) : List Row := if ip then placeRows else offsetRows++twelfthRows tw
def counterRows : List Row := [(761,.SLLI .x28 .x28 9),(762,.ADD .x28 .x28 .x26),(763,.ADDI .x28 .x28 256),
  (764,.SD .x10 .x28 0)]
def preRows (b ip tw : Bool) : List Row := headRows++groupRows b++parityRows++slotRows ip tw++counterRows

def selectRows : List Row := [(766,.ADD .x31 .x31 .x12),(767,.SLLI .x30 .x6 4),(768,.ADD .x30 .x30 .x22)]
def copyRows : List Row := [(769,.LD .x28 .x31 0),(770,.SD .x30 .x28 0),(771,.LD .x28 .x31 8),(772,.SD .x30 .x28 8)]
def nextRows (last : Bool) : List Row := [(773,.ADDI .x14 .x14 8),(774,.ADDI .x17 .x17 (-1)),(775,.BNE .x17 .x0 8048)] ++
  (if last then [(776,.JAL .x0 2094108)] else [])
def postRows (last : Bool) : List Row := selectRows++copyRows++nextRows last

theorem walk_join (s : MachineState) (xs ys : List Row) :
    walkRows s (xs++ys)=walkRows (walkRows s xs) ys := by
  simp only [walkRows,List.foldl_append]

theorem legal_append (s : MachineState) (a b : List Row) (head : legal a s) (tail : legal b (walkRows s a)) :
    legal (a++b) s := by
  induction a generalizing s with
  | nil => exact tail
  | cons p a ih =>
    rcases p with ⟨i,op⟩
    exact ⟨head.1,head.2.1,ih _ head.2.2 tail⟩

theorem price_append (a b : List Row) : price (a++b)=price a+price b := by
  simp [price]

private theorem row_fetch (row : Row) (bounded : row.1<777) (dec : (openingImage.code[row.1]?).bind Opening.decodeBase=some row.2) :
    ∀ st : MachineState, st.pc=address row.1 → fetch openingImage st=some (.base row.2) :=
  fun st pc => packed_fetch_base st _ _ bounded pc dec

theorem pre_row_fetch (b ip tw : Bool) : presentRows (preRows b ip tw) := by
  have raw : ∀ b ip tw : Bool, ∀ i : Fin (preRows b ip tw).length, let row := (preRows b ip tw)[i];
      row.1<777 ∧ (openingImage.code[row.1]?).bind Opening.decodeBase=some row.2 := by decide +kernel
  intro p hp;obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp hp
  subst p
  exact row_fetch _ (raw b ip tw ⟨i,hi⟩).1 (raw b ip tw ⟨i,hi⟩).2

/-- The record writer's group-base rows (368-byte quartet blocks: `x7 = x24 + (x6 >>> 2) * x4`). -/
def writerRows : List Row := [(34,.ADDI .x21 .x21 16),(35,.SRLI .x7 .x6 2),(36,.MUL .x7 .x7 .x4),
  (37,.ADD .x7 .x7 .x24),(38,.ANDI .x10 .x6 3)]

theorem writer_row_fetch : presentRows writerRows := by
  intro p hp
  apply row_fetch
  · simp only [writerRows,List.mem_cons,List.not_mem_nil,or_false] at hp;rcases hp with h|h|h|h|h <;> subst p <;> decide
  · simp only [writerRows,List.mem_cons,List.not_mem_nil,or_false] at hp;rcases hp with h|h|h|h|h <;> subst p <;> decide +kernel

theorem post_row_fetch (last : Bool) : presentRows (postRows last) := by
  have raw : ∀ l : Bool, ∀ i : Fin (postRows l).length, let row := (postRows l)[i];
      row.1<777 ∧ (openingImage.code[row.1]?).bind Opening.decodeBase=some row.2 := by decide +kernel
  intro p hp;obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp hp
  subst p
  exact row_fetch _ (raw last ⟨i,hi⟩).1 (raw last ⟨i,hi⟩).2

theorem ecall_fetch (st : MachineState) (pc : st.pc=address 765) : fetch openingImage st=some (.base .ECALL) :=
  packed_fetch_base st 765 _ (by decide) pc (by decide +kernel)

end TwoPermutationPrototype.GroupedOpening
