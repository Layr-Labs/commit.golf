import CommitGolfCandidate.GroupOpenImage
import CommitGolfCandidate.Execution
import CommitGolfCandidate.TwoPermutationOpeningCopy

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000

/-- `packed_fetch_all` for every row of the image below word 6144 (the V2a pass phases sit at 3078..3387). -/
theorem packed_fetch_far (state : MachineState) (index : Nat) (instruction : Instr)
    (bounded : index < 6144) (pc : state.pc = BitVec.ofNat 64 (4096+4*index))
    (decoded : (openingImage.code[index]?).bind Opening.decodeBase = some instruction) :
    fetch openingImage state = some (.base instruction) := by
  have current : state.pc.toNat = 4096+4*index := by
    rw [pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  rw [fetch, current, ite_eq_left (by omega), show (4096+4*index-4096)/4=index by omega]
  cases code : openingImage.code[index]? with
  | none => simp [code] at decoded
  | some word =>
    simp [code, Opening.decodeBase] at decoded
    cases dec : decodeInstruction word with
    | none => simp [dec] at decoded
    | some result =>
      cases result with
      | base inst =>
        simp [dec] at decoded
        simpa [decoded] using dec
      | word op rd rs₁ rs₂ => simp [dec] at decoded
      | sraiw rd rs sh => simp [dec] at decoded

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

theorem pc_of_set (s : MachineState) (p : Word) : (s.setPC p).pc=p := rfl
theorem mem_of_set (s : MachineState) (p : Word) : (s.setPC p).mem=s.mem := rfl
theorem mem_of_reg (s : MachineState) (r : Reg) (v : Word) : (s.setReg r v).mem=s.mem := by cases r <;> rfl
theorem mem_of_store (s : MachineState) (a v : Word) : (s.setMem a v).mem=fun w => if w==a then v else s.mem w := rfl
theorem open_zero (s : MachineState) : s.getReg .x0=0 := rfl

theorem address_succ (n : Nat) : address n+4=address (n+1) := by
  show BitVec.ofNat 64 (4096+4*n)+BitVec.ofNat 64 4=_
  rw [← BitVec.ofNat_add]; unfold address; congr 1

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
  simp [price,List.map_append,List.sum_append]

/-- Instructions without a memory access. -/
def noMemOp : Instr → Bool
  | .LD .. | .SD .. | .LW .. | .LWU .. | .SW .. | .LH .. | .LHU .. | .SH .. | .LB .. | .LBU .. | .SB .. => false
  | _ => true

theorem no_mem_valid (st : MachineState) (op : Instr) (h : noMemOp op=true) : memoryArgumentsValid st op=true := by
  cases op <;> simp_all [noMemOp,memoryArgumentsValid,memAccess]

/-- The pc chain of a row list (the legality of rows without memory accesses). -/
def pcChain : List Row → MachineState → Prop
  | [],_ => True
  | (i,op)::tail,s => s.pc=address i ∧ pcChain tail (execInstrBr s op)

theorem legal_of_chain (rows : List Row) (s : MachineState)
    (nm : rows.all (fun p => plain p.2 && noMemOp p.2)=true) (c : pcChain rows s) : legal rows s := by
  induction rows generalizing s with
  | nil => trivial
  | cons p rest ih =>
    rcases p with ⟨i,op⟩
    simp only [List.all_cons,Bool.and_eq_true] at nm
    exact ⟨c.1,(ord_iff s op nm.1.1).mpr (no_mem_valid s op nm.1.2),ih _ nm.2 c.2⟩

theorem bne_reg' (u : MachineState) (a b : Reg) (imm : BitVec 13) (r : Reg) :
    (execInstrBr u (.BNE a b imm)).getReg r=u.getReg r := by
  simp only [execInstrBr];split <;> exact MachineState.getReg_setPC ..

theorem bne_mem' (u : MachineState) (a b : Reg) (imm : BitVec 13) : (execInstrBr u (.BNE a b imm)).mem=u.mem := by
  simp only [execInstrBr];split <;> rfl

/-- Word-pair copies `ld x31, 8a(src); sd x31, 8b(dst)` for `(a, b)` in `pairs`, rows from `start`. -/
def pairRows (start : Nat) (src dst : Reg) : List (Nat × Nat) → List Row
  | [] => []
  | (a,b)::rest => (start,.LD .x31 src (BitVec.ofNat 12 (8*a))) :: (start+1,.SD dst .x31 (BitVec.ofNat 12 (8*b))) ::
      pairRows (start+2) src dst rest

private theorem row_fetch (row : Row) (bounded : row.1<6144) (dec : (openingImage.code[row.1]?).bind Opening.decodeBase=some row.2) :
    ∀ st : MachineState, st.pc=address row.1 → fetch openingImage st=some (.base row.2) :=
  fun st pc => packed_fetch_far st _ _ (by omega) pc dec

theorem rows_present (rows : List Row)
    (raw : ∀ i : Fin rows.length, rows[i].1<6144 ∧ (openingImage.code[rows[i].1]?).bind Opening.decodeBase=some rows[i].2) :
    presentRows rows := by
  intro p hp;obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp hp
  subst p
  exact row_fetch _ (raw ⟨i,hi⟩).1 (raw ⟨i,hi⟩).2

end TwoPermutationPrototype.GroupedOpening
