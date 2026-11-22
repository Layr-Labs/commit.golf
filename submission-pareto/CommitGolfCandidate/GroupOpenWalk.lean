import CommitGolfCandidate.GroupOpenImage
import CommitGolfCandidate.Execution
import CommitGolfCandidate.TwoPermutationOpeningCopy

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000

/-- `packed_fetch_all` for every row of the image, including the relocated first pass (3077..3147). -/
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

/-! First pass, one position `i` (quartet `g = i >> 2`, block `B = B_g`), rows 3077..3147 (inside the NOP gap after the record-writer selector).
Head (rows 3077..3096): `x3 := 16 i` and `x30 :=` the table entry of `i % 4096` (`GroupOpenTable`); `skip` to
row 3096 when `g` equals the previous position's quartet (`x4`); otherwise `x4 := g`, the rebuilt block is
`B+512`, the entry's signed offsets give the reply (`B+168` even, `B-1056` odd) and the address of the sibling
group's node (`B+136` even, `B-856` odd), the inverse of the reply lands in the rebuilt block (call at 3092),
rows 3093..3094 restore `x13, x12`, row 3095 stores the sibling node's address in the word after the rebuilt
block (`B+712`), where the record writer's level-0 head loads it. Then the chained salt generator (3097..3105
and the link block 3106..3138, `K3OpenChain`) and the salt rows (3139..3147). -/

def headRows : List Row := [(3077,.LD .x6 .x14 0),(3078,.SRLI .x28 .x6 2),(3079,.SLLI .x3 .x6 4),
  (3080,.AND .x30 .x3 .x1),(3081,.ADD .x30 .x30 .x2),(3082,.BEQ .x28 .x4 56)]
/-- Row 3096: `addi x10,x0,1024`, shared by the skip path (branch target) and the end of a new quartet's rows. -/
def loadRow : List Row := [(3096,.ADDI .x10 .x0 1024)]
/-- A repeated quartet: rows 3077..3082, then 3096. -/
def skipRows : List Row := headRows ++ loadRow
/-- A new quartet before its inverse call (row 3092). -/
def newRows : List Row := [(3083,.ADDI .x4 .x28 0),(3084,.SLLI .x7 .x28 10),(3085,.ADD .x7 .x7 .x24),
  (3086,.ADDI .x12 .x7 512),(3087,.LH .x10 .x30 4),(3088,.ADD .x10 .x10 .x7),(3089,.LH .x31 .x30 6),
  (3090,.ADD .x31 .x31 .x7),(3091,.ADDI .x13 .x0 2)]
def preRows : List Row := headRows ++ newRows
def restoreRows : List Row := [(3093,.ADDI .x13 .x0 1),(3094,.ADDI .x12 .x0 1536)]
/-- `sd x31, 712(x7)`: the sibling node's address into word 89 of the quartet block. -/
def ptrRows : List Row := [(3095,.SD .x7 .x31 712)]
/-- A new quartet after its inverse call: rows 3093..3096. -/
def headPost : List Row := restoreRows ++ ptrRows ++ loadRow

/-- Salt rows: the destination `x30 := 16 i + x22` (row 3139, right after the link block), then two dword
copies from the reply address `x28` the table supplied (rows 3140..3143), falling through to the latch. -/
def selectRows : List Row := [(3139,.ADD .x30 .x3 .x22)]
def copyRows : List Row :=
  [(3140,.LD .x31 .x28 0),(3141,.SD .x30 .x31 0),(3142,.LD .x31 .x28 8),(3143,.SD .x30 .x31 8)]
def nextRows (last : Bool) : List Row := [(3144,.ADDI .x14 .x14 8),(3145,.BNE .x14 .x17 7920)] ++
  (if last then [(3146,.ADDI .x25 .x9 0),(3147,.JAL .x0 2084624)] else [])

def postRows (last : Bool) : List Row := selectRows ++ copyRows ++ nextRows last

private theorem row_fetch (row : Row) (bounded : row.1<6144) (dec : (openingImage.code[row.1]?).bind Opening.decodeBase=some row.2) :
    ∀ st : MachineState, st.pc=address row.1 → fetch openingImage st=some (.base row.2) :=
  fun st pc => packed_fetch_far st _ _ (by omega) pc dec

theorem rows_present (rows : List Row)
    (raw : ∀ i : Fin rows.length, rows[i].1<6144 ∧ (openingImage.code[rows[i].1]?).bind Opening.decodeBase=some rows[i].2) :
    presentRows rows := by
  intro p hp;obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp hp
  subst p
  exact row_fetch _ (raw ⟨i,hi⟩).1 (raw ⟨i,hi⟩).2

theorem skip_row_fetch : presentRows skipRows := by apply rows_present; decide +kernel
theorem pre_row_fetch : presentRows preRows := by apply rows_present; decide +kernel
theorem head_post_fetch : presentRows headPost := by apply rows_present; decide +kernel
theorem post_row_fetch (last : Bool) : presentRows (postRows last) := by
  apply rows_present; revert last; decide +kernel

theorem inverse_fetch (s : MachineState) (pc : s.pc=address 3092) : fetch openingImage s=some (.base .ECALL) :=
  packed_fetch_far _ 3092 _ (by decide) pc (by decide +kernel)

end TwoPermutationPrototype.GroupedOpening
