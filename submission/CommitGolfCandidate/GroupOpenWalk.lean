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

/-! K3-lite prefix, one position `i` (quartet `g = i >> 2`, even block `B = B_{2 (g >> 1)}`), rows 740..812.
Head paths (rows 740..776): `skip` when `g` equals the previous position's quartet (`x4`); otherwise `x4 := g`, the
parity selects the reply (`B+168` even, `B-32` odd), the rebuilt block (`B+512` even, `B+1536` odd, both
`Q+512+1024 g`) and the level-22 sibling node (`B+136` even, `B+168` odd); the inverse of the reply lands in the
rebuilt block (call at 761), rows 762..764 restore `x13, x12, x10` and rows 765..776 copy the sibling to
`heap[2^22 + (g ^ 1)]`. Then the chained salt generator (777..795, `K3OpenChain`) and the K1 salt rows (796..812). -/

def headRows : List Row := [(740,.LD .x6 .x14 0),(741,.SRLI .x28 .x6 2),(742,.BEQ .x28 .x4 140)]
def newRows : List Row := [(743,.ADDI .x4 .x28 0),(744,.SRLI .x7 .x6 3),(745,.SLLI .x7 .x7 11),(746,.ADD .x7 .x7 .x24),
  (747,.ANDI .x30 .x6 4),(748,.BNE .x30 .x0 36)]
/-- Even quartet: reply_E at `B+168`, rebuilt block at `B+512`, sibling G_O at `B+136`; jump to 760. -/
def evenSel : List Row := [(749,.ADDI .x10 .x7 168),(750,.ADDI .x12 .x7 512),(751,.ADDI .x30 .x7 136),(752,.JAL .x0 32)]
/-- Odd quartet: reply_O at `B-32` (immediate `4064 = -32` in 12 bits), rebuilt block at `B+1536`, sibling G_E at `B+168`. -/
def oddSel : List Row := [(757,.ADDI .x10 .x7 4064),(758,.ADDI .x12 .x7 1536),(759,.ADDI .x30 .x7 168)]
def selRows (odd : Bool) : List Row := if odd then oddSel else evenSel
def callRow : List Row := [(760,.ADDI .x13 .x0 2)]
/-- A new quartet before its inverse call (row 761). -/
def preRows (odd : Bool) : List Row := headRows ++ newRows ++ selRows odd ++ callRow
def restoreRows : List Row := [(762,.ADDI .x13 .x0 1),(763,.ADDI .x12 .x0 1536),(764,.ADDI .x10 .x0 1024)]
def sibPairs : List (Nat × Nat) := [(0,0),(1,1),(2,2),(3,3)]
def sibRows : List Row :=
  [(765,.XORI .x28 .x28 1),(766,.ADD .x28 .x28 .x19),(767,.SLLI .x28 .x28 5),(768,.ADD .x28 .x28 .x9)] ++
  pairRows 769 .x30 .x28 sibPairs
/-- A new quartet after its inverse call: rows 762..776. -/
def headPost : List Row := restoreRows ++ sibRows

/-- Reply-offset rows by rank class `k` (0: rank 0, 1: rank 1, 2: rank ≥ 2), ending with the salt destination. -/
def selectRows (k : Fin 3) : List Row :=
  [(796,.ADDI .x7 .x28 (-1)),(797,.SLLI .x7 .x7 4),(798,.BLTU .x23 .x28 16)] ++
  (if k.val ≤ 1 then [(799,.ADDI .x7 .x0 0),(800,.BNE .x28 .x23 8)] else []) ++
  (if k.val = 1 then [(801,.ADDI .x7 .x0 184)] else []) ++
  [(802,.ADD .x7 .x7 .x12),(803,.SLLI .x30 .x6 4),(804,.ADD .x30 .x30 .x22)]
def copyRows : List Row := [(805,.LD .x31 .x7 0),(806,.SD .x30 .x31 0),(807,.LD .x31 .x7 8),(808,.SD .x30 .x31 8)]
def nextRows (last : Bool) : List Row := [(809,.ADDI .x14 .x14 8),(810,.ADDI .x17 .x17 (-1)),(811,.BNE .x17 .x0 7908)] ++
  (if last then [(812,.JAL .x0 2093964)] else [])

def postRows (k : Fin 3) (last : Bool) : List Row := selectRows k ++ copyRows ++ nextRows last

private theorem row_fetch (row : Row) (bounded : row.1<813) (dec : (openingImage.code[row.1]?).bind Opening.decodeBase=some row.2) :
    ∀ st : MachineState, st.pc=address row.1 → fetch openingImage st=some (.base row.2) :=
  fun st pc => packed_fetch_base st _ _ (by omega) pc dec

theorem rows_present (rows : List Row)
    (raw : ∀ i : Fin rows.length, rows[i].1<813 ∧ (openingImage.code[rows[i].1]?).bind Opening.decodeBase=some rows[i].2) :
    presentRows rows := by
  intro p hp;obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp hp
  subst p
  exact row_fetch _ (raw ⟨i,hi⟩).1 (raw ⟨i,hi⟩).2

theorem skip_row_fetch : presentRows headRows := by apply rows_present; decide +kernel
theorem pre_row_fetch (odd : Bool) : presentRows (preRows odd) := by apply rows_present; revert odd; decide +kernel
theorem head_post_fetch : presentRows headPost := by apply rows_present; decide +kernel
theorem post_row_fetch (k : Fin 3) (last : Bool) : presentRows (postRows k last) := by
  apply rows_present; revert k last; decide +kernel

theorem inverse_fetch (s : MachineState) (pc : s.pc=address 761) : fetch openingImage s=some (.base .ECALL) :=
  packed_fetch_base _ 761 _ (by decide) pc (by decide +kernel)

end TwoPermutationPrototype.GroupedOpening
