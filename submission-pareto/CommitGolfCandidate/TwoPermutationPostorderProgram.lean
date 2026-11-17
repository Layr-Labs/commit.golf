import CommitGolfCandidate.TwoPermutationOpeningCapEntry
import CommitGolfCandidate.TwoPermutationOpeningCapStructure

namespace TwoPermutationPrototype.Opening.Postorder
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

def offset (n : Nat) : BitVec 12 := BitVec.ofNat 12 (8*n + 2049)
def addr (n : Nat) : Word := BitVec.ofNat 64 (markBase + 8*n)
def pcOf (i : Nat) : Word := BitVec.ofNat 64 (4096 + 4*i)

def reg : Nat → Reg
  | 0 => .x7 | 1 => .x28 | 2 => .x29 | 3 => .x31 | 4 => .x10
  | 5 => .x11 | 6 => .x12 | 7 => .x13 | _ => .x14

theorem offset_ok : ∀ n : Fin 512, 6143#64 + signExtend12 (offset n.val) = addr n.val := by decide
theorem addr_valid (n : Nat) (bound : n < 512) : accessValid (addr n) 8 = true := by
  apply aligned_access
  · unfold markBase; omega
  · unfold markBase MEMORY_BYTES; omega

theorem reg_ne_zero : ∀ i : Fin 9, reg i.val ≠ .x0 := by decide
theorem reg_ne_base : ∀ i : Fin 9, reg i.val ≠ .x6 := by decide
theorem reg_distinct : ∀ i j : Fin 9, i.val ≠ j.val → reg i.val ≠ reg j.val := by decide

def words (n : Nat) : Nat → Nat → List Instr
  | 0, d => [.LD (reg d) .x6 (offset n)]
  | h+1, d =>
    words (2*n) h d ++ (words (2*n+1) h (d+1) ++
      [.OR (reg d) (reg d) (reg (d+1)), .SD .x6 (reg d) (offset n)])

def cost : Nat → Nat
  | 0 => 1
  | h+1 => cost h + cost h + 2

@[simp] theorem words_length (n h d : Nat) : (words n h d).length = cost h := by
  induction h generalizing n d with
  | zero => rfl
  | succ h ih => simp [words,cost,ih,Nat.add_assoc]

def CodeAt (i : Nat) (code : List Instr) : Prop :=
  ∀ j : Fin code.length,
    (openingImage.code[i+j.val]?).bind decodeInstruction = some (.base code[j.val])

theorem split_code {i : Nat} {a b : List Instr} (h : CodeAt i (a++b)) :
    CodeAt i a ∧ CodeAt (i+a.length) b := by
  constructor
  · intro j
    have fetched := h ⟨j.val, by simp; omega⟩
    simpa only [List.getElem_append_left j.isLt] using fetched
  · intro j
    have fetched := h ⟨a.length+j.val, by simp⟩
    rw [List.getElem_append_right (by omega : a.length ≤ a.length+j.val)] at fetched
    simpa only [Nat.add_sub_cancel_left, Nat.add_assoc] using fetched

theorem add_pc (i j : Nat) : pcOf i + BitVec.ofNat 64 (4*j) = pcOf (i+j) := by
  unfold pcOf
  rw [← BitVec.ofNat_add]
  congr 1
  omega

attribute [local simp] getReg_setReg getReg_setMem

def finish (s : MachineState) (n d : Nat) : MachineState :=
  let w := s.getReg (reg d) ||| s.getReg (reg (d+1))
  ((s.setReg (reg d) w).setMem (addr n) w).setPC (s.pc + 8)

def eval (s : MachineState) (n : Nat) : Nat → Nat → MachineState
  | 0, d => (s.setReg (reg d) (s.getMem (addr n))).setPC (s.pc+4)
  | h+1, d =>
    let l := eval s (2*n) h d
    let r := eval l (2*n+1) h (d+1)
    finish r n d

theorem eval_register (s : MachineState) (n h d : Nat) (r : Reg)
    (outside : ∀ j, d ≤ j → j ≤ d+h → reg j ≠ r) :
    (eval s n h d).getReg r = s.getReg r := by
  induction h generalizing s n d with
  | zero => simp [eval, outside d (by omega) (by omega)]
  | succ h ih =>
    simp only [eval, finish, MachineState.getReg_setPC, getReg_setMem, getReg_setReg,
      outside d (by omega) (by omega), false_and, ite_false]
    rw [ih _ _ (d+1) (by intro j lo hi; apply outside <;> omega),
      ih _ _ d (by intro j lo hi; apply outside <;> omega)]

theorem eval_pc (s : MachineState) (n h d i : Nat) (pc : s.pc = pcOf i) :
    (eval s n h d).pc = pcOf (i+cost h) := by
  induction h generalizing s n d i with
  | zero => change s.pc + 4 = _; rw [pc]; exact add_pc i 1
  | succ h ih =>
    have left := ih s (2*n) d i pc
    have right := ih _ (2*n+1) (d+1) _ left
    change (eval (eval s (2*n) h d) (2*n+1) h (d+1)).pc + 8 = _
    rw [right]
    exact (add_pc _ 2).trans (congrArg pcOf (by simp [cost,Nat.add_assoc]))

end TwoPermutationPrototype.Opening.Postorder
