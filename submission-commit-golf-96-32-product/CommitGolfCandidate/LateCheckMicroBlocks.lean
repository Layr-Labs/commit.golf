import CommitGolfCandidate.LateCheckMicroCalc

namespace CommitGolfCandidate.Late.Check.Micro
open CommitGolfCandidate.Late.Open (Calc Bin Expr original evaluated price requirements live bump)
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

inductive Part where
  | dispatch | normalLen | normalReady | batchLen | batchReady | loadIndex | leafReady | parity | oddDest | evenDest | advance
deriving DecidableEq

def Part.start : Part → Nat
  | .dispatch => 0
  | .normalLen => 7
  | .normalReady => 12
  | .batchLen => 197
  | .batchReady => 201
  | .loadIndex => 15
  | .leafReady => 384
  | .parity => 406
  | .oddDest => 416
  | .evenDest => 419
  | .advance => 430

def Part.stop : Part → Nat
  | .dispatch => 6
  | .normalLen => 11
  | .normalReady => 14
  | .batchLen => 200
  | .batchReady => 207
  | .loadIndex => 16
  | .leafReady => 387
  | .parity => 409
  | .oddDest => 417
  | .evenDest => 420
  | .advance => 432

def Part.ops : Part → List Calc
  | .dispatch => [.addi .x26 .x11 0, .addi .x24 .x13 0, .addi .x8 .x14 0, .addi .x25 .x15 0, .addi .x27 .x16 0, .addi .x6 .x0 128]
  | .normalLen => [.addi .x6 .x0 0, .slli .x6 .x6 11, .addi .x6 .x0 792, .mul .x7 .x16 .x6]
  | .normalReady => [.addi .x30 .x0 24, .addi .x21 .x0 256]
  | .batchLen => [.addi .x6 .x0 33, .slli .x6 .x6 11, .addi .x6 .x6 1536]
  | .batchReady => [.addi .x6 .x0 31, .slli .x6 .x6 11, .addi .x6 .x6 1792, .add .x19 .x25 .x6, .addi .x21 .x0 256, .addi .x30 .x0 16]
  | .loadIndex => [.ld .x20 .x24 0]
  | .leafReady => [.addi .x5 .x0 0, .addi .x13 .x0 0, .addi .x11 .x0 96]
  | .parity => [.andi .x28 .x20 1, .slli .x7 .x28 5, .addi .x7 .x7 160]
  | .oddDest => [.addi .x12 .x0 160]
  | .evenDest => [.addi .x12 .x0 232]
  | .advance => [.addi .x8 .x8 256, .addi .x25 .x25 24]

def Part.equation : Part → Reg → Expr
  | .dispatch,.x6 => (.lit 128)
  | .dispatch,.x8 => (.op .add (.reg .x14) (.lit 0))
  | .dispatch,.x24 => (.op .add (.reg .x13) (.lit 0))
  | .dispatch,.x25 => (.op .add (.reg .x15) (.lit 0))
  | .dispatch,.x26 => (.op .add (.reg .x11) (.lit 0))
  | .dispatch,.x27 => (.op .add (.reg .x16) (.lit 0))
  | .normalLen,.x6 => (.lit 792)
  | .normalLen,.x7 => (.op .mul (.reg .x16) (.lit 792))
  | .normalReady,.x21 => (.lit 256)
  | .normalReady,.x30 => (.lit 24)
  | .batchLen,.x6 => (.lit 69120)
  | .batchReady,.x6 => (.lit 65280)
  | .batchReady,.x19 => (.op .add (.reg .x25) (.lit 65280))
  | .batchReady,.x21 => (.lit 256)
  | .batchReady,.x30 => (.lit 16)
  | .loadIndex,.x20 => (.load (.op .add (.reg .x24) (.lit 0)))
  | .leafReady,.x5 => (.lit 0)
  | .leafReady,.x11 => (.lit 96)
  | .leafReady,.x13 => (.lit 0)
  | .parity,.x7 => (.op .add (.op .shl (.op .and (.reg .x20) (.lit 1)) (.lit 5)) (.lit 160))
  | .parity,.x28 => (.op .and (.reg .x20) (.lit 1))
  | .oddDest,.x12 => (.lit 160)
  | .evenDest,.x12 => (.lit 232)
  | .advance,.x8 => (.op .add (.reg .x8) (.lit 256))
  | .advance,.x25 => (.op .add (.reg .x25) (.lit 24))
  | _,r => original r

def Part.reads : Part → List Expr
  | .dispatch => []
  | .normalLen => []
  | .normalReady => []
  | .batchLen => []
  | .batchReady => []
  | .loadIndex => [(.op .add (.reg .x24) (.lit 0))]
  | .leafReady => []
  | .parity => []
  | .oddDest => []
  | .evenDest => []
  | .advance => []

def Part.cycles : Part → Nat
  | .dispatch => 6
  | .normalLen => 7
  | .normalReady => 2
  | .batchLen => 3
  | .batchReady => 6
  | .loadIndex => 1
  | .leafReady => 3
  | .parity => 3
  | .oddDest => 1
  | .evenDest => 1
  | .advance => 2
def Part.after (b : Part) (s : MachineState) := evaluated b.ops s

private def represents (n : Nat) (op : Instr) : Bool :=
  match decodeInstruction (checkWord n) with
  | some (.base actual) => decide (actual=op)
  | _ => false

private theorem represented {n : Nat} {op : Instr} (h : represents n op) :
    decodeInstruction (checkWord n) = some (.base op) := by
  unfold represents at h
  split at h
  · next actual eq => rw [eq,of_decide_eq_true h]
  · contradiction

set_option maxRecDepth 8000 in
private theorem checked (b : Part) :
    b.start+b.ops.length=b.stop ∧ b.stop≤814 ∧ b.ops.length=b.stop-b.start ∧
    price b.ops=b.cycles ∧ b.ops.all (fun c => c.dst != .x0) = true ∧
    requirements original b.ops=b.reads ∧
    ∀ j : Fin b.ops.length, represents (b.start+j.val) b.ops[j.val].instr := by
  cases b <;> decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
private theorem outputs (b : Part) (r : Reg) :
    (b.ops.foldl bump original) r = b.equation r := by cases b <;> cases r <;> rfl

structure BlockResult (b : Part) (s : MachineState) : Prop where
  runs : Runs s (b.after s) (b.stop-b.start) b.cycles
  regs : ∀ r, (b.after s).getReg r = (b.equation r).eval s
  mem : (b.after s).mem=s.mem
  pc : (b.after s).pc=pcAt b.stop

theorem block_result (b : Part) (s : MachineState) (pc : s.pc=pcAt b.start)
    (safe : ∀ a ∈ b.reads, accessValid (a.eval s) 8=true) : BlockResult b s := by
  obtain ⟨edge,bound,size,cost,ok,reads,enc⟩ := checked b
  have regs : live s s original := by intro r;cases r <;> rfl
  have r := evaluate_block b.ops b.start s s original regs rfl pc (by omega)
    (fun c h => bne_iff_ne.mp (List.all_eq_true.mp ok c h)) (reads.symm ▸ safe)
    (fun j hj => represented (enc ⟨j,hj⟩))
  dsimp only at r
  refine ⟨?_,fun k => (r.2.1 k).trans (congrArg (Expr.eval s) (outputs b k)),r.2.2.1,?_⟩
  · rw [←size,←cost]; exact r.1
  · exact r.2.2.2.trans (congrArg pcAt edge)

end CommitGolfCandidate.Late.Check.Micro
