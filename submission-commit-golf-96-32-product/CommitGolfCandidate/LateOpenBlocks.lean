import CommitGolfCandidate.LateOpenExpressions

namespace CommitGolfCandidate.Late.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

inductive Part where
  | init | depth | batchDepth | saltSource | pathStart | siblingSource | pathNext | recordNext | mode | capStart | capMid | capNext | reverseStart | overrideSource | reverseNext | batchExit | normalExit
deriving DecidableEq

def Part.start : Part → Nat
  | .init => 0
  | .depth => 15
  | .batchDepth => 18
  | .saltSource => 19
  | .pathStart => 34
  | .siblingSource => 38
  | .pathNext => 51
  | .recordNext => 57
  | .mode => 60
  | .capStart => 62
  | .capMid => 76
  | .capNext => 86
  | .reverseStart => 90
  | .overrideSource => 108
  | .reverseNext => 127
  | .batchExit => 129
  | .normalExit => 135

def Part.stop : Part → Nat
  | .init => 14
  | .depth => 17
  | .batchDepth => 19
  | .saltSource => 28
  | .pathStart => 38
  | .siblingSource => 43
  | .pathNext => 56
  | .recordNext => 59
  | .mode => 61
  | .capStart => 68
  | .capMid => 78
  | .capNext => 89
  | .reverseStart => 108
  | .overrideSource => 119
  | .reverseNext => 128
  | .batchExit => 134
  | .normalExit => 139

def Part.ops : Part → List Calc
  | .init => [.addi .x9 .x12 0, .addi .x24 .x13 0, .addi .x25 .x15 0, .addi .x27 .x16 0, .addi .x18 .x0 1408, .slli .x18 .x18 11, .addi .x18 .x18 2, .slli .x18 .x18 11, .addi .x18 .x18 32, .addi .x29 .x0 192, .slli .x29 .x29 11, .addi .x29 .x29 0, .slli .x29 .x29 11, .addi .x29 .x29 0]
  | .depth => [.addi .x30 .x0 24, .addi .x6 .x0 128]
  | .batchDepth => [.addi .x30 .x0 16]
  | .saltSource => [.ld .x20 .x24 0, .slli .x7 .x20 1, .add .x7 .x7 .x20, .slli .x7 .x7 5, .add .x23 .x18 .x7, .andi .x6 .x20 1, .addi .x6 .x6 4095, .andi .x6 .x6 72, .add .x23 .x23 .x6]
  | .pathStart => [.addi .x25 .x25 24, .addi .x22 .x9 0, .addi .x17 .x29 0, .addi .x28 .x30 0]
  | .siblingSource => [.xori .x7 .x20 1, .srli .x6 .x20 1, .add .x7 .x7 .x6, .slli .x7 .x7 5, .add .x23 .x22 .x7]
  | .pathNext => [.addi .x25 .x25 32, .srli .x20 .x20 1, .addi .x28 .x28 4095, .add .x22 .x22 .x17, .srli .x17 .x17 1]
  | .recordNext => [.addi .x24 .x24 8, .addi .x27 .x27 4095]
  | .mode => [.addi .x6 .x0 128]
  | .capStart => [.addi .x23 .x0 1407, .slli .x23 .x23 11, .addi .x23 .x23 2044, .slli .x23 .x23 11, .addi .x23 .x23 32, .addi .x28 .x0 64]
  | .capMid => [.addi .x23 .x23 32, .addi .x25 .x25 32]
  | .capNext => [.addi .x23 .x23 64, .addi .x25 .x25 32, .addi .x28 .x28 4095]
  | .reverseStart => [.addi .x24 .x0 1824, .slli .x24 .x24 11, .addi .x24 .x24 2, .slli .x24 .x24 11, .addi .x24 .x24 1056, .addi .x18 .x0 1, .slli .x18 .x18 11, .addi .x18 .x18 832, .slli .x18 .x18 11, .addi .x18 .x18 35, .slli .x18 .x18 11, .addi .x18 .x18 1056, .addi .x19 .x0 1407, .slli .x19 .x19 11, .addi .x19 .x19 2038, .slli .x19 .x19 11, .addi .x19 .x19 32, .addi .x28 .x0 128]
  | .overrideSource => [.addi .x24 .x24 4088, .ld .x20 .x24 0, .srli .x20 .x20 16, .andi .x20 .x20 255, .xori .x7 .x20 1, .srli .x6 .x20 1, .add .x7 .x7 .x6, .slli .x7 .x7 5, .add .x23 .x19 .x7, .slli .x6 .x6 5, .add .x25 .x18 .x6]
  | .reverseNext => [.addi .x28 .x28 4095]
  | .batchExit => [.addi .x11 .x0 35, .slli .x11 .x11 11, .addi .x11 .x11 1024, .addi .x5 .x0 1, .addi .x10 .x0 0]
  | .normalExit => [.addi .x6 .x0 792, .mul .x11 .x16 .x6, .addi .x5 .x0 1, .addi .x10 .x0 0]

def Part.equation : Part → Reg → Expr
  | .init,.x9 => (.op .add (.reg .x12) (.lit 0))
  | .init,.x18 => (.lit 5905584160)
  | .init,.x24 => (.op .add (.reg .x13) (.lit 0))
  | .init,.x25 => (.op .add (.reg .x15) (.lit 0))
  | .init,.x27 => (.op .add (.reg .x16) (.lit 0))
  | .init,.x29 => (.lit 805306368)
  | .depth,.x6 => (.lit 128)
  | .depth,.x30 => (.lit 24)
  | .batchDepth,.x30 => (.lit 16)
  | .saltSource,.x6 => (.op .and (.op .add (.op .and (.load (.op .add (.reg .x24) (.lit 0))) (.lit 1)) (.lit 18446744073709551615)) (.lit 72))
  | .saltSource,.x7 => (.op .shl (.op .add (.op .shl (.load (.op .add (.reg .x24) (.lit 0))) (.lit 1)) (.load (.op .add (.reg .x24) (.lit 0)))) (.lit 5))
  | .saltSource,.x20 => (.load (.op .add (.reg .x24) (.lit 0)))
  | .saltSource,.x23 => (.op .add (.op .add (.reg .x18) (.op .shl (.op .add (.op .shl (.load (.op .add (.reg .x24) (.lit 0))) (.lit 1)) (.load (.op .add (.reg .x24) (.lit 0)))) (.lit 5))) (.op .and (.op .add (.op .and (.load (.op .add (.reg .x24) (.lit 0))) (.lit 1)) (.lit 18446744073709551615)) (.lit 72)))
  | .pathStart,.x17 => (.op .add (.reg .x29) (.lit 0))
  | .pathStart,.x22 => (.op .add (.reg .x9) (.lit 0))
  | .pathStart,.x25 => (.op .add (.reg .x25) (.lit 24))
  | .pathStart,.x28 => (.op .add (.reg .x30) (.lit 0))
  | .siblingSource,.x6 => (.op .shr (.reg .x20) (.lit 1))
  | .siblingSource,.x7 => (.op .shl (.op .add (.op .xor (.reg .x20) (.lit 1)) (.op .shr (.reg .x20) (.lit 1))) (.lit 5))
  | .siblingSource,.x23 => (.op .add (.reg .x22) (.op .shl (.op .add (.op .xor (.reg .x20) (.lit 1)) (.op .shr (.reg .x20) (.lit 1))) (.lit 5)))
  | .pathNext,.x17 => (.op .shr (.reg .x17) (.lit 1))
  | .pathNext,.x20 => (.op .shr (.reg .x20) (.lit 1))
  | .pathNext,.x22 => (.op .add (.reg .x22) (.reg .x17))
  | .pathNext,.x25 => (.op .add (.reg .x25) (.lit 32))
  | .pathNext,.x28 => (.op .add (.reg .x28) (.lit 18446744073709551615))
  | .recordNext,.x24 => (.op .add (.reg .x24) (.lit 8))
  | .recordNext,.x27 => (.op .add (.reg .x27) (.lit 18446744073709551615))
  | .mode,.x6 => (.lit 128)
  | .capStart,.x23 => (.lit 5905571872)
  | .capStart,.x28 => (.lit 64)
  | .capMid,.x23 => (.op .add (.reg .x23) (.lit 32))
  | .capMid,.x25 => (.op .add (.reg .x25) (.lit 32))
  | .capNext,.x23 => (.op .add (.reg .x23) (.lit 64))
  | .capNext,.x25 => (.op .add (.reg .x25) (.lit 32))
  | .capNext,.x28 => (.op .add (.reg .x28) (.lit 18446744073709551615))
  | .reverseStart,.x18 => (.lit 12079668256)
  | .reverseStart,.x19 => (.lit 5905559584)
  | .reverseStart,.x24 => (.lit 7650415648)
  | .reverseStart,.x28 => (.lit 128)
  | .overrideSource,.x6 => (.op .shl (.op .shr (.op .and (.op .shr (.load (.op .add (.op .add (.reg .x24) (.lit 18446744073709551608)) (.lit 0))) (.lit 16)) (.lit 255)) (.lit 1)) (.lit 5))
  | .overrideSource,.x7 => (.op .shl (.op .add (.op .xor (.op .and (.op .shr (.load (.op .add (.op .add (.reg .x24) (.lit 18446744073709551608)) (.lit 0))) (.lit 16)) (.lit 255)) (.lit 1)) (.op .shr (.op .and (.op .shr (.load (.op .add (.op .add (.reg .x24) (.lit 18446744073709551608)) (.lit 0))) (.lit 16)) (.lit 255)) (.lit 1))) (.lit 5))
  | .overrideSource,.x20 => (.op .and (.op .shr (.load (.op .add (.op .add (.reg .x24) (.lit 18446744073709551608)) (.lit 0))) (.lit 16)) (.lit 255))
  | .overrideSource,.x23 => (.op .add (.reg .x19) (.op .shl (.op .add (.op .xor (.op .and (.op .shr (.load (.op .add (.op .add (.reg .x24) (.lit 18446744073709551608)) (.lit 0))) (.lit 16)) (.lit 255)) (.lit 1)) (.op .shr (.op .and (.op .shr (.load (.op .add (.op .add (.reg .x24) (.lit 18446744073709551608)) (.lit 0))) (.lit 16)) (.lit 255)) (.lit 1))) (.lit 5)))
  | .overrideSource,.x24 => (.op .add (.reg .x24) (.lit 18446744073709551608))
  | .overrideSource,.x25 => (.op .add (.reg .x18) (.op .shl (.op .shr (.op .and (.op .shr (.load (.op .add (.op .add (.reg .x24) (.lit 18446744073709551608)) (.lit 0))) (.lit 16)) (.lit 255)) (.lit 1)) (.lit 5)))
  | .reverseNext,.x28 => (.op .add (.reg .x28) (.lit 18446744073709551615))
  | .batchExit,.x5 => (.lit 1)
  | .batchExit,.x10 => (.lit 0)
  | .batchExit,.x11 => (.lit 72704)
  | .normalExit,.x5 => (.lit 1)
  | .normalExit,.x6 => (.lit 792)
  | .normalExit,.x10 => (.lit 0)
  | .normalExit,.x11 => (.op .mul (.reg .x16) (.lit 792))
  | _,r => original r

def Part.reads : Part → List Expr
  | .init => []
  | .depth => []
  | .batchDepth => []
  | .saltSource => [(.op .add (.reg .x24) (.lit 0))]
  | .pathStart => []
  | .siblingSource => []
  | .pathNext => []
  | .recordNext => []
  | .mode => []
  | .capStart => []
  | .capMid => []
  | .capNext => []
  | .reverseStart => []
  | .overrideSource => [(.op .add (.op .add (.reg .x24) (.lit 18446744073709551608)) (.lit 0))]
  | .reverseNext => []
  | .batchExit => []
  | .normalExit => []

def Part.cycles : Part → Nat
  | .init => 14
  | .depth => 2
  | .batchDepth => 1
  | .saltSource => 9
  | .pathStart => 4
  | .siblingSource => 5
  | .pathNext => 5
  | .recordNext => 2
  | .mode => 1
  | .capStart => 6
  | .capMid => 2
  | .capNext => 3
  | .reverseStart => 18
  | .overrideSource => 11
  | .reverseNext => 1
  | .batchExit => 5
  | .normalExit => 7
def Part.after (b : Part) (s : MachineState) := evaluated b.ops s

private def represents (n : Nat) (op : Instr) : Bool :=
  match decodeInstruction (openWord n) with
  | some (.base actual) => decide (actual=op)
  | _ => false

private theorem represented {n : Nat} {op : Instr} (h : represents n op) :
    decodeInstruction (openWord n) = some (.base op) := by
  unfold represents at h
  split at h
  · next actual eq => rw [eq,of_decide_eq_true h]
  · contradiction

set_option maxRecDepth 8000 in
private theorem checked (b : Part) :
    b.start+b.ops.length=b.stop ∧ b.stop≤140 ∧ b.ops.length=b.stop-b.start ∧
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

end CommitGolfCandidate.Late.Open
