import CommitGolfCandidate.TwoPermutationPackedFetchBase

namespace CommitGolfCandidate.Layout2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

inductive Block where
  | entry | guard | empty | init | choose | full | next | tail | one | two | three | pair | single | callTail | clearHead | clearCell | restore | copyHead | copyByte | writeHead | byteHead | bitStep | emitByte | ret

def Block.start : Block → Nat
  | .entry => 786
  | .guard => 705
  | .empty => 708
  | .init => 709
  | .choose => 713
  | .full => 714
  | .next => 718
  | .tail => 721
  | .one => 722
  | .two => 724
  | .three => 726
  | .pair => 730
  | .single => 734
  | .callTail => 737
  | .clearHead => 739
  | .clearCell => 742
  | .restore => 745
  | .copyHead => 759
  | .copyByte => 762
  | .writeHead => 767
  | .byteHead => 768
  | .bitStep => 770
  | .emitByte => 782
  | .ret => 785

def Block.ops : Block → List Instr
  | .entry => [.JAL .x0 2096828]
  | .guard => [.ADDI .x6 .x0 534, .MUL .x6 .x16 .x6, .BLTU .x17 .x6 6820]
  | .empty => [.BEQ .x16 .x0 148]
  | .init => [.ADDI .x8 .x15 0, .ADDI .x9 .x16 0, .ADDI .x20 .x0 4, .ADDI .x21 .x0 8]
  | .choose => [.BLTU .x9 .x20 32]
  | .full => [.ADDI .x18 .x0 2047, .ADDI .x18 .x18 89, .ADDI .x19 .x2 0, .JAL .x31 168]
  | .next => [.ADD .x8 .x8 .x18, .ADDI .x9 .x9 4092, .JAL .x0 2097124]
  | .tail => [.BEQ .x9 .x0 72]
  | .one => [.ADDI .x5 .x0 1, .BEQ .x9 .x5 44]
  | .two => [.ADDI .x5 .x0 2, .BEQ .x9 .x5 20]
  | .three => [.ADDI .x18 .x0 1602, .LUI .x5 15, .ADDI .x5 .x5 2464, .JAL .x0 32]
  | .pair => [.ADDI .x18 .x0 1068, .LUI .x5 10, .ADDI .x5 .x5 1760, .JAL .x0 16]
  | .single => [.ADDI .x18 .x0 534, .LUI .x5 8, .ADDI .x5 .x5 1408]
  | .callTail => [.ADD .x19 .x2 .x5, .JAL .x31 84]
  | .clearHead => [.ADDI .x5 .x10 0, .ADDI .x6 .x10 2047, .ADDI .x6 .x6 89]
  | .clearCell => [.SD .x5 .x0 0, .ADDI .x5 .x5 8, .BNE .x5 .x6 8184]
  | .restore => [.ADDI .x5 .x0 0, .ADDI .x7 .x0 0, .ADDI .x28 .x0 0, .ADDI .x29 .x0 0, .ADDI .x30 .x0 0, .ADDI .x31 .x0 0, .ADDI .x8 .x0 0, .ADDI .x9 .x0 0, .ADDI .x18 .x0 0, .ADDI .x19 .x0 0, .ADDI .x20 .x0 0, .ADDI .x21 .x0 0, .ADDI .x6 .x0 534, .JAL .x0 2094124]
  | .copyHead => [.ADDI .x5 .x8 0, .ADDI .x6 .x10 0, .ADD .x7 .x8 .x18]
  | .copyByte => [.LBU .x28 .x5 0, .SB .x6 .x28 0, .ADDI .x5 .x5 1, .ADDI .x6 .x6 1, .BNE .x5 .x7 8176]
  | .writeHead => [.ADDI .x5 .x8 0]
  | .byteHead => [.ADDI .x6 .x0 0, .ADDI .x28 .x0 0]
  | .bitStep => [.LHU .x29 .x19 0, .SRLI .x30 .x29 3, .ADD .x30 .x30 .x10, .LBU .x30 .x30 0, .ANDI .x29 .x29 7, .SRL .x30 .x30 .x29, .ANDI .x30 .x30 1, .SLL .x30 .x30 .x28, .OR .x6 .x6 .x30, .ADDI .x19 .x19 2, .ADDI .x28 .x28 1, .BNE .x28 .x21 8148]
  | .emitByte => [.SB .x5 .x6 0, .ADDI .x5 .x5 1, .BNE .x5 .x7 8128]
  | .ret => [.JALR .x0 .x31 0]

def pc (index : Nat) : Word := BitVec.ofNat 64 (4096+4*index)
def eval (s : MachineState) (ops : List Instr) := ops.foldl execInstrBr s
def price (ops : List Instr) := (ops.map fun op => instructionCycles (.base op)).sum
def Ready : MachineState → List Instr → Prop
 | _, [] => True
 | s, op::ops => memoryArgumentsValid s op=true ∧ Ready (execInstrBr s op) ops

def rowsAt (I : Image) (w : Nat) (xs : List Instr) : Prop :=
  ∀ j : Fin xs.length, (I.code[w+j.val]?).bind decodeInstruction=some (.base xs[j])
def Program (I : Image) : Prop := ∀ b : Block, rowsAt I b.start b.ops

def ordinary : Instr → Bool
 | .ADDI .. | .MUL .. | .BLTU .. | .BEQ .. | .BNE .. | .JAL .. | .JALR .. | .LUI .. | .ADD ..
 | .SD .. | .LBU .. | .SB .. | .LHU .. | .SRLI .. | .ANDI .. | .SRL .. | .SLL .. | .OR .. => true
 | _ => false
def straight : Instr → Bool
 | .ADDI .. | .MUL .. | .LUI .. | .ADD .. | .SD .. | .LBU .. | .SB .. | .LHU ..
 | .SRLI .. | .ANDI .. | .SRL .. | .SLL .. | .OR .. => true
 | _ => false
def syntaxOK : List Instr → Bool
 | [] => true
 | x::xs => ordinary x && (xs.isEmpty || straight x) && syntaxOK xs

def Runs (I : Image) (s t : MachineState) (steps cycles : Nat) : Prop :=
  ∀ fuel, execute I (steps+fuel) s false = do
    let z ← execute I fuel t false
    pure (z.charge cycles 0)

attribute [local irreducible] execute
theorem runs_zero (I : Image) (s : MachineState) : Runs I s s 0 0 := by
  intro fuel; simp [Execution.charge]
theorem Runs.thenDo {I s t u a b c d} (first : Runs I s t a b) (last : Runs I t u c d) :
    Runs I s u (a+c) (b+d) := by
  intro fuel; rw [Nat.add_assoc,first,last];simp [bind_assoc,Execution.charge,Nat.add_assoc]

theorem pc_next (w : Nat) : pc w+4=pc (w+1) := by
  unfold pc;change BitVec.ofNat 64 _ + BitVec.ofNat 64 4 = _
  rw [←BitVec.ofNat_add];congr 1 <;> omega

theorem run_rows (I : Image) (ops : List Instr) (w : Nat) (s : MachineState)
    (atRows : rowsAt I w ops) (syntaxH : syntaxOK ops=true) (bound : w+ops.length<2^40)
    (here : s.pc=pc w) (ready : Ready s ops) :
    Runs I s (eval s ops) ops.length (price ops) := by
  induction ops generalizing s w with
  | nil => exact runs_zero I s
  | cons x xs ih =>
    rw [syntaxOK,Bool.and_eq_true,Bool.and_eq_true] at syntaxH
    have f:=wide_image_fetch I s w x (by omega) here (by simpa using atRows ⟨0,by simp⟩)
    have valid:=ready.1
    have ord : ordinaryStep s (.base x)=some (execInstrBr s x) := by
      have kind:=syntaxH.1.1
      cases x <;> simp [ordinary] at kind <;> simp only [ordinaryStep,valid,ite_true]
    have head : Runs I s (execInstrBr s x) 1 (instructionCycles (.base x)) := by
      intro fuel;rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ f ord]
    cases xs with
    | nil => simpa [eval,price] using head
    | cons y ys =>
      have linear : straight x=true := by simpa using syntaxH.1.2
      have p : (execInstrBr s x).pc=s.pc+4 := by cases x <;> first | rfl | cases linear
      have later : rowsAt I (w+1) (y::ys) := by
        intro j
        simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using atRows ⟨j.val+1,by simpa using j.isLt⟩
      have tail:=ih (w+1) (execInstrBr s x) later syntaxH.2
        (by simp only [List.length_cons] at bound ⊢;omega) (by rw [p,here,pc_next]) ready.2
      simpa only [eval,List.foldl_cons, List.length_cons, price,List.map_cons,List.sum_cons,Nat.add_comm 1] using head.thenDo tail

def after (b : Block) (s : MachineState) := eval s b.ops

theorem runBlock {I} (program : Program I) (b : Block) (s : MachineState) (here : s.pc=pc b.start)
    (ready : Ready s b.ops) : Runs I s (after b s) b.ops.length (price b.ops) :=
  run_rows I _ _ s (program b) (by cases b <;> decide) (by cases b <;> decide) here ready

end CommitGolfCandidate.Layout2
