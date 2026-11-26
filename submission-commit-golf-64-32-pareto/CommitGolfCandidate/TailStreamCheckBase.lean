import CommitGolfCandidate.TwoPermutationPackedUnpackSteps
import CommitGolfCandidate.TwoPermutationPackedOpeningPack
import CommitGolfCandidate.HeadStreamSeven
import CommitGolfCandidate.AlignedMemoryOrigin

namespace TwoPermutationPrototype.Packed.Checker.TailRestore
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open PackedOpening.Pack (ordinaryInstr w_add w_sub w_mul w_divu w_shl w_shr toNat_w w_inj accessValid_of w_or_mul)
set_option maxRecDepth 8192

def pcOf (i : Nat) : Word := BitVec.ofNat 64 (4096+4*(626+i))
def instrAt (i : Nat) : Instr := code.getD i .NOP
def cost (i : Nat) : Nat := instructionCycles (.base (instrAt i))
def run (s : MachineState) (ns : List Nat) : MachineState := ns.foldl (fun t n => execInstrBr t (instrAt n)) s
def cycles (ns : List Nat) : Nat := (ns.map cost).sum

set_option maxHeartbeats 1000000 in
theorem table : ∀ i : Fin 75, (packedImage.code[626+i.val]?).bind decodeInstruction=
    some (.base (instrAt i.val)) := by
  intro ⟨i,hi⟩
  interval_cases i <;> rfl

theorem runs_step (s : MachineState) (n : Nat) (hn : n<75) (pc : s.pc=pcOf n)
    (ordinary : ordinaryInstr (instrAt n)=true) (valid : memoryArgumentsValid s (instrAt n)=true) :
    Hop s (execInstrBr s (instrAt n)) 1 (cost n) := by
  exact hop_one s (626+n) _ (by omega) pc (table ⟨n,hn⟩)
    (PackedOpening.Pack.ordinary_step_eq _ _ ordinary valid)

def PathOK : MachineState → List Nat → Prop
  | _, [] => True
  | s, n::ns => n<75 ∧ s.pc=pcOf n ∧ ordinaryInstr (instrAt n)=true ∧
      memoryArgumentsValid s (instrAt n)=true ∧ PathOK (execInstrBr s (instrAt n)) ns

theorem runs_path (s : MachineState) (ns : List Nat) (ok : PathOK s ns) :
    Hop s (run s ns) ns.length (cycles ns) := by
  induction ns generalizing s with
  | nil => exact Hop.refl s
  | cons n ns ih =>
    obtain ⟨hn,pc,ord,valid,rest⟩ := ok
    exact ((runs_step s n hn pc ord valid).thenDo (ih _ rest)).cast
      (by simp [Nat.add_comm]) (by simp [cycles])

def writes (i : Instr) (r : Reg) : Bool :=
  match i with
  | .ADD d .. | .SUB d .. | .MUL d .. | .DIVU d .. | .OR d .. | .SRL d ..
  | .ADDI d .. | .ANDI d .. | .SLLI d .. | .SRLI d .. | .LBU d .. | .JAL d .. => decide (r=d ∧ d≠.x0)
  | _ => false

def safe : Instr → Bool
  | .ADD .. | .SUB .. | .MUL .. | .DIVU .. | .OR .. | .SRL .. | .ADDI ..
  | .ANDI .. | .SLLI .. | .SRLI .. | .LBU .. | .SB .. | .BEQ .. | .BLTU .. | .JAL .. => true
  | _ => false

theorem code_safe (n : Nat) (hn : n<75) : safe (instrAt n)=true :=
  (show ∀ n : Fin 75, safe (instrAt n.val)=true by decide) ⟨n,hn⟩

theorem keep_step (s : MachineState) (i : Instr) (r : Reg) (hi : safe i=true)
    (hr : writes i r=false) : (execInstrBr s i).getReg r=s.getReg r := by
  cases i <;> simp only [safe] at hi <;> try contradiction
  all_goals simp_all [writes,execInstrBr,Opening.getReg_setReg,apply_ite]
  all_goals split <;> simp_all

theorem keep_path (s : MachineState) (ns : List Nat) (r : Reg)
    (safePath : ∀ n∈ns, n<75) (hr : ns.all (fun n => !(writes (instrAt n) r))=true) :
    (run s ns).getReg r=s.getReg r := by
  induction ns generalizing s with
  | nil => rfl
  | cons n ns ih =>
    simp only [List.all_cons,Bool.and_eq_true,Bool.not_eq_true'] at hr
    rw [run,List.foldl_cons]
    exact (ih _ (fun i hi => safePath i (by simp [hi])) hr.2).trans
      (keep_step s _ r (code_safe n (safePath n (by simp))) hr.1)

def other (s : MachineState) :=
  (s.code,s.committed,s.publicValues,s.privateInput,s.inputBufBase,s.regs .x0)

@[simp] theorem other_setReg (s : MachineState) (r : Reg) (v : Word) : other (s.setReg r v)=other s := by
  cases r <;> rfl
@[simp] theorem other_setPC (s : MachineState) (p : Word) : other (s.setPC p)=other s := rfl
@[simp] theorem other_setByte (s : MachineState) (a : Word) (b : Byte) : other (s.setByte a b)=other s := rfl

theorem step_other (s : MachineState) (i : Instr) (hi : safe i=true) : other (execInstrBr s i)=other s := by
  cases i <;> simp only [safe] at hi <;> try contradiction
  all_goals simp_all [execInstrBr,apply_ite]

theorem step_unaligned (s : MachineState) (i : Instr) (hi : safe i=true)
    (a : Word) (ha : alignToDword a≠a) : (execInstrBr s i).mem a=s.mem a := by
  change (execInstrBr s i).getMem a=s.getMem a
  cases i <;> simp only [safe] at hi <;> try contradiction
  all_goals simp_all [execInstrBr,apply_ite]
  exact setByte_unaligned _ _ _ _ ha
  all_goals split <;> simp_all

inductive Reach : MachineState → MachineState → Prop
  | refl (s) : Reach s s
  | step (s) (n) (hn : n<75) : Reach s (execInstrBr s (instrAt n))
  | trans {s t u} : Reach s t → Reach t u → Reach s u

theorem reach_path (s : MachineState) (ns : List Nat) (ok : PathOK s ns) : Reach s (run s ns) := by
  induction ns generalizing s with
  | nil => exact Reach.refl s
  | cons n ns ih => exact (Reach.step s n ok.1).trans (ih _ ok.2.2.2.2)

theorem Reach.other_eq {s t : MachineState} (h : Reach s t) : other t=other s := by
  induction h with
  | refl => rfl
  | step s n hn => exact step_other s _ (code_safe n hn)
  | trans _ _ ih ih' => exact ih'.trans ih

theorem Reach.keep {s t : MachineState} (h : Reach s t) (r : Reg)
    (hr : ∀ n<75, writes (instrAt n) r=false) : t.getReg r=s.getReg r := by
  induction h with
  | refl => rfl
  | step s n hn => exact keep_step s _ r (code_safe n hn) (hr n hn)
  | trans _ _ ih ih' => exact ih'.trans ih

theorem Reach.unaligned {s t : MachineState} (h : Reach s t) (a : Word) (ha : alignToDword a≠a) :
    t.mem a=s.mem a := by
  induction h with
  | refl => rfl
  | step s n hn => exact step_unaligned s _ (code_safe n hn) a ha
  | trans _ _ ih ih' => exact ih'.trans ih

end TwoPermutationPrototype.Packed.Checker.TailRestore
