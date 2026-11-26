import CommitGolfCandidate.S5OpenCode
import CommitGolfCandidate.S5OpenSources
import CommitGolfCandidate.S5FirstRound
import CommitGolfCandidate.S5Operations
namespace CommitGolfCandidate.S5Machine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

def tableOffset (l : Nat) := levelOffset l

def materialize (l : Nat) : List Instr :=
  let off:=tableOffset l
  let lo:=BitVec.ofNat 12 off
  let load:=if off<2048 then [.ADDI .x6 .x0 lo] else
    [.LUI .x6 (BitVec.ofNat 20 ((off+2048)/4096))] ++ (if lo=0 then [] else [.ADDI .x6 .x6 lo])
  load ++ [.ADD .x6 .x8 .x6]

def tableIndex : Nat→Nat
  | 0=>0
  | k+1=>tableIndex k + (materialize k).length+1

def tablePC (batch : Bool) (l : Nat) := (if batch then 44 else 402)+tableIndex l
def tableSlot (l : Nat) := 2048+8*l
def storeAt (l : Nat) := Instr.SD .x3 .x6 (BitVec.ofNat 12 (8*l))
def tableInitial : KnownRegs := fun r=>if r=.x0 then some 0 else if r=.x8 then some (W tdBase) else none

private theorem tableFacts : ∀ l : Fin 25,
    (materialize l.val).all setupOp ∧ (materialize l.val).foldl knownStep tableInitial .x6=some (W (tdBase+levelOffset l.val)) ∧
    (materialize l.val).all (fun op=>match op with | .ADDI .x6 .. | .LUI .x6 .. | .ADD .x6 ..=>true | _=>false) ∧
    signExtend12 (BitVec.ofNat 12 (8*l.val))=W (8*l.val) ∧
    accessValid (W (tableSlot l.val)) 8=true := by decide +kernel

private theorem tableSites : ∀ batch : Bool,∀ l : Fin 25,
    tablePC batch l.val+(materialize l.val).length<993 ∧
    (List.range (materialize l.val).length).all (fun j=>
      matchesWord .opening (tablePC batch l.val+j,((materialize l.val)[j]?).getD .EBREAK)) ∧
    matchesWord .opening (tablePC batch l.val+(materialize l.val).length,storeAt l.val) := by decide +kernel

def putTable (s : MachineState) (l : Nat) := execInstrBr ((materialize l).foldl execInstrBr s) (storeAt l)

private theorem keepReg (s : MachineState) (xs : List Instr)
    (all : xs.all (fun op=>match op with | .ADDI .x6 .. | .LUI .x6 .. | .ADD .x6 ..=>true | _=>false))
    (r : Reg) (diff : r≠.x6) : (xs.foldl execInstrBr s).getReg r=s.getReg r := by
  induction xs generalizing s with
  | nil=>rfl
  | cons op rest ih=>
    simp only [List.all_cons,Bool.and_eq_true] at all
    rw [List.foldl_cons,ih _ all.2]
    have one:=all.1
    split at one <;> first | contradiction | exact MachineState.getReg_setPC.trans (MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm diff))

theorem put_table (s : MachineState) (l : Fin 25) (batch : Bool) (pc : s.pc=pcAt (tablePC batch l))
    (base : s.getReg .x8=W tdBase) (gp : s.getReg .x3=W 2048) :
    let t:=putTable s l
    let n:=(materialize l).length+1
    Runs s t n n ∧ t.pc=pcAt (tablePC batch (l.val+1)) ∧
    (∀ r, r≠.x6→t.getReg r=s.getReg r) ∧
    (∀ a, t.getMem a=if a==W (tableSlot l) then W (tdBase+levelOffset l) else s.getMem a) := by
  obtain ⟨sane,out,only6,off,valid⟩:=tableFacts l
  obtain ⟨bound,layout,last⟩:=tableSites batch l
  let ops:=materialize l
  let u:=ops.foldl execInstrBr s
  have known : Agrees tableInitial s := by
    intro r v e; cases r <;> simp [tableInitial] at e <;> subst v <;> first | rfl | exact base
  have value : u.getReg .x6=W (tdBase+levelOffset l) := known_header ops tableInitial s
    (List.all_eq_true.mp sane) known _ _ out
  have keep (r : Reg) (h : r≠.x6) := keepReg s ops only6 r h
  have prop:=header_properties ops s (List.all_eq_true.mp sane)
  have slot : u.getReg .x3+signExtend12 (BitVec.ofNat 12 (8*l.val))=W (tableSlot l) := by
    rw [keep _ (by decide),gp,off];exact (BitVec.ofNat_add ..).symm
  have addr : memoryArgumentsValid u (storeAt l)=true := by change accessValid (_+_) 8=true;rw [slot];exact valid
  have next : u.pc=pcAt (tablePC batch l+ops.length) := by rw [show u.pc=_ from prop.2,pc,pc_delta]
  have linear : Runs s u ops.length ops.length := by
    intro fuel;apply execute_linear .opening true ops _ _ _ pc
    · intro c m;exact header_straight c (List.all_eq_true.mp sane c m)
    · intro i hi
      have h:=List.all_eq_true.mp layout i (List.mem_range.mpr hi)
      rw [List.getElem?_eq_getElem hi,Option.getD_some] at h
      apply site (by change _<993;dsimp [ops] at hi;omega)
      simpa [matchesWord,show tablePC batch l+i<words .opening by change _<993;dsimp [ops] at hi;omega] using h
  have lastCode : decodeInstruction (openWord (tablePC batch l+ops.length))=some (.base (storeAt l)) := by
    simpa [matchesWord,openWord,words,bound,ops] using last
  have oneStep : Runs u (putTable s l) 1 1 := one _ bound _ lastCode _ _ next
    (by change (if memoryArgumentsValid u (storeAt l) then some (execInstrBr u (storeAt l)) else none)=_
        rw [addr];rfl)
  refine ⟨linear.trans oneStep,?_,?_,?_⟩
  · change u.pc+4=_
    rw [next,pc_succ];apply congrArg pcAt;simp [tablePC,tableIndex,ops,Nat.add_assoc]
  · intro r hr;exact (show (putTable s l).getReg r=u.getReg r by cases r <;> rfl).trans (keep _ hr)
  · intro a;change (if a==_ then u.getReg .x6 else u.getMem a)=_
    rw [value,slot];simp only [MachineState.getMem,show u.mem=s.mem from prop.1]
end CommitGolfCandidate.S5Machine.Open
