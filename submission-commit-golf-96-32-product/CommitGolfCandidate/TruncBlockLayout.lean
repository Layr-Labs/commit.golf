import CommitGolfCandidate.TruncMoveRun
import CommitGolfCandidate.TruncLayoutFacts
namespace CommitGolfCandidate.Trunc.Wire
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

def im (back : Bool) := submission.image (if back then .check else .opening)
def rowPC (back record : Bool) :=
  if back then (if record then 488 else 452) else (if record then 155 else 670)
def bodyPC (back record : Bool) := rowPC back record+(if back then 2 else 0)
private def codeSuffix (b : Bool) := if b then checkWireCode else openingWireCode
private def offset (b f : Bool) := bodyPC b f

private def compareOp (word : Option Instruction) (op : Instr) : Bool :=
  match word,op with
  | some (.base (.SH a b i)),.SH x y j => a==x && b==y && i==j
  | some (.base (.LHU a b i)),.LHU x y j => a==x && b==y && i==j
  | _,_=>false

private theorem comparison {word op} (h : compareOp word op=true) : word=some (.base op) := by
  unfold compareOp at h;split at h <;> simp_all [Bool.and_eq_true,beq_iff_eq]

private def codeMatches : List (BitVec 32) → List Instr → Bool
  | _,[]=>true
  | [],_::_=>false
  | w::code,x::ops=>compareOp (decodeInstruction w) x && codeMatches code ops

private theorem onWord {code : List (BitVec 32)} {ops : List Instr} (agree : codeMatches code ops=true) :
    ∀ j (h : j<ops.length),code[j]?.bind decodeInstruction=some (.base ops[j]) := by
  induction ops generalizing code with
  | nil=>intro j h;simp at h
  | cons x xs ih=>
    cases code with
    | nil=>simp [codeMatches] at agree
    | cons w ws=>
      have split : compareOp (decodeInstruction w) x=true ∧ codeMatches ws xs=true := by simpa only [codeMatches,Bool.and_eq_true] using agree
      intro j h;cases j with
      | zero=>exact comparison split.1
      | succ j=>exact ih split.2 j (by simpa using h)

private theorem known : ∀ b f : Bool,
    codeMatches ((codeSuffix b).drop (offset b f)) (sequence b f)=true := by decide

theorem bodyEncoded (b f : Bool) : Slice (im b) (bodyPC b f) (sequence b f) := by
  intro i hi
  have eqn:=onWord (known b f) i hi
  rw [List.getElem?_drop] at eqn
  unfold im;rw [wire_image];cases b <;> exact eqn

theorem movesLegal (b f : Bool) : ∀ m∈moves b f,legal m := by
  intro m hm
  obtain ⟨j,hj,eq⟩:=List.mem_map.mp hm;subst m
  have l:=localFacts b f j (List.mem_range.mp hj)
  have tgt:=l.target;have e:=l.even
  refine ⟨?_,e,?_⟩
  · cases b <;> cases f <;> simp only [wide,short,Bool.false_eq_true,ite_true,ite_false] at tgt <;> omega
  · intro x hx;have h:=l.source x hx
    cases b <;> cases f <;> simp only [short,wide,Bool.false_eq_true,ite_false,ite_true] at h <;> omega

theorem listKept (ms : List Move) (s : MachineState) (r : Reg) (h : r≠.x6) :
    (moveList ms s).getReg r=s.getReg r := by
  induction ms generalizing s with
  | nil=>rfl
  | cons m l ih =>
    change ((instructions m++l.flatMap instructions).foldl execInstrBr s).getReg r=_
    rw [List.foldl_append]
    exact (ih (after m s)).trans (moveKeeps m s r h)

theorem listPC (ms : List Move) (s : MachineState) :
    (moveList ms s).pc=s.pc+BitVec.ofNat 64 (4*(ms.flatMap instructions).length) := by
  induction ms generalizing s with
  | nil=>simp [moveList]
  | cons m l ih =>
    change ((instructions m++l.flatMap instructions).foldl execInstrBr s).pc=_
    rw [List.foldl_append]
    change (moveList l (after m s)).pc=_
    rw [ih,movePC,BitVec.add_assoc,←BitVec.ofNat_add,List.flatMap_cons,List.length_append];congr 2;omega

theorem runBody (b f : Bool) (r : Nat) (hr : r<128) (s : MachineState) (pc : s.pc=loc (bodyPC b f))
    (src : s.getReg .x18=BitVec.ofNat 64 (base+sourceStart b f r))
    (dst : s.getReg .x19=BitVec.ofNat 64 (base+destStart b f r)) :
    Runs (im b) s (moveList (moves b f) s) (sequence b f).length (sequence b f).length := by
  have space : bodyPC b f+(sequence b f).length≤2048 := by rw [cores];cases b <;> cases f <;> decide
  apply bodyRun _ _ _ _ _ _ pc space (bodyEncoded _ _) (movesLegal _ _) src dst
  all_goals cases b <;> cases f <;> simp [base,sourceStart,destStart,wBase,sBase,MEMORY_BYTES] <;> omega
end CommitGolfCandidate.Trunc.Wire
