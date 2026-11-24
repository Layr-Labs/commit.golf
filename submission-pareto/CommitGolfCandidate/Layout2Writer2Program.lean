import CommitGolfCandidate.Layout2WriterProgram
import CommitGolfCandidate.Layout2Phase2
namespace CommitGolfCandidate.Layout2Writer2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Layout2Phase Layout2Writer
set_option maxRecDepth 16000
set_option maxHeartbeats 1800000
abbrev qword (q j : Nat) := 9+4*q+j

/-- Logical slots 9..24 are reached through the selected reply-slot base in x28. -/
def routed (j : Nat) : Bool := decide (9≤j ∧ j<25)
def op : Row → Instr
  | .store t j => if routed j then .SD .x28 t.reg (BitVec.ofNat 12 (8*(9+(j-9)%4)))
                   else .SD .x21 t.reg (BitVec.ofNat 12 (8*j))
  | r => instruction r

def start2 : Model := ⟨fun t=>match t with | .n=>.pos | .ptr=>.base 4 | .c=>.carry | x=>.orig x,fun _=>none⟩

def need (q p : Nat) (m : Model) (r : Row) : Prop :=
  match r with
  | .store _ j => 8*j+8≤stride p ∧ (routed j=true → m.reg .aux=.orig .aux ∧ 9+4*q≤j ∧ j<13+4*q)
  | .load d b f j => 4≤f ∧ pre p m (.load d b f j)
  | .quartet | .root | .ascend .. | .flip .. | .scale .. | .sibling .. | .shl .. | .shr .. | .bor .. => pre p m r
  | _ => False

instance (q p m r) : Decidable (need q p m r) := by
  cases r <;> unfold need <;> infer_instance

def valid (q p : Nat) (m : Model) : List Row→Bool
  | [] => true
  | r::rs => decide (need q p m r) && valid q p (advance m r) rs

def headOps : List Instr := [.ANDI .x10 .x6 3,.SLLI .x10 .x10 5,.ADD .x28 .x21 .x10,.LD .x7 .x21 16]
private def copies (base : T) (f dst count : Nat) : List Row :=
  (List.range count).flatMap fun j=>[.load .d base f j,.store .d (dst+j)]
private def levelRows (l : Nat) : List Row := [.ascend (l-1),.flip l,.scale l,.sibling l]
private def bandA (i : Nat) : List Row :=
  let f:=6+i
  levelRows (2+i) ++ copies .ptr f (if i=0 then 6 else 22+3*i) 3 ++
    (match i with
     | 0 => [.load .a .ptr f 3]
     | 1 => [.load .d .ptr f 3,.shl .aux .d 48,.bor .a .a .aux,.store .a 34,.shr .a .d 16]
     | 2 => [.load .d .ptr f 3,.shl .aux .d 32,.bor .a .a .aux,.store .a 35,.shr .a .d 32]
     | _ => [.load .d .ptr f 3,.shl .aux .d 16,.bor .a .a .aux,.store .a 36])
private def bandB (p i : Nat) : List Row :=
  let f:=10+i
  let n:= (carryIn p+46*i)%64
  let out:=61+(carryIn p+46*i)/64
  levelRows (6+i) ++ copies .ptr f (37+3*i) 3 ++
    if n=0 then [.load .c .ptr f 3]
    else if n<18 then [.load .d .ptr f 3,.shl .d .d n,.bor .c .c .d]
    else if n=18 then [.load .d .ptr f 3,.shl .d .d 18,.bor .c .c .d,.store .c out]
    else [.load .d .ptr f 3,.shl .aux .d n,.bor .c .c .aux,.store .c out,.shr .c .d (64-n)]

def rows (p q : Nat) : List Row :=
  copies .ptr 4 (qword q 0) 4 ++ [.quartet,.root] ++ levelRows 1 ++ copies .ptr 5 2 4 ++
  (List.range 4).flatMap bandA ++ (List.range 8).flatMap (bandB p)

def finalModel (p q : Nat) := (rows p q).foldl advance start2

def correct (p q : Nat) : Prop :=
  valid q p start2 (rows p q)=true ∧ 4+(rows p q).length=Layout2Phase2.bodyLen p ∧
    (finalModel p q).reg .c=(symStream p).1 ∧ (finalModel p q).reg .n=.node 13 ∧
    ∀ d : Fin (stride p/8), (finalModel p q).out d.val =
      if Layout2Phase2.written q d.val then some ((expected p).getD (Layout2Phase2.v1Dword d.val) (.data 0)) else none

instance (p q) : Decidable (correct p q) := by unfold correct;infer_instance

def listing (p q : Nat) := headOps ++ (rows p q).map op
def ImageAt (I : Image) (p : Nat) : Prop :=
  (((I.code.drop (Layout2Phase2.bodyWord p)).take (Layout2Phase2.bodyLen p)).map decodedBase) =
    (listing p 0).map some
instance (I p) : Decidable (ImageAt I p) := by unfold ImageAt;infer_instance

theorem same_listing : ∀ p q : Fin 4, listing p q=listing p 0 := by decide +kernel
end CommitGolfCandidate.Layout2Writer2
