import CommitGolfCandidate.Layout2WriterModel
namespace CommitGolfCandidate.Layout2Writer
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Layout2Phase
set_option maxRecDepth 20000
set_option maxHeartbeats 2200000

private def copies (base : T) (f dst count : Nat) : List Row :=
  (List.range count).flatMap fun j=>[.load .d base f j,.store .d (dst+j)]
private def mateRows (i : Nat) : List Row :=
  [.mateOffset (i+1),.mateBase (i+1)] ++ copies .aux (i+1) (2+4*i) 4
private def levelRows (l : Nat) : List Row := [.ascend (l-1),.flip l,.scale l,.sibling l]
private def bandA (i : Nat) : List Row :=
  let f:=6+i
  levelRows (2+i) ++ copies .ptr f (22+3*i) 3 ++
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

def program (p : Nat) : List Row :=
  copies .ptr 0 0 2 ++ [.residue,.selector,.quartet,.groupDelta,.groupBase] ++ (List.range 3).flatMap mateRows ++
  [.pointer] ++ copies .ptr 4 14 4 ++ [.root] ++ levelRows 1 ++ copies .ptr 5 18 4 ++
  (List.range 4).flatMap bandA ++ (List.range 8).flatMap (bandB p)

def result (p : Nat) := (program p).foldl advance initial

theorem program_valid (p : Nat) (small : p<4) :
    checked p initial (program p)=true ∧ (program p).length=bodyLen p ∧
    (result p).reg .c=(symStream p).1 ∧ (result p).reg .n=.node 13 ∧
    ∀ j : Fin (stride p/8), (result p).out j.val=some ((expected p).getD j.val (.data 0)) := by
  interval_cases p <;> decide +kernel

def decodedBase (word : BitVec 32) : Option Instr :=
  match decodeInstruction word with | some (.base i)=>some i | _=>none

/-- Exact code footprint needed to instantiate the verified writer in any opening image. -/
def BodyAt (image : Image) (p : Nat) : Prop :=
  (((image.code.drop (bodyWord p)).take (program p).length).map decodedBase)=
    (program p).map (fun r=>some (instruction r))
instance (I : Image) (p : Nat) : Decidable (BodyAt I p) := by unfold BodyAt;infer_instance

def CodeAt (image : Image) (w : Nat) (rs : List Row) : Prop :=
  ∀ i : Fin rs.length, (image.code[w+i.val]?).bind decodeInstruction=some (.base (instruction rs[i]))

theorem body_decoded {I p} (code : BodyAt I p) : CodeAt I (bodyWord p) (program p) := by
  intro i
  have h:=congrArg (fun xs : List (Option Instr)=>xs[i.val]?) code
  simp only [List.getElem?_map,List.getElem?_take,i.isLt,ite_true,List.getElem?_drop,
    List.getElem?_eq_getElem i.isLt,Option.map_some] at h
  cases word : I.code[bodyWord p+i.val]? with
  | none => simp [word] at h
  | some w =>
    simp only [word,Option.map_some,Option.some.injEq] at h
    unfold decodedBase at h
    cases decoded : decodeInstruction w with
    | none => simp [decoded] at h
    | some inst =>
      cases inst <;> simp_all

end CommitGolfCandidate.Layout2Writer
