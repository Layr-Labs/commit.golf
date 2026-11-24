import CommitGolfCandidate.Layout2WriterSources
namespace CommitGolfCandidate.Layout2Writer
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Layout2Phase

inductive T where | n | ptr | a | c | aux | d deriving DecidableEq
def T.reg : T→Reg | .n=>.x6 | .ptr=>.x7 | .a=>.x10 | .c=>.x11 | .aux=>.x28 | .d=>.x31
inductive V where
  | orig (t:T) | pos | base (f:Nat) | carry | residue | selector | quartet | groupDelta | grp | mate (f:Nat)
  | node (l:Nat) | flipped (l:Nat) | scaled (l:Nat)
  | data (off:Nat) | shl (v:V) (n:Nat) | shr (v:V) (n:Nat) | bor (x y:V)
  deriving DecidableEq

def denote (s : MachineState) (pos l22 : Nat) (c : Word) : V→Word
  | .orig t => s.getReg t.reg
  | .pos => addr pos
  | .base f => addr (fieldBase l22 pos f)
  | .carry => c
  | .residue => addr (pos%4)
  | .selector => addr (32*(pos%4))
  | .quartet => addr (pos/4)
  | .groupDelta => addr (1024*(pos/4))
  | .grp => addr (group pos)
  | .mate f => addr (mateOffset pos f)
  | .node l => addr (node pos l)
  | .flipped l => addr (node pos l ^^^ 1)
  | .scaled l => addr (32*(node pos l ^^^ 1))
  | .data k => dwordOf (recordSource s l22 pos) k
  | .shl v n => denote s pos l22 c v <<< n
  | .shr v n => denote s pos l22 c v >>> n
  | .bor x y => denote s pos l22 c x ||| denote s pos l22 c y

structure Model where
  reg : T→V
  out : Nat→Option V

def initial : Model := ⟨fun t=>match t with | .n=>.pos | .ptr=>.base 0 | .c=>.carry | x=>.orig x,fun _=>none⟩

/-- Address roles annotate the observable stage of each RV instruction. They generate no code. -/
inductive Row where
  | residue | selector | quartet | groupDelta | groupBase | mateOffset (f:Nat) | mateBase (f:Nat) | pointer
  | root | ascend (l:Nat) | flip (l:Nat) | scale (l:Nat) | sibling (l:Nat)
  | load (dst base:T) (f j:Nat) | store (src:T) (slot:Nat)
  | shl (dst src:T) (n:Nat) | shr (dst src:T) (n:Nat) | bor (dst x y:T)

def instruction : Row→Instr
  | .residue => .ANDI .x10 .x6 3
  | .selector => .SLLI .x10 .x10 5
  | .quartet => .SRLI .x6 .x6 2
  | .groupDelta => .SLLI .x7 .x6 10
  | .groupBase => .ADD .x7 .x7 .x18
  | .mateOffset f => .XORI .x28 .x10 (BitVec.ofNat 12 (32*f))
  | .mateBase _ => .ADD .x28 .x28 .x7
  | .pointer => .LD .x7 .x7 128
  | .root => .ADD .x6 .x6 .x19
  | .ascend _ => .SRLI .x6 .x6 1
  | .flip _ => .XORI .x7 .x6 1
  | .scale _ => .SLLI .x7 .x7 5
  | .sibling _ => .ADD .x7 .x9 .x7
  | .load d b _ j => .LD d.reg b.reg (BitVec.ofNat 12 (8*j))
  | .store t j => .SD .x21 t.reg (BitVec.ofNat 12 (8*j))
  | .shl d t n => .SLLI d.reg t.reg (BitVec.ofNat 6 n)
  | .shr d t n => .SRLI d.reg t.reg (BitVec.ofNat 6 n)
  | .bor d x y => .OR d.reg x.reg y.reg

inductive Effect where | reg (t:T) (v:V) | mem (j:Nat) (v:V)

def effect (m : Model) : Row→Effect
  | .residue => .reg .a .residue
  | .selector => .reg .a .selector
  | .quartet => .reg .n .quartet
  | .groupDelta => .reg .ptr .groupDelta
  | .groupBase => .reg .ptr .grp
  | .mateOffset f => .reg .aux (.mate f)
  | .mateBase f => .reg .aux (.base f)
  | .pointer => .reg .ptr (.base 4)
  | .root => .reg .n (.node 0)
  | .ascend l => .reg .n (.node (l+1))
  | .flip l => .reg .ptr (.flipped l)
  | .scale l => .reg .ptr (.scaled l)
  | .sibling l => .reg .ptr (.base (4+l))
  | .load d _ f j => .reg d (.data (start f+8*j))
  | .store t j => .mem j (m.reg t)
  | .shl d t n => .reg d (.shl (m.reg t) n)
  | .shr d t n => .reg d (.shr (m.reg t) n)
  | .bor d x y => .reg d (.bor (m.reg x) (m.reg y))

def changeReg (m : Model) (t : T) (v : V) : Model := {m with reg:=fun u=>if u=t then v else m.reg u}
def changeMem (m : Model) (j : Nat) (v : V) : Model := {m with out:=fun i=>if i=j then some v else m.out i}
def advance (m : Model) (r : Row) : Model := match effect m r with
  | .reg t v => changeReg m t v
  | .mem j v => changeMem m j v

def pre (p : Nat) (m : Model) : Row→Prop
  | .residue | .quartet => m.reg .n=.pos
  | .selector => m.reg .a=.residue
  | .groupDelta | .root => m.reg .n=.quartet
  | .groupBase => m.reg .ptr=.groupDelta
  | .mateOffset f => m.reg .a=.selector ∧ 0<f ∧ f<4
  | .mateBase f => m.reg .aux=.mate f ∧ m.reg .ptr=.grp ∧ 0<f ∧ f<4
  | .pointer => m.reg .ptr=.grp
  | .ascend l | .flip l => m.reg .n=.node l
  | .scale l => m.reg .ptr=.flipped l
  | .sibling l => m.reg .ptr=.scaled l ∧ 0<l
  | .load _ b f j => m.reg b=.base f ∧ 8*j+8≤width f
  | .store _ j => 8*j+8≤stride p
  | .shr _ _ n | .shl _ _ n => n<64
  | .bor .. => True
instance (p m row) : Decidable (pre p m row) := by cases row <;> unfold pre <;> infer_instance

def checked (p : Nat) (m : Model) : List Row→Bool
  | [] => true
  | r::rs => decide (pre p m r) && checked p (advance m r) rs

abbrev Stream := V × Nat × List V
def symStep (st : Stream) (v : V) : Stream :=
  if st.2.1=0 then (v,46,st.2.2)
  else if st.2.1<18 then (.bor st.1 (.shl v st.2.1),st.2.1+46,st.2.2)
  else if st.2.1=18 then (.bor st.1 (.shl v 18),0,st.2.2++[.bor st.1 (.shl v 18)])
  else (.shr v (64-st.2.1),st.2.1+46-64,st.2.2++[.bor st.1 (.shl v st.2.1)])
def tailAV (a : Nat) := V.data (176+32*a+24)
def tailBV (a : Nat) := V.data (304+32*a+24)
def symStream (p : Nat) : Stream :=
  ((List.range 8).map tailBV).foldl symStep (.carry,carryIn p,[])
def expected (p : Nat) : List V :=
  [.data 0,.data 8] ++ (List.range 12).map (fun i=>V.data (16+8*i)) ++
  (List.range 4).map (fun i=>V.data (112+8*i)) ++ (List.range 4).map (fun i=>V.data (144+8*i)) ++
  (List.range 12).map (fun i=>V.data (176+32*(i/3)+8*(i%3))) ++
  [.bor (tailAV 0) (.shl (tailAV 1) 48),.bor (.shr (tailAV 1) 16) (.shl (tailAV 2) 32),
   .bor (.shr (tailAV 2) 32) (.shl (tailAV 3) 16)] ++
  (List.range 24).map (fun i=>V.data (304+32*(i/3)+8*(i%3))) ++ (symStream p).2.2

def mapStream (ev : V→Word) (st : Stream) := (ev st.1,st.2.1,st.2.2.map ev)
theorem eval_step (s : MachineState) (pos l22 : Nat) (c : Word) (st : Stream) (v : V) :
    let ev:=denote s pos l22 c
    mapStream ev (symStep st v)=streamStep (mapStream ev st) (ev v) := by
  dsimp only;unfold symStep streamStep mapStream;split_ifs <;> simp [denote]

theorem eval_fold (s : MachineState) (pos l22 : Nat) (c : Word) (xs : List V) (st : Stream) :
    let ev:=denote s pos l22 c
    mapStream ev (xs.foldl symStep st)=(xs.map ev).foldl streamStep (mapStream ev st) := by
  induction xs generalizing st with
  | nil => rfl
  | cons x xs ih => dsimp only; rw [List.foldl_cons,ih,List.map_cons,List.foldl_cons,eval_step]

theorem eval_stream (s : MachineState) (pos l22 : Nat) (c : Word) (p : Nat) :
    mapStream (denote s pos l22 c) (symStream p)=streamRun p (recordSource s l22 pos) c := by
  unfold symStream streamRun;rw [eval_fold];rfl

attribute [local irreducible] symStream streamRun

theorem eval_expected (s : MachineState) (pos l22 : Nat) (c : Word) (p : Nat) :
    (expected p).map (denote s pos l22 c)=writerDwords p (recordSource s l22 pos) c := by
  have res:=eval_stream s pos l22 c p
  have stream:=congrArg (fun t : Word × Nat × List Word=>t.2.2) res
  dsimp only [mapStream] at stream
  simp only [expected,writerDwords,List.map_append,List.map_map,List.map_cons,List.map_nil,
    bandATails,tailA,tailAV,Function.comp_def,denote,stream]

end CommitGolfCandidate.Layout2Writer
