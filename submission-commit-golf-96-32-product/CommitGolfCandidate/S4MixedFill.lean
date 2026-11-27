import CommitGolfCandidate.S4FillState

set_option Elab.async false
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (Digest pcAt)
def blockWord (ps : List (List Instr)) (i : Nat) := (ps.take i).flatten.length
theorem segment {c : Code} (n : Nat) (ps : List (List Instr)) (ok : Matches c n ps.flatten)
    (j : Nat) (bj : j<ps.length) : Matches c (n+blockWord ps j) ps[j] := by
  induction ps generalizing n j with
  | nil=>simp at bj
  | cons x xs ih=>
    cases j with
    | zero=>exact ok.left
    | succ j=>
      have f:=ih (n+x.length) ok.right j (by simpa using bj)
      simpa only [blockWord,List.take_succ_cons,List.flatten_cons,List.length_append,Nat.add_assoc,List.getElem_cons_succ] using f

def segments (tern : Bool) : List (List Instr) :=
  [calcCode (digits tern),depositCode 256,calcCode (rotate tern),depositCode 352]++
    if tern then [calcCode (rotate true),depositCode 384] else [[.ADDI .x14 .x0 512],zeroOps 4]
def fillSize (b : Bool) := if b then 39 else 30
private theorem layout : ∀ b : Bool,(segments b).flatten.length=fillSize b:=by decide

structure Filled (o : Oracle) (s t : MachineState) (site n h j : Nat) : Prop where
  run : CheckRuns o s t n 0
  pc : t.pc=pcAt (site+n)
  idx : t.getReg .x20=W (j/radix h)
  keep : ∀ r,untouchedFill r → t.getReg r=s.getReg r
  outside : SameOutside s t 512 96
  row : readBuffer t 512 96=payload (lane h j) (readBuffer s 256 32) (readBuffer s 352 32,readBuffer s 384 32)

private theorem ternary (o : Oracle) (s : MachineState) (n j : Nat) (pc : s.pc=pcAt n)
    (room : n+39≤Code.check.count) (ok : Matches .check n (segments true).flatten)
    (idx : s.getReg .x20=W j) (small : j<2^64) (three : s.getReg .x23=3) :
    ∃ t,Filled o s t n 39 0 j := by
  have part:=segment n (segments true) ok
  have f:=fillStart true o s n j pc (by omega) (part 0 (by decide)) idx small three
  let k:=j%3;have bk : k<3:=Nat.mod_lt _ (by decide)
  have a:=f.put 256 (Or.inl rfl) bk (by omega) (part 1 (by decide))
  have b:=a.turn true (by change n+2+11+2≤_;omega) (part 2 (by decide)) bk three
  have c:=b.put 352 (Or.inr (Or.inl rfl)) (Nat.mod_lt _ (by decide)) (by change n+2+11+2+11≤_;omega) (part 3 (by decide))
  have d:=c.turn true (by change n+2+11+2+11+2≤_;omega) (part 4 (by decide)) (Nat.mod_lt _ (by decide)) three
  have e:=d.put 384 (Or.inr (Or.inr rfl)) (Nat.mod_lt _ (by decide)) (by change n+2+11+2+11+2+11≤_;omega) (part 5 (by decide))
  refine ⟨_,e.run,e.pc.trans (congrArg pcAt (by change n+2+11+2+11+2+11=n+39;omega)),e.index,e.keep,e.frame,?_⟩
  rw [tripleRead,e.read 2 (by decide),e.read 1 (by decide),e.read 0 (by decide)]
  exact cyclicPayload j _ _ _ _

attribute [local irreducible] deposit Sym.evaluated clearState
set_option maxRecDepth 5000 in
private theorem binary (o : Oracle) (s : MachineState) (n j h : Nat) (pos : 0<h) (pc : s.pc=pcAt n)
    (room : n+30≤Code.check.count) (ok : Matches .check n (segments false).flatten)
    (idx : s.getReg .x20=W j) (small : j<2^64) (three : s.getReg .x23=3) :
    ∃ t,Filled o s t n 30 h j := by
  have part:=segment n (segments false) ok
  have f:=fillStart false o s n j pc (by omega) (part 0 (by decide)) idx small three
  have bk : j%2<2:=Nat.mod_lt _ (by decide)
  have a:=f.put 256 (Or.inl rfl) (by change j%2<3;omega) (by omega) (part 1 (by decide))
  have b:=a.turn false (by change n+2+11+1≤_;omega) (part 2 (by decide)) bk three
  have bd : (j%2+1)%2<3:=by omega
  have c:=b.put 352 (Or.inr (Or.inl rfl)) bd (by change n+2+11+1+11≤_;omega) (part 3 (by decide))
  let src:=deposit (Sym.evaluated (rotate false) (deposit (Sym.evaluated (digits false) s) 256)) 352
  let u:=execInstrBr src (.ADDI .x14 .x0 512)
  have k4 : Matches .check (n+25) [.ADDI .x14 .x0 512]:=part 4 (by decide)
  have at25 : src.pc=pcAt (n+25):=c.pc.trans (congrArg pcAt (by change n+2+11+1+11=n+25;omega))
  have reset:=stepAdd .check src (n+25) .x14 .x0 512 (by omega) at25 k4.head
  have addr : u.getReg .x14=W 512:=by rw [show u.getReg .x14=src.getReg .x0+signExtend12 512 from getAfterAdd src .x14 .x0 _ (by decide)];rfl
  have next : u.pc=pcAt (n+26):=addPC _ _ _ at25
  have k5 : Matches .check (n+26) (zeroOps 4):=part 5 (by decide)
  obtain ⟨z,zero⟩:=zeroRow u (n+26) next addr (by omega) k5
  have before : SameOutside s u 512 96:=bothRows c.frame (unchangedBytes (show u.mem=src.mem from rfl) _ _)
  have rad : radix h=2:=if_neg (by omega)
  refine ⟨_,(c.run.trans (ofRuns o reset)).trans (ofRuns o z.run),z.pc.trans (congrArg pcAt (by omega)),?_,?_,
    before.combined z.outside (by omega),?_⟩
  · rw [rad];exact (z.regs .x20).trans ((keepAdd src .x14 .x0 .x20 512 (by decide)).trans c.index)
  · intro r bound
    have ne : Reg.x14≠r:=by intro eqv;subst r;exact bound (by decide)
    exact (z.regs r).trans ((keepAdd src .x14 .x0 r 512 ne).trans (c.keep r bound))
  · have lo (k : Nat) (lim : k<2) : cell (clearState u 4) k=cell src k:=
      (z.outside.read (by omega) (Or.inl (by omega))).trans (cellPreserved (show u.mem=src.mem from rfl) k)
    rw [tripleRead,show cell (clearState u 4) 2=0 from zero,lo 0 (by decide),lo 1 (by decide),c.read 0 (by decide),c.read 1 (by decide)]
    exact pairPayload h j pos _ _ _ _

theorem fill (o : Oracle) (s : MachineState) (n h j : Nat) (pc : s.pc=pcAt n)
    (room : n+fillSize (decide (h=0))≤Code.check.count) (ok : Matches .check n (segments (decide (h=0))).flatten)
    (idx : s.getReg .x20=W j) (small : j<2^64) (three : s.getReg .x23=3) :
    ∃ t,Filled o s t n (fillSize (decide (h=0))) h j := by
  by_cases zero : h=0
  · subst h;exact ternary o s n j pc room ok idx small three
  · rw [decide_eq_false zero] at room ok ⊢;exact binary o s n j h (by omega) pc room ok idx small three
end CommitGolfCandidate.S4.Machine
