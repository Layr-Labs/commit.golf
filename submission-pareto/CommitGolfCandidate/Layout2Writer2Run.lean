import CommitGolfCandidate.Layout2Writer2Head
import CommitGolfCandidate.Layout2Writer2Step
import CommitGolfCandidate.Layout2Writer2Phase0
import CommitGolfCandidate.Layout2Writer2Phase1
import CommitGolfCandidate.Layout2Writer2Phase2
import CommitGolfCandidate.Layout2Writer2Phase3

namespace CommitGolfCandidate.Layout2Writer2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Layout2Writer Layout2Phase OracleComp
set_option maxRecDepth 14000
set_option maxHeartbeats 1600000

theorem program_facts (p q : Nat) (hp : p<4) (hq : q<4) : correct p q := by
  interval_cases p
  · exact correct_phase_0 ⟨q,hq⟩
  · exact correct_phase_1 ⟨q,hq⟩
  · exact correct_phase_2 ⟨q,hq⟩
  · exact correct_phase_3 ⟨q,hq⟩

private theorem step_one {I : Image} (r : Row) (m : MachineState) (w : Nat) (small : w<2^40)
    (pc : m.pc=wordAddress w) (code : (I.code[w]?).bind decodeInstruction=some (.base (op r)))
    (ok : memoryArgumentsValid m (op r)=true) :
    RunsBlock I m (execInstrBr m (op r)) 1 ∧ (execInstrBr m (op r)).pc=wordAddress (w+1) := by
  have facts : ordinaryStep m (.base (op r))=some (execInstrBr m (op r)) ∧
      instructionCycles (.base (op r))=1 ∧ (execInstrBr m (op r)).pc=m.pc+4 := by
    cases r with
    | store t j =>
      by_cases hit : routed j=true <;> simp only [op,hit,Bool.false_eq_true,ite_true,ite_false] at ok ⊢ <;>
        exact ⟨by simp only [ordinaryStep,ok,ite_true],rfl,rfl⟩
    | _ => all_goals exact ⟨by simp only [op,instruction] at ok ⊢;simp only [ordinaryStep,ok,ite_true],rfl,rfl⟩
  exact ⟨unit m w _ small pc code facts.1 facts.2.1, facts.2.2.trans (pc ▸ pc_next w)⟩

theorem execute_rows {I a p pos B l22 c} (e : Core a p pos B l22 c) (xs : List Row)
    (w : Nat) (m : MachineState) (v : Model) (tr : Track a m p pos B l22 c v)
    (pc : m.pc=wordAddress w) (bound : w+xs.length<2^40) (code : InstrsAt I w (xs.map op))
    (checked : valid (pos%4) p v xs=true) :
    ∃ t, RunsBlock I m t xs.length ∧ t.pc=wordAddress (w+xs.length) ∧ Track a t p pos B l22 c (xs.foldl advance v) := by
  induction xs generalizing w m v with
  | nil => exact ⟨m,zero_run I m,pc,tr⟩
  | cons r rs ih =>
    simp only [valid,Bool.and_eq_true,decide_eq_true_eq] at checked
    obtain ⟨ready,next⟩:=progress e tr r checked.1
    obtain ⟨one,pc1⟩:=step_one r m w (by omega) pc (by simpa using code ⟨0,by simp⟩) ready
    have rest : InstrsAt I (w+1) (rs.map op) := by
      intro i;simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using code ⟨i.val+1,by simpa using i.isLt⟩
    obtain ⟨t,ran,pcT,frame⟩:=ih (w+1) _ _ next pc1 (by simp only [List.length_cons] at bound;omega) rest checked.2
    refine ⟨t,by simpa only [List.length_cons,Nat.add_comm 1] using join_run one ran,?_,frame⟩
    simpa only [List.length_cons,show w+1+rs.length=w+(rs.length+1) by omega] using pcT

private theorem byte_frame {s t : MachineState} (p B a : Nat) (alg : B%8=0) (fit : a<2^64)
    (outside : a<B ∨ B+stride p≤a)
    (frame : ∀ q : Word, q.toNat<B ∨ B+stride p≤q.toNat → t.getMem q=s.getMem q) :
    t.getByte (addr a)=s.getByte (addr a) := by
  have width : stride p%8=0 := by unfold stride;split <;> decide
  let base:=8*(a/8)
  have e : base+a%8=a := by dsimp [base];omega
  have n : (addr base).toNat=base := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by dsimp [base];omega)]
  have outside' : base<B ∨ B+stride p≤base := by dsimp [base];omega
  have same:=frame (addr base) (by rw [n];exact outside')
  have atByte (m : MachineState) := aligned_byte' m base (a%8) (by dsimp [base];omega) (by omega)
  have lhs:=atByte t;have rhs:=atByte s
  rw [e] at lhs rhs
  exact lhs.trans ((congrArg (fun x=>extractByte x (a%8)) same).trans rhs.symm)

attribute [local irreducible] rows expected symStream streamRun writerDwords writerCarry

private theorem carry_value (s : MachineState) (pos l22 : Nat) (c : Word) (p : Nat) :
    denote s pos l22 c (symStream p).1=writerCarry p (recordSource s l22 pos) c := by
  have h:=congrArg (fun q : Word × Nat × List Word=>q.1) (eval_stream s pos l22 c p)
  dsimp only [mapStream] at h
  unfold writerCarry
  exact h

/-- A straight-line V2a phase, independent of its enclosing loop and every other code address. -/
theorem phase_facts {I p} (code : ImageAt I p) : Layout2Phase2.PhaseFacts I p := by
  intro s pos B l22 c e
  let q:=pos%4
  have qfit : q<4 := Nat.mod_lt _ (by decide)
  obtain ⟨good,len,carry,nodeR,stored⟩:=program_facts p q e.phase qfit
  obtain ⟨atHead,atRows⟩:=split_code (decoded code e.phase qfit len)
  obtain ⟨a,headRun,start,mem,keep,ctx⟩:=start_head e atHead
  have range : Layout2Phase2.bodyWord p+Layout2Phase2.bodyLen p<2^40 := by
    unfold Layout2Phase2.bodyWord Layout2Phase2.bodyLen;split_ifs <;> decide
  obtain ⟨t,ran,pcT,h⟩:=execute_rows ctx (rows p q) (Layout2Phase2.bodyWord p+4) a start2
    (begin_track ctx) start (by omega) atRows good
  change Track a t p pos B l22 c (finalModel p q) at h
  have agree : recordSource a l22 pos=recordSource s l22 pos := by
    funext k;simp only [recordSource,MachineState.getByte,MachineState.getMem,mem]
  have aligned:=e.aligned
  have wid : stride p%8=0 := by unfold stride;split <;> decide
  have minimum : 528≤stride p := by unfold stride;split <;> decide
  refine ⟨t,len ▸ join_run headRun ran,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [pcT];unfold Layout2Phase2.tailWord;congr 1;omega
  · intro j inside hit
    let i:=j/8
    have cell : 8*i+8≤stride p := by dsimp [i];omega
    have bytes:=aligned_byte' t (B+8*i) (j%8) (by omega) (by omega)
    rw [show B+8*i+j%8=B+j by dsimp [i];omega] at bytes
    rw [bytes,h.block i cell,stored ⟨i,by omega⟩,if_pos hit]
    let d:=Layout2Phase2.v1Dword i
    change extractByte (denote a pos l22 c ((expected p).getD d (.data 0))) (j%8)=_
    rw [extract_eq,Layout2Phase2.writtenByte,←agree,←eval_expected a pos l22 c p]
    have length:=writer_dwords_length p (recordSource a l22 pos) c e.phase
    rw [←eval_expected a pos l22 c p,List.length_map] at length
    have isLt : d<(expected p).length := by dsimp [d,Layout2Phase2.v1Dword];split_ifs <;> omega
    change _=(((expected p).map (denote a pos l22 c)).getD d 0).extractLsb' _ _
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem isLt,Option.map_some,Option.getD_some]
  · have v:=h.reg .c;rw [carry] at v
    exact v.trans ((carry_value a pos l22 c p).trans (congrArg (fun src=>writerCarry p src c) agree))
  · have v:=h.reg .n;rw [nodeR] at v
    refine v.trans (congrArg addr ?_);unfold node;rw [Nat.shiftRight_eq_div_pow];omega
  · intro r b d f g i j;let free : Free r := ⟨b,d,f,g,i,j⟩;exact (h.fixed r free).trans (keep r free)
  · intro x fit away
    by_cases inside : B≤x ∧ x<B+stride p
    · let j:=x-B
      let i:=j/8
      have hit : Layout2Phase2.written q i=false := by
        apply Bool.eq_false_iff.mpr;intro yes;exact away ⟨inside.1,inside.2,yes⟩
      have cell : 8*i+8≤stride p := by dsimp [i,j];omega
      have line:=h.block i cell
      rw [stored ⟨i,by omega⟩,if_neg (by simp [hit])] at line
      change t.getMem (addr (B+8*i))=a.getMem (addr (B+8*i)) at line
      have lane := fun (u : MachineState)=>aligned_byte' u (B+8*i) (j%8) (by omega) (by omega)
      have out:=lane t;have src:=lane a
      rw [show B+8*i+j%8=x by dsimp [i,j];omega] at out src
      exact out.trans ((congrArg (fun z=>extractByte z (j%8)) line).trans (src.symm.trans (by simp only [MachineState.getByte,MachineState.getMem,mem])))
    · exact (byte_frame p B x aligned fit (by omega) h.frame).trans (by simp only [MachineState.getByte,MachineState.getMem,mem])
  · intro w away;exact (h.frame w away).trans (by simp only [MachineState.getMem,mem])

end CommitGolfCandidate.Layout2Writer2
