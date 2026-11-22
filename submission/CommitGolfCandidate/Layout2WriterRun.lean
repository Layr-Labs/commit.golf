import CommitGolfCandidate.Layout2WriterStep
import CommitGolfCandidate.Layout2WriterProgram
import CommitGolfCandidate.TwoPermutationPackedFetchBase
namespace CommitGolfCandidate.Layout2Writer
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp Layout2Phase
set_option maxRecDepth 12000
set_option maxHeartbeats 1400000

private theorem rows_zero (I : Image) (m : MachineState) : RunsBlock I m m 0 := by
  intro fuel coins; simp [Execution.charge]
private theorem rows_next {I s m t n k} (a : RunsBlock I s m n) (b : RunsBlock I m t k) :
    RunsBlock I s t (n+k) := by
  intro fuel coins;rw [Nat.add_assoc,a,b];simp [bind_assoc,pure_bind,Execution.charge,Nat.add_assoc]
private theorem pc4 (w : Nat) : wordAddress w+4=wordAddress (w+1) := by
  unfold wordAddress;change addr _+addr 4=_
  rw [←BitVec.ofNat_add];congr 1 <;> omega

private theorem unit_step {I : Image} (r : Row) (m : MachineState) (w : Nat) (small : w<2^40)
    (pc : m.pc=wordAddress w) (code : (I.code[w]?).bind decodeInstruction=some (.base (instruction r)))
    (valid : memoryArgumentsValid m (instruction r)=true) :
    RunsBlock I m (execInstrBr m (instruction r)) 1 ∧ (execInstrBr m (instruction r)).pc=wordAddress (w+1) := by
  have fetch:=wide_image_fetch I m w (instruction r) small pc code
  have step : ordinaryStep m (.base (instruction r))=some (execInstrBr m (instruction r)) := by
    cases r <;> simp only [instruction] at valid ⊢ <;> simp only [ordinaryStep,valid,ite_true]
  have cycle : instructionCycles (.base (instruction r))=1 := by cases r <;> rfl
  have moved : (execInstrBr m (instruction r)).pc=m.pc+4 := by cases r <;> rfl
  refine ⟨?_,by rw [moved,pc,pc4]⟩
  intro fuel coins
  rw [Nat.add_comm 1 fuel,execute_ordinary_step _ _ _ _ _ _ fetch step,cycle]

private theorem run_checked {I s p pos B l22 c} (e : PhaseEntry s p pos B l22 c) (xs : List Row)
    (w : Nat) (m : MachineState) (v : Model) (tr : Track s m p pos B l22 c v)
    (pc : m.pc=wordAddress w) (bound : w+xs.length<2^40) (code : CodeAt I w xs) (valid : checked p v xs=true) :
    ∃ t, RunsBlock I m t xs.length ∧ t.pc=wordAddress (w+xs.length) ∧ Track s t p pos B l22 c (xs.foldl advance v) := by
  induction xs generalizing w m v with
  | nil => exact ⟨m,rows_zero I m,pc,tr⟩
  | cons r rs ih =>
    simp only [checked,Bool.and_eq_true,decide_eq_true_eq] at valid
    obtain ⟨ready,next⟩:=progress e tr r valid.1
    obtain ⟨one,pc1⟩:=unit_step r m w (by omega) pc (by simpa using code ⟨0,by simp⟩) ready
    have rest : CodeAt I (w+1) rs := by
      intro i;simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using code ⟨i.val+1,by simpa using i.isLt⟩
    obtain ⟨t,ran,pcT,frame⟩:=ih (w+1) _ _ next pc1 (by simp only [List.length_cons] at bound;omega) rest valid.2
    refine ⟨t,by simpa only [List.length_cons,Nat.add_comm 1] using rows_next one ran,?_,frame⟩
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

attribute [local irreducible] program expected symStream streamRun writerDwords writerCarry

private theorem carry_value (s : MachineState) (pos l22 : Nat) (c : Word) (p : Nat) :
    denote s pos l22 c (symStream p).1=writerCarry p (recordSource s l22 pos) c := by
  have h:=congrArg (fun q : Word × Nat × List Word=>q.1) (eval_stream s pos l22 c p)
  dsimp only [mapStream] at h
  unfold writerCarry
  exact h

/-- Each phase depends on just its own fetched words. The surrounding loop, checker and cap
may be linked independently. All 560 source bytes and the incoming carry are arbitrary. -/
theorem phase_facts {I p} (code : BodyAt I p) : PhaseFacts I p := by
  intro s pos B l22 c e
  obtain ⟨ok,len,carry,nodeR,stored⟩:=program_valid p e.phase
  have room : bodyWord p+bodyLen p<2^40 := by unfold bodyWord bodyLen;split_ifs <;> decide
  obtain ⟨t,ran,pcT,h⟩:= run_checked e (program p) (bodyWord p) s initial (entry_track e) e.pc
    (by rwa [len]) (body_decoded code) ok
  change Track s t p pos B l22 c (result p) at h
  refine ⟨t,len ▸ ran,by simpa only [tailWord,len] using pcT,?_,?_,?_,?_,?_,h.frame⟩
  · intro j inside
    let i:=j/8
    have alg:=e.aligned
    have wid : stride p%8=0 := by unfold stride;split <;> decide
    have cell : 8*i+8≤stride p := by dsimp [i];omega
    have bytes:=aligned_byte' t (B+8*i) (j%8) (by omega) (by omega)
    rw [show B+8*i+j%8=B+j by dsimp [i];omega] at bytes
    rw [bytes,h.block i cell,stored ⟨i,by omega⟩]
    change extractByte (denote s pos l22 c ((expected p).getD i (.data 0))) (j%8)=_
    rw [extract_eq,writerByte,←eval_expected s pos l22 c p]
    have length:=writer_dwords_length p (recordSource s l22 pos) c e.phase
    rw [←eval_expected s pos l22 c p,List.length_map] at length
    have isLt : i<(expected p).length := by omega
    simp only [i,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem isLt,Option.map_some,Option.getD_some]
  · have v:=h.reg .c;rw [carry] at v
    exact v.trans (carry_value s pos l22 c p)
  · have v:=h.reg .n;rw [nodeR] at v
    refine v.trans (congrArg addr ?_)
    unfold node;rw [Nat.shiftRight_eq_div_pow]; omega
  · intro r a b d f g k;exact h.fixed r ⟨a,b,d,f,g,k⟩
  · intro a fit away;exact byte_frame p B a e.aligned fit away h.frame

end CommitGolfCandidate.Layout2Writer
