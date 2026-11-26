import CommitGolfCandidate.R4bFields
set_option Elab.async false
namespace CommitGolfCandidate.R4b
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open CommitGolfCandidate.S4
open Open (Sources Marked)
open Machine (W Runs proofBase indexBase byte Wrote Safe)
open Late (pcAt)
structure Frame (td : Late.Trapdoor) (ps : Positions) (t l : Nat) (s : MachineState) : Prop where
  consts : Agree (fixed t) s
  out : s.getReg .x19=W (proofBase+2040*t)
  count : s.getReg .x9=W (32-t)
  flagBase : s.getReg .x24=512
  one : s.getReg .x25=1
  buffer : s.getReg .x15=W proofBase
  sources : Sources td ps s
  table : TableMem s
  flags : Marked ps (4*t+l) s
  cursor : Cursor (tape td ps) (510*(4*t+l)) s

private theorem finalMark (s : MachineState) (i : Index) (ix : s.getReg .x28=W (i.val/3/128))
    (fb : s.getReg .x24=512) (one : s.getReg .x25=1) :
    let n:=nodeIndex i.val 15
    ∃ z,Straight s markCode z ∧ Kept s z ∧ z.getReg .x20=s.getReg .x20 ∧
      Wrote s z (512+n) 1 (fun _=>1) := by
  let n:=nodeIndex i.val 15
  let u:=alu s .x8 (W n)
  have a:=shiftR s .x8 .x28 7 (by decide)
  have ixBound : i.val<16777216:=i.isLt
  rw [ix,Machine.shr _ _ (by omega),show i.val/3/128/2^7=n by dsimp [n,nodeIndex,span];omega] at a
  let v:=alu u .x6 (W (512+n))
  have bu : u.getReg .x24=W 512:=(aluKeep _ _ _ _ (by decide)).trans fb
  have b : Straight u [.ADD .x6 .x24 .x8] v:=by
    apply Straight.one _ rfl
    change some (alu u .x6 (u.getReg .x24+u.getReg .x8))=some v
    rw [bu,show u.getReg .x8=W n from aluGet _ _ _ (by decide),←BitVec.ofNat_add]
  have addr : v.getReg .x6+signExtend12 0=W (512+n):=by
    rw [show v.getReg .x6=W (512+n) from aluGet _ _ _ (by decide)];exact BitVec.add_zero _
  have value : v.getReg .x25=1:=(aluKeep _ _ _ _ (by decide)).trans ((aluKeep _ _ _ _ (by decide)).trans one)
  let w:=execInstrBr v (.SB .x6 .x25 0)
  have limit : n<342:=by dsimp [n,nodeIndex,span];omega
  have valid : memoryArgumentsValid v (.SB .x6 .x25 0)=true:=by
    change accessValid _ 1=true;rw [addr];apply Safe.valid;exact ⟨by change 512+n+1≤68719476736;omega,Nat.mod_one _⟩
  have c : Straight v [.SB .x6 .x25 0] w:=.one (by simp only [ordinaryStep,if_pos valid];rfl) rfl
  have kept (k : Reg) (a : k≠.x8) (b : k≠.x6) : w.getReg k=s.getReg k:=
    (show w.getReg k=v.getReg k by cases k <;> rfl).trans ((aluKeep u .x6 _ k b.symm).trans (aluKeep s .x8 _ k a.symm))
  refine ⟨w,(a.append b).append c,fun k h=>kept k (by intro e;subst k;contradiction) (by intro e;subst k;contradiction),
    kept _ (by decide) (by decide),?_⟩
  have store:=Machine.storedFlag v (512+n) (1 : Byte) (by omega)
  have equal : w.mem=(v.setByte (W (512+n)) 1).mem:=by simp only [w,execInstrBr,addr,value];rfl
  have eqv:=store.mem equal
  intro q h
  exact (eqv q h).trans (by rfl)

theorem recordRun (td : Late.Trapdoor) (ps : Positions) (batch : ps.card=128) (t l : Nat) (bt : t<32) (bl : l<4)
    (s : MachineState) (f : Frame td ps t l s) :
    ∃ z,Straight s (rowCode l) z ∧ Frame td ps t (l+1) z := by
  let r:=4*t+l
  let i:=recordIndex ps r
  have inside : r<ps.card:=by dsimp [r];omega
  obtain ⟨u,body,frame,keep,loc,bytes⟩:=fieldsRun td ps batch t l bt bl s f.sources f.table f.consts f.out f.cursor 17 le_rfl
  have carry : u.getReg .x28=W (i.val/3/128):=loc _ _ rfl
  obtain ⟨z,mark,kept,carryWord,wr⟩:=finalMark u i carry ((keep _ rfl).trans f.flagBase) ((keep _ rfl).trans f.one)
  have pres:=keep.trans kept
  have nodeLim : nodeIndex i.val 15<342:=by have h:=i.isLt;change i.val<16777216 at h;change i.val/49152<342;omega
  have away (q : Nat) (above : 1024≤q) (h : q<2^64) : byte z q=byte u q:=(wr q h).trans (if_neg (by omega))
  have ss:=frame.sources f.sources
  have ts:=frame.table f.table
  refine ⟨z,body.append mark,⟨pres.fixed f.consts,(pres _ rfl).trans f.out,(pres _ rfl).trans f.count,
    (pres _ rfl).trans f.flagBase,(pres _ rfl).trans f.one,(pres _ rfl).trans f.buffer,?_,?_,?_,?_⟩⟩
  · intro q lo hi;exact (away q (by unfold Open.tdBase at lo;omega) (by unfold Machine.valueBase at hi;omega)).trans (ss q lo hi)
  · apply tableOfBytes ts;intro q lo hi;exact away q (by unfold tableBase at lo;omega) (by unfold tableBase at hi;omega)
  · exact Open.markChanged inside (protectMarks frame f.flags) wr
  · have eq : 510*(4*t+l)+Open.offsetAt true 17=510*(4*t+(l+1)):=by change 510*(4*t+l)+510=_;omega
    rw [eq] at bytes
    refine ⟨fun j hj=> (away _ (by unfold proofBase;omega) (by unfold completed proofBase at *;omega)).trans (bytes.filled j hj),
      fun nz j hj=> by rw [carryWord];exact bytes.pending nz j hj⟩

theorem tileRun (td : Late.Trapdoor) (ps : Positions) (batch : ps.card=128) (t : Nat) (bt : t<32)
    (s : MachineState) (f : Frame td ps t 0 s) :
    ∃ z,Straight s tileCode z ∧ Frame td ps t 4 z := by
  have ind (l : Nat) (le : l≤4) : ∃ u,Straight s ((List.range l).flatMap rowCode) u ∧ Frame td ps t l u := by
    induction l with
    | zero=>exact ⟨s,.nil _,f⟩
    | succ l ih=>
      obtain ⟨u,pre,frame⟩:=ih (by omega)
      obtain ⟨z,last,done⟩:=recordRun td ps batch t l bt (by omega) u frame
      exact ⟨z,by simpa only [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil] using pre.append last,done⟩
  exact ind 4 le_rfl
end CommitGolfCandidate.R4b
