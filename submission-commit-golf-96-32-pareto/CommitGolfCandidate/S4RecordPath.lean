import CommitGolfCandidate.S4NodeRun
import CommitGolfCandidate.S4NodeSites
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt)
theorem InputsStill.scratch {i : CheckInput} {s t : MachineState} (old : InputsStill i s) (within : SameOutside s t 256 352) :
    InputsStill i t:=fun q l h=>(within q h (Or.inr (by omega))).trans (old q l h)

private theorem viewAt (x : CheckInput) (r h : Nat) (b : Bool) (choice : b=decide (x.positions.card=BATCH))
    (level : h<pathLevels b) (s : MachineState) (f : InputsStill x s) (br : r<x.positions.card) :
    peersBefore s (siblingPtr b r h) (nodeLength b h) h=(readView x).peers r h := by
  have count : x.positions.card≤LENGTH:=by simpa using Finset.card_le_univ x.positions
  change x.positions.card≤16777216 at count
  have sz:=(nodeSize b h level).2.2.2.2
  have max : recordBytes b≤824:=by cases b <;> decide
  have hi : siblingPtr b r h+nodeLength b h+otherSize h≤MEMORY_BYTES:=by
    unfold siblingPtr proofBase MEMORY_BYTES otherSize;cases b <;> simp only [recordBytes,ite_true,ite_false,Bool.false_eq_true] at *
    all_goals omega
  have lo : 32768≤siblingPtr b r h:=by unfold siblingPtr proofBase;omega
  have part (n : Nat) (k : Nat) (len : k+n≤nodeLength b h+otherSize h) :
      readBuffer s (siblingPtr b r h+k) n=proofAt x (r*recordBytes b+fieldOffset b h+k) n:=by
    rw [f.read _ _ (by omega) (by unfold MEMORY_BYTES at hi;omega)]
    unfold proofAt initial siblingPtr
    apply congrArg (fun a=>readBuffer (Late.submission.initialState .check x) a n)
    change proofBase+recordBytes b*r+fieldOffset b h+k=proofBase+(r*recordBytes b+fieldOffset b h+k)
    rw [Nat.mul_comm (recordBytes b) r];omega
  have first :=part (nodeLength b h) 0 (by omega)
  simp only [Nat.add_zero] at first
  apply Prod.ext
  · subst b;exact congrArg (BitVec.setWidth 256) first
  · by_cases zero : h=0
    · subst h
      have full : nodeLength b 0=32:=by cases b <;> decide
      have two:=part 32 32 (by rw [full];decide)
      simp only [peersBefore,readView,←choice,ite_true,full];exact two
    · simp only [peersBefore,readView,if_neg zero]

structure PathState (o : Oracle) (x : CheckInput) (b : Bool) (r k : Nat) (s t : MachineState) : Prop where
  run : CheckRuns o s t (pathPrice b k) k
  pc : t.pc=pcAt (nodePC b k)
  index : t.getReg .x20=W (nodeIndex ((readView x).idx r).val k)
  cursor : t.getReg .x18=W (siblingPtr b r k)
  keep : ∀ reg,pathKeep reg → t.getReg reg=s.getReg reg
  frame : SameOutside s t 256 352
  digest : readBuffer t 256 32=recordAt .packed o.compression (readView x) r k ((readView x).peers r)

private theorem nextHash (o : Oracle) (v : View) (r k : Nat) :
    recordAt .packed o.compression v r (k+1) (v.peers r)=retained .packed (k+1) (o.compression
      (payload (lane k (nodeIndex (v.idx r).val k)) (recordAt .packed o.compression v r k (v.peers r)) (v.peers r k))) := rfl
set_option maxRecDepth 5000 in
theorem recordPath (o : Oracle) (x : CheckInput) (b : Bool) (r k : Nat) (s : MachineState) (br : r<x.positions.card)
    (choice : b=decide (x.positions.card=BATCH)) (bound : k≤pathLevels b) (pc : s.pc=pcAt (firstNode b))
    (index : s.getReg .x20=W ((readView x).idx r).val) (ptr : s.getReg .x18=W (siblingPtr b r 0))
    (leaf : readBuffer s 256 32=Late.leaf o.compression (((readView x).idx r).val.testBit 0) ((readView x).salt r) ((readView x).entry r))
    (env : Env x s) : ∃ t,PathState o x b r k s t := by
  induction k with
  | zero=>
    refine ⟨s,⟨CheckRuns.refl o s,
      pc,?_,ptr,fun _ _=>rfl,fun _ _ _=>rfl,leaf⟩⟩
    simpa only [nodeIndex,span,Nat.div_one] using index
  | succ k ih=>
    have level : k<pathLevels b:=by omega
    obtain ⟨u,st⟩:=ih (by omega)
    let i:=(readView x).idx r
    let src:=siblingPtr b r k
    have sz:=nodeSize b k level
    have room : nodePC b k+(nodeCode b k).length≤Code.check.count:=sz.2.2.2.1
    have small : nodeIndex i.val k<2^64:=lt_of_le_of_lt (Nat.div_le_self ..) (by have h:=i.isLt;change i.val<16777216 at h;omega)
    have cap : x.positions.card≤LENGTH:=by simpa using Finset.card_le_univ x.positions
    change x.positions.card≤16777216 at cap
    have hi : src+nodeLength b k+otherSize k≤MEMORY_BYTES:=by
      have limit:=sz.2.2.2.2;have max : recordBytes b≤824:=by cases b <;> decide
      dsimp only [src,siblingPtr,proofBase,otherSize];unfold MEMORY_BYTES
      cases b <;> simp only [recordBytes,ite_true,ite_false,Bool.false_eq_true] at * <;> omega
    have low : 32768≤src:=by dsimp only [src,siblingPtr,proofBase];omega
    have members:=env.data.scratch st.frame
    obtain ⟨v,node⟩:=nodeRun o u b k (nodeIndex i.val k) src (nodePC b k) level rfl st.pc room (nodeSite b k level)
      st.index small st.cursor low hi ((st.keep _ (by decide)).trans env.mode) ((st.keep _ (by decide)).trans env.kind)
      ((st.keep _ (by decide)).trans env.width) ((st.keep _ (by decide)).trans env.three)
    have peers:=viewAt x r k b choice level u members br
    refine ⟨v,⟨st.run.trans node.run,node.next,?_,?_,fun reg hr=>(node.keep reg hr).trans (st.keep reg hr),
      bothScratch st.frame node.frame,?_⟩⟩
    · rw [nextIndex];exact node.idx
    · apply node.nextProof.trans;apply congrArg W
      have increment:=sz.2.1
      dsimp only [src,siblingPtr,otherSize];omega
    · rw [nextHash]
      apply node.digest.trans
      have eqv : peersBefore u src (nodeLength b k) k=(readView x).peers r k:=peers
      rw [st.digest,eqv]
end CommitGolfCandidate.S4.Machine
