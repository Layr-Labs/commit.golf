import CommitGolfCandidate.GroupOpenPass
import CommitGolfCandidate.GroupedInvariant
import CommitGolfCandidate.GroupOpenModel

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open CommitGolfCandidate.Permutation.CounterSalt (coord salts)
open TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Grouped (groupReply rank)
set_option maxRecDepth 18000
set_option maxHeartbeats 1400000

theorem input_for (s : MachineState) (i : Index) (ord left : Nat) (r : Input s i ord left)
    (k : BitVec 192) (intact : StoredKey s k) :
    packBuffer (window (memoryView (beforeCall s)) 128)=Permutation.CounterSalt.input (coord i).1 k := by
  rw [←Grouped.reply_pack (Permutation.CounterSalt.input (coord i).1 k)]
  apply congrArg packBuffer;funext j
  have mem := (before_regs s i ord left r).2.2.2.2
  have atWord : memoryView (beforeCall s) (128+j.val)=
      writeWord (memoryView s) 128 (ctrAt i) (128+j.val) := by
    change (beforeCall s).mem _=_
    rw [mem]
    exact memory_at_store (address:=128) (index:=128+j.val) (by decide) (by have := j.isLt;omega)
  rw [Grouped.input_word]
  change memoryView (beforeCall s) (128+j.val)=_
  rw [atWord];by_cases zero : j.val=0
  · simp [writeWord,zero,ctrAt]
  · simp only [writeWord,show 128+j.val≠128 by omega,zero,ite_false];exact intact j.val (by omega) j.isLt

def answerFor (o : Oracle) (k : BitVec 192) (i : Index) : BitVec 1600 := groupReply o k i

def fixedPass (o : Oracle) (p : Positions) (k : BitVec 192) : Nat → Nat → MachineState → MachineState
  | 0,_,s=>s
  | n+1,j,s=>fixedPass o p k n (j+1) (finishOne s (pos p j) (p.card-j) (answerFor o k (pos p j)))

theorem pass_fixed (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (k : BitVec 192)
    (s : MachineState) (j n : Nat) (bound : j+n≤p.card) (r : Ready td p k s j) :
    o.run (passTrace p n j s)=pure (fixedPass o p k n j s,n) := by
  induction n generalizing j s with
  | zero => exact oracle_run_pure ..
  | succ n ih =>
    let i:=pos p j
    have hit:=input_for s i j _ (input_of_ready _ _ _ _ _ r (by omega)) k r.keyFrame
    have one : o.run (perTrace s i (p.card-j))=pure (finishOne s i (p.card-j) (answerFor o k i),1) := by
      rw [perTrace,oracle_run_public_bind,hit];simp [answerFor,groupReply,Oracle.answer,oracle_run_pure];rfl
    rw [passTrace,oracle_run_bind,one,pure_bind];dsimp only
    have recursiveRun := ih (finishOne s i (p.card-j) (answerFor o k i)) (j+1) (by omega)
      (next_ready td p k s j r (by omega) (answerFor o k i))
    rw [recursiveRun]
    simp [fixedPass,i,Nat.add_comm]

def Seen (o : Oracle) (k : BitVec 192) (p : Positions) (s : MachineState) (n : Nat) :=
  ∀ a<n, ∀ j : Fin 2, let i:=pos p a
    s.getMem (destAt i+BitVec.ofNat 64 (8*j.val))=saltWords (salts o.permutation k i) j

theorem next_seen (o : Oracle) (k : BitVec 192) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions)
    (s : MachineState) (n : Nat) (h : n<p.card) (r : Ready td p k s n) (old : Seen o k p s n) :
    let i:=pos p n
    Seen o k p (finishOne s i (p.card-n) (answerFor o k i)) (n+1) := by
  let i:=pos p n
  have card : p.card≤16777216:=by change p.card≤LENGTH;simpa [Index] using Finset.card_le_univ p
  have input:=input_of_ready _ _ _ _ _ r h
  change Seen o k p (finishOne s i (p.card-n) (answerFor o k i)) (n+1)
  intro a ha j
  let v:=pos p a
  have jh:=j.isLt
  by_cases eq : v=i
  · change (finishOne s i _ _).getMem (destAt v+_)=_
    change (finishOne s i _ _).getMem (destAt v+_)=saltWords (salts o.permutation k v) j
    rw [eq]
    exact (installs_salt s i n _ (by omega) (by omega) input (answerFor o k i) j).trans
      (congrFun (PackedLeaves.Counter.slice_eq (answerFor o k i) (coord i).2) j)
  · have earlier : a<n := by
      by_contra bad
      have h0 : a=n:=by omega
      exact eq (congrArg (pos p) h0)
    have index : v.val≠i.val:=fun z=>eq (Fin.ext z)
    have ix : v.val<16777216:=v.isLt
    let w:=872415748+2*v.val+j.val
    have addr : destAt v+BitVec.ofNat 64 (8*j.val)=wordAddress w := by
      unfold destAt wordAddress w;rw [←BitVec.ofNat_add];congr 1 <;> omega
    have same:=outside_writes s i n (p.card-n) (by omega) (by omega) input (answerFor o k i) w
      (by dsimp [w];omega) (by dsimp [w];omega) (by dsimp [w];constructor <;> omega)
    have last:=old a earlier j
    change (finishOne s i _ _).getMem (destAt v+_)=_
    exact (show (finishOne s i _ _).getMem (destAt v+_)=s.getMem (destAt v+_) by simpa only [addr,memoryView] using same).trans last

theorem seen_pass (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (k : BitVec 192)
    (s : MachineState) (j n : Nat) (b : j+n≤p.card) (r : Ready td p k s j) (seen : Seen o k p s j) :
    Seen o k p (fixedPass o p k n j s) (j+n) := by
  induction n generalizing s j with
  | zero => exact seen
  | succ n ih =>
    simpa only [fixedPass,show j+(n+1)=(j+1)+n by omega] using ih _ (j+1) (by omega)
      (next_ready _ _ _ _ _ r (by omega) _) (next_seen o k td p s j (by omega) r seen)

end TwoPermutationPrototype.GroupedOpening
