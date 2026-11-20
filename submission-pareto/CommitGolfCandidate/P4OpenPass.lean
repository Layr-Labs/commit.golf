import CommitGolfCandidate.P4OpenEffect
import CommitGolfCandidate.TwoPermutationPackedOpeningInitial
import CommitGolfCandidate.TwoPermutationPackedOpeningRecordRun
import CommitGolfCandidate.TwoPermutationPackedOpeningRecords
import CommitGolfCandidate.GroupedInvariant
import CommitGolfCandidate.TwoPermutationHidingHits

/-! P4 opener: the whole prefix pass (one iteration per opened position) as an oracle trace, its exact cost, and its
fixed evaluation under the counter-mode salt oracle. Ported from dadon's 2a19be00 `GroupOpenPass` and
`GroupOpenFixed`; the base registers are 04680e02's record-loop registers. -/

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open Opening (sortedIndex RecordMarks machineMarks groupsBefore OpeningLayout SameOpeningInput trapdoorBase proofBase indicesBase input_index)
open TwoPermutationPrototype.Grouped (rank)
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def pos (p : Positions) (j : Nat) : Index := ((p.sort (·≤·))[j]?).getD ⟨0,by decide⟩
theorem pos_present (p : Positions) (j : Nat) (hj : j<p.card) : pos p j=sortedIndex p j hj := by
  unfold pos sortedIndex;rw [List.getElem?_eq_getElem (by simpa using hj)];rfl

structure Base (s : MachineState) (p : Positions) : Prop where
  indices : s.getReg .x8=BitVec.ofNat 64 indicesBase
  heap : s.getReg .x9=BitVec.ofNat 64 trapdoorBase
  count : s.getReg .x18=BitVec.ofNat 64 p.card
  leaves : s.getReg .x19=16777216
  start : s.getReg .x20=BitVec.ofNat 64 proofBase
  dest : s.getReg .x21=BitVec.ofNat 64 proofBase
  mark : s.getReg .x23=1
  cap : s.getReg .x25=BitVec.ofNat 64 trapdoorBase
  capLeaves : s.getReg .x27=256

def Preserved (u s : MachineState) :=
  ∀ w<2^33, (w<128 ∨ 153≤w) → (w<192 ∨ 217≤w) →
    (w<704643588 ∨ 738198020≤w) → memoryView s w=memoryView u w

def StoredKey (s : MachineState) (k : BitVec 192) :=
  ∀ j, 0<j → j<25 → memoryView s (128+j)=Grouped.keyBlock k j

def passPC (p : Positions) (j : Nat) := if j=p.card then address 13 else address 1467

structure Ready (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (key : BitVec 192)
    (s : MachineState) (j : Nat) : Prop extends Registers s j (p.card-j), Base s p where
  pc : s.pc=passPC p j
  frame : Preserved (actual.initialState .opening (td,p)) s
  keyFrame : StoredKey s key

theorem input_of_ready (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (key : BitVec 192)
    (s : MachineState) (j : Nat) (r : Ready td p key s j) (hj : j<p.card) :
    Input s (pos p j) j (p.card-j) := by
  have card : p.card≤16777216 := by change p.card≤LENGTH;simpa [Index] using Finset.card_le_univ p
  have ea : indexAt j=wordAddress (738198020+j) := by unfold indexAt wordAddress;congr 1 <;> omega
  refine ⟨r.toRegisters,by simpa [passPC,Nat.ne_of_lt hj] using r.pc,?_,?_⟩
  · have same := r.frame (738198020+j) (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
    have orig := input_index actual actual_layout td p j hj
    rw [pos_present p j hj]
    exact (show s.getMem (indexAt j)=(actual.initialState .opening (td,p)).getMem (indexAt j) by
      simpa only [ea,memoryView] using same).trans orig
  · unfold indexAt;apply Opening.aligned_access
    · omega
    · change _≤2^36;omega

theorem next_ready (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (key : BitVec 192)
    (s : MachineState) (j : Nat) (r : Ready td p key s j) (hj : j<p.card) (y : BitVec 1600) :
    Ready td p key (finishOne s (pos p j) (p.card-j) y) (j+1) := by
  let i:=pos p j
  have ix : i.val<16777216:=i.isLt
  have card : p.card≤16777216:=by change p.card≤LENGTH;simpa [Index] using Finset.card_le_univ p
  have inp:=input_of_ready td p key s j r hj
  have ⟨reg,pc,_⟩:=finish_regs s i j _ (by omega) (by omega) inp y
  have keep (a : Reg) (safe : Saved a := by unfold Saved;decide) := finish_keep s i (p.card-j) y a safe
  have same := outside_writes s i j (p.card-j) (by omega) (by omega) inp y
  refine ⟨by simpa only [show p.card-j-1=p.card-(j+1) by omega] using reg,
    ⟨(keep .x8).trans r.indices,(keep .x9).trans r.heap,(keep .x18).trans r.count,
     (keep .x19).trans r.leaves,(keep .x20).trans r.start,(keep .x21).trans r.dest,(keep .x23).trans r.mark,
     (keep .x25).trans r.cap,(keep .x27).trans r.capLeaves⟩,?_,?_,?_⟩
  · rw [pc];unfold finalPC passPC;split <;> rename_i h <;> simp [show j+1=p.card ↔ p.card-j=1 by omega,h]
  · intro w fit one two three
    exact (same w fit ⟨by omega,two⟩ ⟨by omega,by omega⟩).trans (r.frame _ fit one two three)
  · intro k lo hi
    exact (same (128+k) (by omega) ⟨by omega,Or.inl (by omega)⟩ ⟨by omega,by omega⟩).trans (r.keyFrame _ lo hi)

def passTrace (p : Positions) : Nat → Nat → MachineState → OracleComp World MachineState
  | 0,_,s => pure s
  | n+1,j,s => do let t ← perTrace s (pos p j) (p.card-j);passTrace p n (j+1) t

def passSteps (p : Positions) : Nat → Nat → Nat
  | 0,_ => 0
  | n+1,j => perSteps (pos p j) (p.card-j)+passSteps p n (j+1)

theorem step_support (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (key : BitVec 192)
    (s t : MachineState) (j : Nat) (r : Ready td p key s j) (hj : j<p.card)
    (hit : t∈support (perTrace s (pos p j) (p.card-j))) : Ready td p key t (j+1) := by
  simp only [perTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hit
  obtain ⟨y,_,rfl⟩:=hit;exact next_ready td p key s j r hj y

theorem pass_post (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (key : BitVec 192)
    (s t : MachineState) (n j : Nat) (r : Ready td p key s j) (bound : j+n≤p.card)
    (hit : t∈support (passTrace p n j s)) : Ready td p key t (j+n) := by
  induction n generalizing j s with
  | zero => simp only [passTrace,support_pure,Set.mem_singleton_iff] at hit;subst t;exact r
  | succ n ih =>
    rw [passTrace,mem_support_bind_iff] at hit;obtain ⟨u,one,rest⟩:=hit
    exact (show j+(n+1)=(j+1)+n by omega) ▸ ih _ _ (step_support _ _ _ _ _ _ r (by omega) one) (by omega) rest

theorem pass_run (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (key : BitVec 192)
    (s : MachineState) (n j fuel : Nat) (r : Ready td p key s j) (bound : j+n≤p.card) :
    execute openingImage (passSteps p n j+fuel) s true=(do
      let t ← passTrace p n j s;let z ← execute openingImage fuel t true
      return z.charge (passSteps p n j+13*n) n) := by
  induction n generalizing j s with
  | zero => simp [passSteps,passTrace,Execution.charge]
  | succ n ih =>
    have card : p.card≤16777216 := by change p.card≤LENGTH;simpa [Index] using Finset.card_le_univ p
    rw [passSteps,Nat.add_assoc,per_run s (pos p j) j _ _ (by omega) (by omega) (input_of_ready _ _ _ _ _ r (by omega))]
    simp only [passTrace,bind_assoc]
    apply bind_congr_of_forall_mem_support;intro u hit
    rw [ih u (j+1) (step_support _ _ _ _ _ _ r (by omega) hit) (by omega)]
    simp only [bind_assoc,pure_bind]
    apply bind_congr;intro t;apply bind_congr;intro z;apply congrArg (fun x : Execution => (pure x : OracleComp World Execution))
    cases z;simp [Execution.charge,passSteps,perCycles,Nat.mul_succ] <;> omega

theorem pass_steps_bound (p : Positions) (n j : Nat) (bound : j+n≤p.card) : passSteps p n j≤22*n+1 := by
  induction n generalizing j with
  | zero => simp [passSteps]
  | succ n ih =>
    rw [passSteps]
    have h:=ih (j+1) (by omega)
    unfold perSteps
    by_cases last : p.card-j=1
    · have empty : n=0 := by omega
      subst n;simp [last,passSteps];split <;> omega
    · simp only [if_neg last];split <;> omega

end TwoPermutationPrototype.GroupedOpening

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
    let w:=704643588+2*v.val+j.val
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
