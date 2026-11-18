import CommitGolfCandidate.GroupOpenEffect
import CommitGolfCandidate.GroupOpenLatch
import CommitGolfCandidate.GroupOpenInitial
import CommitGolfCandidate.GroupOpenRecordRun
import CommitGolfCandidate.GroupOpenRecords

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open Opening (sortedIndex RecordMarks machineMarks groupsBefore)
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def pos (p : Positions) (j : Nat) : Index := ((p.sort (·≤·))[j]?).getD ⟨0,by decide⟩
theorem pos_present (p : Positions) (j : Nat) (hj : j<p.card) : pos p j=sortedIndex p j hj := by
  unfold pos sortedIndex;rw [List.getElem?_eq_getElem (by simpa using hj)];rfl

structure Base (s : MachineState) (p : Positions) : Prop where
  indices : s.getReg .x8=BitVec.ofNat 64 indicesBase
  heap : s.getReg .x9=BitVec.ofNat 64 trapdoorBase
  count : s.getReg .x18=BitVec.ofNat 64 p.card
  leaves : s.getReg .x19=4194304
  start : s.getReg .x20=BitVec.ofNat 64 proofBase
  dest : s.getReg .x21=BitVec.ofNat 64 proofBase
  mark : s.getReg .x23=1
  slots : s.getReg .x24=BitVec.ofNat 64 groupSlots
  cap : s.getReg .x25=BitVec.ofNat 64 trapdoorBase
  capLeaves : s.getReg .x27=256

/-- The previous position's quartet (`x4`); none before the first position. -/
def lastOf (p : Positions) (j : Nat) : Nat := if j=0 then 2^64-1 else (pos p (j-1)).val/4
/-- Quartets below this one may have had their blocks rebuilt (sorted positions). -/
def topOf (p : Positions) (j : Nat) : Nat := if j=0 then 0 else (pos p (j-1)).val/4+1

theorem pos_lt (p : Positions) (a b : Nat) (ab : a<b) (hb : b<p.card) : (pos p a).val<(pos p b).val := by
  have ha : a<p.card := by omega
  rw [pos_present p a ha,pos_present p b hb]
  unfold sortedIndex
  have s := (Finset.sortedLT_sort p).pairwise
  have := List.pairwise_iff_getElem.mp s a b (by simpa using ha) (by simpa using hb) ab
  exact this

theorem top_succ (p : Positions) (j : Nat) : topOf p (j+1)=(pos p j).val/4+1 := by simp [topOf]

theorem top_le (p : Positions) (j : Nat) : topOf p j≤4194304 := by
  unfold topOf; split
  · omega
  · have := (pos p (j-1)).isLt; change _<16777216 at this; omega

theorem top_mono (p : Positions) (j : Nat) (hj : j<p.card) : topOf p j≤topOf p (j+1) := by
  rw [top_succ]
  by_cases z : j=0
  · simp [topOf,z]
  · have e : topOf p j=(pos p (j-1)).val/4+1 := by simp [topOf,z]
    have := pos_lt p (j-1) j (by omega) hj
    have : (pos p (j-1)).val/4≤(pos p j).val/4 := Nat.div_le_div_right (by omega)
    omega

theorem last_lt_top (p : Positions) (j : Nat) (hj : j<p.card) (fresh : (pos p j).val/4≠lastOf p j) :
    topOf p j≤(pos p j).val/4 := by
  unfold topOf lastOf at *
  by_cases z : j=0
  · simp [z]
  · simp only [z,ite_false] at fresh ⊢
    have := pos_lt p (j-1) j (by omega) hj
    have : (pos p (j-1)).val/4≤(pos p j).val/4 := Nat.div_le_div_right (by omega)
    omega

/-- Words the pass may have changed before ordinal `j`: the generator block, the reply scratch, the level-22
heap slots, the salt table and the rebuilt blocks of the quartets below `topOf p j`. -/
def Touched (p : Positions) (j : Nat) (w : Nat) : Prop :=
  (128≤w ∧ w<153) ∨ (192≤w ∧ w<217) ∨ (553648644≤w ∧ w<570425860) ∨ (1140851204≤w ∧ w<1174405636) ∨
    (∃ q, q<topOf p j ∧ ∃ m<25, w=rebuiltWord q+m)

def Preserved (p : Positions) (j : Nat) (u s : MachineState) :=
  ∀ w<2^33, ¬Touched p j w → memoryView s w=memoryView u w

theorem touched_mono (p : Positions) (j : Nat) (hj : j<p.card) (w : Nat) (t : Touched p j w) : Touched p (j+1) w := by
  rcases t with h|h|h|h|⟨q,hq,m,hm,rfl⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨q,by have := top_mono p j hj;omega,m,hm,rfl⟩)))

theorem writes_touched (p : Positions) (j : Nat) (hj : j<p.card) (w : Nat) (wr : Writes (pos p j) (lastOf p j) w) :
    Touched p (j+1) w := by
  have ix := (pos p j).isLt
  have top : topOf p (j+1)=(pos p j).val/4+1 := by simp [topOf]
  rcases wr with ⟨_,⟨m,hm,rfl⟩|⟨m,hm,rfl⟩⟩|h|h|h|h
  · have x := xor_one_lt ((pos p j).val/4) 22 (by change _<16777216 at ix;omega) (by decide)
    right;right;left;unfold heapWord;constructor <;> omega
  · right;right;right;right;exact ⟨_,by omega,m,hm,rfl⟩
  · left;omega
  · right;left;exact h
  · right;right;right;left;change _<16777216 at ix;omega
  · right;right;right;left;change _<16777216 at ix;omega

def passPC (p : Positions) (j : Nat) := if j=p.card then address 15 else address 740

structure Ready (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (key : BitVec 192)
    (s : MachineState) (j : Nat) : Prop extends Registers s j (p.card-j), Base s p where
  pc : s.pc=passPC p j
  quartet : s.getReg .x4=BitVec.ofNat 64 (lastOf p j)
  frame : Preserved p j (actual.initialState .opening (td,p)) s
  keyFrame : KeyWords s key

theorem last_small (p : Positions) (j : Nat) : lastOf p j<2^64 := by
  unfold lastOf; split
  · decide
  · have := (pos p (j-1)).isLt; change _<16777216 at this; omega

theorem input_of_ready (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (key : BitVec 192)
    (s : MachineState) (j : Nat) (r : Ready td p key s j) (hj : j<p.card) :
    Input s (pos p j) j (p.card-j) (lastOf p j) := by
  have card : p.card≤16777216 := by change p.card≤LENGTH;simpa [Index] using Finset.card_le_univ p
  have ea : indexAt j=wordAddress (1174405636+j) := by unfold indexAt wordAddress;congr 1 <;> omega
  refine ⟨r.toRegisters,by simpa [passPC,Nat.ne_of_lt hj] using r.pc,r.mark,r.heap,r.leaves,r.slots,r.quartet,
    last_small p j,?_,?_⟩
  · have same := r.frame (1174405636+j) (by omega) (by
      rintro (h|h|h|h|⟨q,hq,m,hm,e⟩)
      all_goals (try omega)
      unfold rebuiltWord blockWord at e; have := top_le p j; omega)
    have orig := input_index actual actual_layout td p j hj
    rw [pos_present p j hj]
    exact (show s.getMem (indexAt j)=(actual.initialState .opening (td,p)).getMem (indexAt j) by
      simpa only [ea,memoryView] using same).trans orig
  · unfold indexAt;apply Opening.aligned_access
    · omega
    · change _≤2^36;omega

theorem next_ready (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (key : BitVec 192)
    (s t : MachineState) (j : Nat) (r : Ready td p key s j) (hj : j<p.card)
    (hit : t∈support (perTrace s (pos p j) (p.card-j) (lastOf p j))) : Ready td p key t (j+1) := by
  let i:=pos p j
  have card : p.card≤16777216:=by change p.card≤LENGTH;simpa [Index] using Finset.card_le_univ p
  have inp:=input_of_ready td p key s j r hj
  obtain ⟨reg,pc,q4,keep,same⟩:=trace_post s i j _ _ (by omega) (by omega) inp t hit
  have kp (a : Reg) (safe : Saved a := by unfold Saved;decide) := keep a safe
  refine ⟨by simpa only [show p.card-j-1=p.card-(j+1) by omega] using reg,
    ⟨(kp .x8).trans r.indices,(kp .x9).trans r.heap,(kp .x18).trans r.count,
     (kp .x19).trans r.leaves,(kp .x20).trans r.start,(kp .x21).trans r.dest,(kp .x23).trans r.mark,
     (kp .x24).trans r.slots,(kp .x25).trans r.cap,(kp .x27).trans r.capLeaves⟩,?_,?_,?_,?_⟩
  · rw [pc];unfold finalPC passPC;split <;> rename_i h <;> simp [show j+1=p.card ↔ p.card-j=1 by omega,h]
  · rw [q4]; simp [lastOf,i]
  · intro w fit away
    exact (same w fit (fun h => away (writes_touched p j hj w h))).trans
      (r.frame w fit (fun h => away (touched_mono p j hj w h)))
  · intro k lo hi
    have away : ¬Writes i (lastOf p j) (128+k) := by
      rintro (⟨_,⟨m,hm,e⟩|⟨m,hm,e⟩⟩|h|h|h|h)
      · unfold heapWord at e; omega
      · unfold rebuiltWord blockWord at e; omega
      all_goals omega
    exact (same (128+k) (by omega) away).trans (r.keyFrame k lo hi)

def passTrace (p : Positions) : Nat → Nat → MachineState → OracleComp World MachineState
  | 0,_,s => pure s
  | n+1,j,s => do let t ← perTrace s (pos p j) (p.card-j) (lastOf p j);passTrace p n (j+1) t

def passSteps (p : Positions) : Nat → Nat → Nat
  | 0,_ => 0
  | n+1,j => perSteps (pos p j) (p.card-j) (lastOf p j)+passSteps p n (j+1)

def passCycles (p : Positions) : Nat → Nat → Nat
  | 0,_ => 0
  | n+1,j => perCycles (pos p j) (p.card-j) (lastOf p j)+passCycles p n (j+1)

def passCalls (p : Positions) : Nat → Nat → Nat
  | 0,_ => 0
  | n+1,j => perCalls (pos p j) (lastOf p j)+passCalls p n (j+1)

theorem pass_post (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (key : BitVec 192)
    (s t : MachineState) (n j : Nat) (r : Ready td p key s j) (bound : j+n≤p.card)
    (hit : t∈support (passTrace p n j s)) : Ready td p key t (j+n) := by
  induction n generalizing j s with
  | zero => simp only [passTrace,support_pure,Set.mem_singleton_iff] at hit;subst t;exact r
  | succ n ih =>
    rw [passTrace,mem_support_bind_iff] at hit;obtain ⟨u,one,rest⟩:=hit
    exact (show j+(n+1)=(j+1)+n by omega) ▸ ih _ _ (next_ready _ _ _ _ _ _ r (by omega) one) (by omega) rest

theorem pass_run (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (key : BitVec 192)
    (s : MachineState) (n j fuel : Nat) (r : Ready td p key s j) (bound : j+n≤p.card) :
    execute openingImage (passSteps p n j+fuel) s true=(do
      let t ← passTrace p n j s;let z ← execute openingImage fuel t true
      return z.charge (passCycles p n j) (passCalls p n j)) := by
  induction n generalizing j s with
  | zero => simp [passSteps,passTrace,passCycles,passCalls,Execution.charge]
  | succ n ih =>
    have card : p.card≤16777216 := by change p.card≤LENGTH;simpa [Index] using Finset.card_le_univ p
    rw [passSteps,Nat.add_assoc,per_run s (pos p j) j _ _ _ (by omega) (by omega) (input_of_ready _ _ _ _ _ r (by omega))]
    simp only [passTrace,bind_assoc]
    apply bind_congr_of_forall_mem_support;intro u hit
    rw [ih u (j+1) (next_ready _ _ _ _ _ _ r (by omega) hit) (by omega)]
    simp only [bind_assoc,pure_bind]
    apply bind_congr;intro t;apply bind_congr;intro z;apply congrArg (fun x : Execution => (pure x : OracleComp World Execution))
    cases z;simp [Execution.charge,passCycles,passCalls] <;> omega

theorem chain_cycles_le (i : Index) : chainCycles i≤299 := by
  have : chainLinks i<34 := by unfold chainLinks; omega
  unfold chainCycles chainSteps chainCalls; omega

theorem chain_calls_le (i : Index) : chainCalls i≤34 := by
  have : chainLinks i<34 := by unfold chainLinks; omega
  unfold chainCalls; omega

/-- At most 359 cycles per position (new even quartet 37, chain link 33: 306, rank 1: 16) plus the exit jump. -/
theorem pass_cycles_bound (p : Positions) (n j : Nat) (bound : j+n≤p.card) : passCycles p n j≤352*n+1 := by
  induction n generalizing j with
  | zero => simp [passCycles]
  | succ n ih =>
    rw [passCycles]
    have h:=ih (j+1) (by omega)
    have c:=chain_cycles_le (pos p j)
    unfold perCycles headCycles postSteps
    by_cases last : p.card-j=1
    · have empty : n=0 := by omega
      subst n;simp only [last,passCycles];split_ifs <;> omega
    · simp only [if_neg last];split_ifs <;> omega

theorem pass_calls_bound (p : Positions) (n j : Nat) : passCalls p n j≤35*n := by
  induction n generalizing j with
  | zero => simp [passCalls]
  | succ n ih =>
    rw [passCalls]
    have h:=ih (j+1); have c:=chain_calls_le (pos p j)
    unfold perCalls; split <;> omega

end TwoPermutationPrototype.GroupedOpening
