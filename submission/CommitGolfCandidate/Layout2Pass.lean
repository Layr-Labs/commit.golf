import CommitGolfCandidate.Layout2PassStep
import CommitGolfCandidate.GroupOpenTableInit
import CommitGolfCandidate.GroupOpenInitial

/-! Layout 2 V2a opener, the first pass over all `k` positions (ordinal `j` in phase `j % 4`): the invariant
`Ready` between positions, execution (`pass_run`), cycles and calls, and under a fixed oracle what it leaves in
the record blocks (`Seen`: salt, pointer and inverse reply of every position). It writes no trapdoor word. -/
namespace TwoPermutationPrototype.GroupedOpening.Layout2V2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.GroupedOpening
open Opening (sortedIndex)
open TwoPermutationPrototype.Sampling (saltWords)
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def pos (p : Positions) (j : Nat) : Index := ((p.sort (·≤·))[j]?).getD ⟨0,by decide⟩
theorem pos_present (p : Positions) (j : Nat) (hj : j<p.card) : pos p j=sortedIndex p j hj := by
  unfold pos sortedIndex;rw [List.getElem?_eq_getElem (by simpa using hj)];rfl

theorem pos_lt (p : Positions) (a b : Nat) (ab : a<b) (hb : b<p.card) : (pos p a).val<(pos p b).val := by
  have ha : a<p.card := by omega
  rw [pos_present p a ha,pos_present p b hb]
  unfold sortedIndex
  have s := (Finset.sortedLT_sort p).pairwise
  exact List.pairwise_iff_getElem.mp s a b (by simpa using ha) (by simpa using hb) ab

theorem pos_of_mem (p : Positions) (idx : Index) (member : idx∈p) : ∃ j, j<p.card ∧ pos p j=idx := by
  have inList : idx∈p.sort (·≤·) := by simpa using member
  obtain ⟨j,hj,hx⟩:=List.mem_iff_getElem.mp inList
  have size : j<p.card := by simpa using hj
  exact ⟨j,size,(pos_present p j size).trans hx⟩

theorem card_le (p : Positions) : p.card≤16777216 := by change p.card≤LENGTH;simpa [Index] using Finset.card_le_univ p

/-- Words the pass may have changed before ordinal `j`: the generator block, the reply scratch and the blocks of
the records before `j`. -/
def Touched (j : Nat) (w : Nat) : Prop :=
  (128≤w ∧ w<153) ∨ (192≤w ∧ w<217) ∨ (∃ a<j, passWord a≤w ∧ w<passWord a+25)

def Preserved (j : Nat) (u s : MachineState) := ∀ w<2^33, ¬Touched j w → memoryView s w=memoryView u w

/-- Distinct records' first 25 block words do not overlap. -/
theorem blocks_apart (a b : Nat) (ab : a<b) : passWord a+25 ≤ passWord b := by
  have ma := pass_word_mul a
  have mb := pass_word_mul b
  have na := pass_dest_next a
  have step : ∀ n, passDest a+passStride (a%4) ≤ passDest (a+1+n) := by
    intro n
    induction n with
    | zero => simp only [Nat.add_zero]; exact na.le
    | succ n ih =>
      have := pass_dest_next (a+1+n)
      rw [show a+1+(n+1)=a+1+n+1 by omega]
      unfold passStride at this; split_ifs at this <;> omega
  have := step (b-a-1)
  rw [show a+1+(b-a-1)=b by omega] at this
  unfold passStride at this
  split_ifs at this <;> omega

theorem touched_mono (j w : Nat) (t : Touched j w) : Touched (j+1) w := by
  rcases t with h|h|⟨a,ha,h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨a,by omega,h⟩)

theorem writes_touched (j w : Nat) (wr : Writes j w) : Touched (j+1) w := by
  rcases wr with h|h|h
  · left; omega
  · right; left; exact h
  · right; right; exact ⟨j,by omega,h⟩

def passPC (p : Positions) (j : Nat) := if j=p.card then address 4096 else address (3079+80*(j%4))

structure Ready (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (key : BitVec 192)
    (s : MachineState) (j : Nat) : Prop extends Registers s j (p.card-j), Base s p where
  pc : s.pc=passPC p j
  cursor : s.getReg .x29=BitVec.ofNat 64 (passDest j)
  frame : Preserved j (actual.initialState .opening (td,p)) s
  keyFrame : KeyWords s key
  sp : s.getReg .x2=BitVec.ofNat 64 tableBase
  mask : s.getReg .x1=65535
  /-- Every processed record's block holds its level-22 sibling node's address in word 2 (`B+16`). -/
  pointer : ∀ a<j, memoryView s (passWord a+2)=wordAddress (nodeWordOf ((pos p a).val/4^^^1))

theorem input_of_ready (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (key : BitVec 192)
    (s : MachineState) (j : Nat) (r : Ready td p key s j) (hj : j<p.card) :
    Entry s (pos p j) j (p.card-j) := by
  have card := card_le p
  have ea : indexAt j=wordAddress (1174405636+j) := by unfold indexAt wordAddress;congr 1 <;> omega
  refine ⟨r.toRegisters,by simpa [passPC,Nat.ne_of_lt hj] using r.pc,r.mark,r.heap,r.leaves,r.slots,r.cursor,
    ?_,?_,r.sp,r.mask,?_⟩
  · have same := r.frame (1174405636+j) (by omega) (by
      rintro (h|h|⟨a,ha,h⟩)
      all_goals (try omega)
      have := pass_word_room a (by omega); have pb : proofBase=13824430176 := rfl; omega)
    have orig := input_index actual actual_layout td p j hj
    rw [pos_present p j hj]
    exact (show s.getMem (indexAt j)=(actual.initialState .opening (td,p)).getMem (indexAt j) by
      simpa only [ea,memoryView] using same).trans orig
  · unfold indexAt;apply Opening.aligned_access
    · omega
    · change _≤2^36;omega
  · intro e he half hh
    have same := r.frame (tableWord e+half) (by simp only [tableWord]; omega) (by
      rintro (h|h|⟨a,ha,h⟩)
      all_goals (try (simp only [tableWord] at h; omega))
      have := pass_word_room a (by omega); have pb : proofBase=13824430176 := rfl; simp only [tableWord] at h; omega)
    rw [same]; exact initial_table td p e he half hh

theorem next_ready (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (key : BitVec 192)
    (s t : MachineState) (j : Nat) (r : Ready td p key s j) (hj : j<p.card)
    (hit : t∈support (perTrace s (pos p j) j (p.card-j))) : Ready td p key t (j+1) := by
  have card := card_le p
  have inp:=input_of_ready td p key s j r hj
  obtain ⟨reg,pc,cur,keep,same,ptr⟩:=trace_post s (pos p j) j (p.card-j) (by omega) (by omega) inp t hit
  have kp (a : Reg) (safe : Saved a := by unfold Saved;decide) := keep a safe
  refine ⟨by simpa only [show p.card-j-1=p.card-(j+1) by omega] using reg,
    ⟨(kp .x8).trans r.indices,(kp .x9).trans r.heap,(kp .x18).trans r.count,
     (kp .x19).trans r.leaves,(kp .x20).trans r.start,(kp .x21).trans r.dest,(kp .x23).trans r.mark,
     (kp .x24).trans r.slots,(kp .x27).trans r.capLeaves⟩,?_,cur,?_,?_,(kp .x2).trans r.sp,(kp .x1).trans r.mask,?_⟩
  · rw [pc];unfold finalPC passPC;split <;> rename_i h <;> simp [show j+1=p.card ↔ p.card-j=1 by omega,h]
  · intro w fit away
    exact (same w fit (fun h => away (writes_touched j w h))).trans
      (r.frame w fit (fun h => away (touched_mono j w h)))
  · intro k lo hi
    have away : ¬Writes j (128+k) := by
      have := pass_word_room j (by omega); have pb : proofBase=13824430176 := rfl
      rintro (h|h|h) <;> omega
    exact (same (128+k) (by omega) away).trans (r.keyFrame k lo hi)
  · intro a ha
    by_cases eq : a=j
    · subst eq; exact ptr
    · have lt : a<j := by omega
      have ap := blocks_apart a j lt
      have room := pass_word_room a (by omega)
      have pb : proofBase=13824430176 := rfl
      rw [same _ (by have := pass_word_room j (by omega); omega) (by rintro (h|h|h) <;> omega)]
      exact r.pointer a lt

def passTrace (p : Positions) : Nat → Nat → MachineState → OracleComp World MachineState
  | 0,_,s => pure s
  | n+1,j,s => do let t ← perTrace s (pos p j) j (p.card-j);passTrace p n (j+1) t

def passSteps (p : Positions) : Nat → Nat → Nat
  | 0,_ => 0
  | n+1,j => perSteps (pos p j) (p.card-j)+passSteps p n (j+1)

def passCycles (p : Positions) : Nat → Nat → Nat
  | 0,_ => 0
  | n+1,j => perCycles (pos p j) (p.card-j)+passCycles p n (j+1)

def passCalls (p : Positions) : Nat → Nat → Nat
  | 0,_ => 0
  | n+1,j => perCalls (pos p j)+passCalls p n (j+1)

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
    have card := card_le p
    rw [passSteps,Nat.add_assoc,per_run s (pos p j) j _ _ (by omega) (by omega) (input_of_ready _ _ _ _ _ r (by omega))]
    simp only [passTrace,bind_assoc]
    apply bind_congr_of_forall_mem_support;intro u hit
    rw [ih u (j+1) (next_ready _ _ _ _ _ _ r (by omega) hit) (by omega)]
    simp only [bind_assoc,pure_bind]
    apply bind_congr;intro t;apply bind_congr;intro z;apply congrArg (fun x : Execution => (pure x : OracleComp World Execution))
    cases z;simp [Execution.charge,passCycles,passCalls] <;> omega

theorem chain_cycles_le (i : Index) : chainCycles i≤280 := by
  have := links_lt i; unfold chainCycles chainSteps chainCalls; omega
theorem chain_calls_le (i : Index) : chainCalls i≤34 := by
  have := links_lt i; unfold chainCalls; omega

/-- At most 312 cycles per position, plus 2 for the last one's exit. -/
theorem pass_cycles_bound (p : Positions) (n j : Nat) (bound : j+n≤p.card) : passCycles p n j≤312*n+2 := by
  induction n generalizing j with
  | zero => simp [passCycles]
  | succ n ih =>
    have c := chain_cycles_le (pos p j)
    have h := ih (j+1) (by omega)
    simp only [passCycles, perCycles]
    by_cases last : p.card-j=1
    · have : n=0 := by omega
      subst this; simp [passCycles, last]; omega
    · simp only [last, if_false]; omega

theorem pass_calls_bound (p : Positions) (n j : Nat) : passCalls p n j≤35*n := by
  induction n generalizing j with
  | zero => simp [passCalls]
  | succ n ih => have := chain_calls_le (pos p j); have := ih (j+1); simp only [passCalls, perCalls]; omega

theorem per_steps_le (i : Index) (left : Nat) : perSteps i left≤69 := by
  have := links_lt i; unfold perSteps chainSteps; split_ifs <;> omega

theorem pass_steps_bound (p : Positions) (n j : Nat) : passSteps p n j≤69*n := by
  induction n generalizing j with
  | zero => simp [passSteps]
  | succ n ih => have := per_steps_le (pos p j) (p.card-j); have := ih (j+1); simp only [passSteps]; omega

/-! ### Fixed oracle -/

/-- The linked (chained) salt array under the oracle's permutation and key `k`. -/
noncomputable abbrev linkedSalts (o : Oracle) (k : BitVec 192) :=
  Permutation.LinkedSalt.salts (Permutation.LinkedSalt.schedule Permutation.LinkedSalt.period) o.permutation k

noncomputable def fixedPass (o : Oracle) (p : Positions) (k : BitVec 192) : Nat → Nat → MachineState → MachineState
  | 0,_,s=>s
  | n+1,j,s=>fixedPass o p k n (j+1) (fixedOne o s (pos p j) j (p.card-j))

theorem next_fixed (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (k : BitVec 192)
    (s : MachineState) (j : Nat) (r : Ready td p k s j) (hj : j<p.card) :
    Ready td p k (fixedOne o s (pos p j) j (p.card-j)) (j+1) :=
  next_ready td p k s _ j r hj (fixed_mem o k s _ j _ (input_of_ready td p k s j r hj) (by have := card_le p; omega)
    r.keyFrame)

theorem pass_fixed (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (k : BitVec 192)
    (s : MachineState) (j n : Nat) (bound : j+n≤p.card) (r : Ready td p k s j) :
    o.run (passTrace p n j s)=pure (fixedPass o p k n j s,passCalls p n j) := by
  induction n generalizing j s with
  | zero => exact oracle_run_pure ..
  | succ n ih =>
    have one := trace_fixed o k s (pos p j) j (p.card-j) (input_of_ready td p k s j r (by omega))
      (by have := card_le p; omega) r.keyFrame
    rw [passTrace,oracle_run_bind,one,pure_bind];dsimp only
    rw [ih _ (j+1) (by omega) (next_fixed o td p k s j r (by omega))]
    simp [fixedPass,passCalls,Nat.add_comm]

theorem fixed_post (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (k : BitVec 192)
    (s : MachineState) (j n : Nat) (bound : j+n≤p.card) (r : Ready td p k s j) :
    Ready td p k (fixedPass o p k n j s) (j+n) := by
  induction n generalizing j s with
  | zero => simpa [fixedPass] using r
  | succ n ih =>
    simpa only [fixedPass,show j+(n+1)=(j+1)+n by omega] using ih _ (j+1) (by omega) (next_fixed o td p k s j r (by omega))

/-- The reply window of a quartet: the trapdoor's reply, untouched by the pass. -/
theorem reply_window (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (k : BitVec 192) (s : MachineState)
    (j : Nat) (hj : j ≤ p.card) (r : Ready td p k s j) (q : Nat) (hq : q<4194304) :
    packBuffer (window (memoryView s) (replyWord q))=groupReply td q := by
  have off : 8*replyWord q=trapdoorBase+groupReplyOffset q := by
    unfold replyWord groupReplyOffset blockWord trapdoorBase LENGTH LOG_LENGTH; split <;> omega
  have hw : (window (memoryView s) (replyWord q) : Words 25)=
      window (memoryView (actual.initialState .opening (td,p))) (replyWord q) := by
    funext w; unfold window
    have card := card_le p
    exact r.frame _ (by unfold replyWord blockWord;omega) (by
      have := w.isLt
      rintro (h|h|⟨a,ha,h⟩)
      · unfold replyWord blockWord at h; omega
      · unfold replyWord blockWord at h; omega
      · have := pass_word_room a (by omega); have pb : proofBase=13824430176 := rfl
        unfold replyWord blockWord at h; omega)
  rw [hw,←read_permutation_window,off]
  exact input_trapdoor_slice actual actual_layout td p _ 200
    (by change _≤5100273664; unfold groupReplyOffset LENGTH LOG_LENGTH; split <;> omega)

/-- After the first `n` positions: each record block holds its linked salt (words 0..1) and the inverse of its
quartet's reply (words 3..24). -/
structure Seen (o : Oracle) (k : BitVec 192) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions)
    (s : MachineState) (n : Nat) : Prop where
  salt : ∀ a<n, ∀ j : Fin 2, memoryView s (passWord a+j.val)=saltWords (linkedSalts o k (pos p a)) j
  reply : ∀ a<n, ∀ m (hm : m<25), 3≤m → memoryView s (passWord a+m)=
    replyWords (o.permutation.symm (groupReply td ((pos p a).val/4))) ⟨m,hm⟩

theorem next_seen (o : Oracle) (k : BitVec 192) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions)
    (s : MachineState) (j : Nat) (hj : j<p.card) (r : Ready td p k s j) (old : Seen o k td p s j) :
    Seen o k td p (fixedOne o s (pos p j) j (p.card-j)) (j+1) := by
  have card := card_le p
  let i:=pos p j
  have ix : i.val<16777216:=i.isLt
  have inp:=input_of_ready td p k s j r hj
  have mem := fixed_mem o k s i j (p.card-j) inp (by omega) r.keyFrame
  obtain ⟨_,_,_,_,same,_⟩ := trace_post s i j (p.card-j) (by omega) (by omega) inp _ mem
  have fb := fixed_block o k s i j (p.card-j) (by omega) (by omega) inp r.keyFrame
  have keep (a : Nat) (ha : a<j) (m : Nat) (hm : m<25) :
      memoryView (fixedOne o s i j (p.card-j)) (passWord a+m)=memoryView s (passWord a+m) := by
    have ap := blocks_apart a j ha
    have room := pass_word_room a (by omega)
    have pb : proofBase=13824430176 := rfl
    exact same _ (by have := pass_word_room j (by omega); omega) (by rintro (h|h|h) <;> omega)
  refine ⟨?_,?_⟩
  · intro a ha jj
    by_cases eq : a=j
    · subst eq; exact fb.1 jj
    · rw [keep a (by omega) _ (by have := jj.isLt; omega)]; exact old.salt a (by omega) jj
  · intro a ha m hm three
    by_cases eq : a=j
    · subst eq
      rw [fb.2 m hm three, fixedInverse, inverseQuery, reply_window td p k s a (by omega) r _ (by omega)]
    · rw [keep a (by omega) m hm]; exact old.reply a (by omega) m hm three

theorem seen_pass (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (k : BitVec 192)
    (s : MachineState) (j n : Nat) (b : j+n≤p.card) (r : Ready td p k s j) (seen : Seen o k td p s j) :
    Seen o k td p (fixedPass o p k n j s) (j+n) := by
  induction n generalizing s j with
  | zero => simpa [fixedPass] using seen
  | succ n ih =>
    simpa only [fixedPass,show j+(n+1)=(j+1)+n by omega] using ih _ (j+1) (by omega)
      (next_fixed o td p k s j r (by omega)) (next_seen o k td p s j (by omega) r seen)

theorem seen_zero (o : Oracle) (k : BitVec 192) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions)
    (s : MachineState) : Seen o k td p s 0 := ⟨fun _ h => absurd h (Nat.not_lt_zero _),fun _ h => absurd h (Nat.not_lt_zero _)⟩

end TwoPermutationPrototype.GroupedOpening.Layout2V2
