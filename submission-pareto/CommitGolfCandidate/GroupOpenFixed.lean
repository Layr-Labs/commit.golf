import CommitGolfCandidate.GroupOpenPass
import CommitGolfCandidate.GroupOpenModel

/-! K3-lite: the prefix pass under a fixed oracle, and what it leaves in memory (salts and the rebuilt blocks of
the opened quartets; the sibling-node pointers are a `Ready` fact). -/
namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open CommitGolfCandidate.Permutation.CounterSalt (coord)
open TwoPermutationPrototype.Sampling
set_option maxRecDepth 18000
set_option maxHeartbeats 1400000

/-- The linked (chained) salt array under the oracle's permutation and key `k`. -/
noncomputable abbrev linkedSalts (o : Oracle) (k : BitVec 192) :=
  Permutation.LinkedSalt.salts (Permutation.LinkedSalt.schedule Permutation.LinkedSalt.period) o.permutation k

noncomputable def fixedPass (o : Oracle) (p : Positions) (k : BitVec 192) : Nat → Nat → MachineState → MachineState
  | 0,_,s=>s
  | n+1,j,s=>fixedPass o p k n (j+1) (fixedOne o s (pos p j) (p.card-j) (lastOf p j))

theorem next_fixed (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (k : BitVec 192)
    (s : MachineState) (j : Nat) (r : Ready td p k s j) (hj : j<p.card) :
    Ready td p k (fixedOne o s (pos p j) (p.card-j) (lastOf p j)) (j+1) :=
  next_ready td p k s _ j r hj (fixed_mem o k s _ j _ _ (input_of_ready td p k s j r hj) r.keyFrame)

theorem pass_fixed (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (k : BitVec 192)
    (s : MachineState) (j n : Nat) (bound : j+n≤p.card) (r : Ready td p k s j) :
    o.run (passTrace p n j s)=pure (fixedPass o p k n j s,passCalls p n j) := by
  induction n generalizing j s with
  | zero => exact oracle_run_pure ..
  | succ n ih =>
    have one := trace_fixed o k s (pos p j) j (p.card-j) (lastOf p j) (input_of_ready td p k s j r (by omega)) r.keyFrame
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

theorem xor_inj (a b : Nat) (h : a^^^1=b^^^1) : a=b := by
  have := congrArg (· ^^^ 1) h; simpa [Nat.xor_assoc] using this

-- ---------------------------------------------------------------- one step's memory effect
/-- Outside the words the step may write, the fixed outcome keeps the word. -/
theorem step_view (o : Oracle) (k : BitVec 192) (s : MachineState) (i : Index) (ord left last : Nat)
    (l : 0<left) (hi : left≤16777216) (bound : ord+left≤16777216) (r : Input s i ord left last) (key : KeyWords s k) (w : Nat) (fit : w<2^33)
    (away : ¬Writes i last w) : memoryView (fixedOne o s i left last) w=memoryView s w := by
  have n128 : w≠128 := fun h => away (Or.inr (Or.inl h))
  have nsc : w<192 ∨ 217≤w := by by_contra h; exact away (Or.inr (Or.inr (Or.inl (by omega))))
  have ns : w≠1140851204+2*i.val ∧ w≠1140851204+2*i.val+1 :=
    ⟨fun h => away (Or.inr (Or.inr (Or.inr (Or.inl h)))),fun h => away (Or.inr (Or.inr (Or.inr (Or.inr h))))⟩
  rw [fixed_outside o k s i ord left last l hi bound r key w fit n128 nsc ns]
  exact head_outside s i ord left last r _ w fit (fun h => away (Or.inl h)) nsc

theorem salt_word_view (s : MachineState) (i : Index) (j : Fin 2) :
    s.getMem (destAt i+BitVec.ofNat 64 (8*j.val))=memoryView s (1140851204+2*i.val+j.val) := by
  have ix := i.isLt
  have jj := j.isLt
  have addr : destAt i+BitVec.ofNat 64 (8*j.val)=wordAddress (1140851204+2*i.val+j.val) := by
    unfold destAt wordAddress;rw [←BitVec.ofNat_add];congr 1 <;> omega
  rw [addr]; rfl

-- ---------------------------------------------------------------- what the pass leaves behind
/-- After the first `n` positions: their salts are the linked salts and their quartets' rebuilt blocks hold the
inverses of their replies. -/
structure Seen (o : Oracle) (k : BitVec 192) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions)
    (s : MachineState) (n : Nat) : Prop where
  salt : ∀ a<n, ∀ j : Fin 2, s.getMem (destAt (pos p a)+BitVec.ofNat 64 (8*j.val))=saltWords (linkedSalts o k (pos p a)) j
  block : ∀ a<n, ∀ m (hm : m<25), memoryView s (rebuiltWord ((pos p a).val/4)+m)=
    replyWords (o.permutation.symm (packBuffer (window (memoryView (actual.initialState .opening (td,p)))
      (replyWord ((pos p a).val/4))))) ⟨m,hm⟩

theorem node_untouched (p : Positions) (j h m : Nat) (hh : h<4194304) (hm : m<4) : ¬Touched p j (nodeWordOf h+m) := by
  have t := top_le p j
  rintro (x|x|x|x|⟨q,hq,m',hm',e⟩) <;> unfold nodeWordOf blockWord at * <;> (try unfold rebuiltWord blockWord at e) <;> omega

/-- No rebuilt block overlaps a reply window (they sit at different offsets within every 1024-byte block). -/
theorem reply_untouched (p : Positions) (j q m : Nat) (small : q<4194304) (hm : m<25) :
    ¬Touched p j (replyWord q+m) := by
  have t := top_le p j
  rintro (x|x|x|x|⟨q',hq',m',hm',e⟩) <;> unfold replyWord blockWord at * <;> (try unfold rebuiltWord blockWord at e)
  all_goals (try omega)
  rcases Nat.mod_two_eq_zero_or_one q with h|h <;> rcases Nat.lt_or_ge q' (2*(q/2)) with h'|h' <;> omega

set_option maxHeartbeats 4000000 in
theorem next_seen (o : Oracle) (k : BitVec 192) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions)
    (s : MachineState) (j : Nat) (hj : j<p.card) (r : Ready td p k s j) (old : Seen o k td p s j) :
    Seen o k td p (fixedOne o s (pos p j) (p.card-j) (lastOf p j)) (j+1) := by
  let i:=pos p j
  have card : p.card≤16777216:=by change p.card≤LENGTH;simpa [Index] using Finset.card_le_univ p
  have ix : i.val<16777216:=i.isLt
  have inp:=input_of_ready td p k s j r hj
  have view (w : Nat) (fit : w<2^33) (away : ¬Writes i (lastOf p j) w) :=
    step_view o k s i j (p.card-j) (lastOf p j) (by omega) (by omega) (by omega) inp r.keyFrame w fit away
  have qlt : i.val/4<4194304 := by omega
  refine ⟨?_,?_⟩
  · -- salts
    intro a ha jj
    by_cases eq : a=j
    · subst eq; exact fixed_salt o k s i a (p.card-a) (lastOf p a) (by omega) (by omega) (by omega) inp r.keyFrame jj
    · have lt : a<j := by omega
      have av := (pos p a).isLt
      have dist : (pos p a).val < i.val := pos_lt p a j lt hj
      have jl := jj.isLt
      rw [salt_word_view]
      change _<16777216 at av
      rw [view _ (by omega) (by
        rintro (⟨_,m,hm,e⟩|h|h|h|h)
        · unfold rebuiltWord blockWord at e; omega
        all_goals omega)]
      have := old.salt a lt jj; rwa [salt_word_view] at this
  · -- rebuilt blocks
    intro a ha m hm
    have keep (b : Nat) (hb : b<j)
        (stay : ¬HeadWrites i (lastOf p j) (rebuiltWord ((pos p b).val/4)+m)) :
        memoryView (fixedOne o s i (p.card-j) (lastOf p j)) (rebuiltWord ((pos p b).val/4)+m)=
          replyWords (o.permutation.symm (packBuffer (window (memoryView (actual.initialState .opening (td,p)))
            (replyWord ((pos p b).val/4))))) ⟨m,hm⟩ := by
      have bv := (pos p b).isLt
      change _<16777216 at bv
      rw [view _ (by unfold rebuiltWord blockWord;omega) (by
        rintro (h|h|h|h|h)
        · exact stay h
        all_goals (unfold rebuiltWord blockWord at h; omega))]
      exact old.block b hb m hm
    by_cases eq : a=j
    · subst eq
      by_cases fresh : i.val/4≠lastOf p a
      · rw [fixed_block o k s i a (p.card-a) (lastOf p a) (by omega) (by omega) (by omega) inp r.keyFrame fresh m hm]
        have hw : (window (memoryView s) (replyWord (i.val/4)) : Words 25)=
            window (memoryView (actual.initialState .opening (td,p))) (replyWord (i.val/4)) := by
          funext w; unfold window
          exact r.frame _ (by unfold replyWord blockWord;omega) (reply_untouched p a _ w.val qlt w.isLt)
        rw [hw]
      · have same : i.val/4=lastOf p a := by omega
        obtain ⟨pos0,prev⟩ := stale_prev p a hj same
        have k' := keep (a-1) (by omega) (by rintro ⟨f,_⟩; exact f same)
        rwa [prev] at k'
    · have lt : a<j := by omega
      apply keep a lt
      rintro ⟨fresh,m',hm',e⟩
      have up := fresh_above p j hj fresh a lt
      have av := (pos p a).isLt; change _<16777216 at av
      unfold rebuiltWord blockWord at e; omega

theorem seen_pass (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (k : BitVec 192)
    (s : MachineState) (j n : Nat) (b : j+n≤p.card) (r : Ready td p k s j) (seen : Seen o k td p s j) :
    Seen o k td p (fixedPass o p k n j s) (j+n) := by
  induction n generalizing s j with
  | zero => simpa [fixedPass] using seen
  | succ n ih =>
    simpa only [fixedPass,show j+(n+1)=(j+1)+n by omega] using ih _ (j+1) (by omega)
      (next_fixed o td p k s j r (by omega)) (next_seen o k td p s j (by omega) r seen)

theorem seen_zero (o : Oracle) (k : BitVec 192) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (s : MachineState) :
    Seen o k td p s 0 :=
  ⟨fun _ h => (Nat.not_lt_zero _ h).elim,fun _ h => (Nat.not_lt_zero _ h).elim⟩

end TwoPermutationPrototype.GroupedOpening
