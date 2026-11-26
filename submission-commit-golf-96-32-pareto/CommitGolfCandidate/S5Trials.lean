import CommitGolfCandidate.S5HonestNormalWire
namespace CommitGolfCandidate.S5
open CommitGolf
open S5Machine.Reader (window)
open S5Machine.Check (window_mod)
theorem canonical_valid (o : Oracle) (m : Message) (ps : Positions) (s : Late.SaltTape) :
    wireValid o.compression (S5Machine.canonicalInput o m ps s) := by
  by_cases b : ps.card=BATCH
  · change (if ps.card=BATCH then _ else _);rw [if_pos b]
    exact ⟨S5Machine.Check.opening_length _ _ _ b,honest_batch_wire o m ps s b⟩
  · exact normal_wire o m ps s b
theorem before_cut (v t n w : Nat) (inside : n+w≤wireBits) : window (complete v t) n w=window v n w := by
  have low : complete v t%2^wireBits=v%2^wireBits:=by unfold complete;rw [Nat.add_mul_mod_self_left,Nat.mod_mod]
  exact (window_mod _ _ _ _ inside).symm.trans ((congrArg (fun z=>window z n w) low).trans (window_mod _ _ _ _ inside))

attribute [local irreducible] packedInput window
theorem trial_salt (x : CheckInput) (q : Fin 4) (r : Nat) (inside : r<128) :
    (batchView x q).salt r=(batchView x 0).salt r := by
  change BitVec.ofNat 192 (window (complete (packedInput x) q.val) _ _)=BitVec.ofNat 192 (window (complete (packedInput x) 0) _ _)
  rw [before_cut _ q.val _ _ (by unfold wireBits;omega),before_cut _ 0 _ _ (by unfold wireBits;omega)]
theorem trial_peer (x : CheckInput) (q : Fin 4) (r h : Nat) (br : r<128) (bh : h<15) :
    (batchView x q).peers r h=(batchView x 0).peers r h := by
  have width : layerBits h+bits h≤4030 := (by decide +kernel : ∀ j : Fin 15,layerBits j.val+bits j.val≤4030) ⟨h,bh⟩
  apply Prod.ext
  · change BitVec.ofNat 256 (window (complete (packedInput x) q.val) _ _)=BitVec.ofNat 256 (window (complete (packedInput x) 0) _ _)
    rw [before_cut _ q.val _ _ (by unfold wireBits;omega),before_cut _ 0 _ _ (by unfold wireBits;omega)]
  · by_cases z : h=0
    · subst h
      change BitVec.ofNat 256 (window (complete (packedInput x) q.val) (4030*r+192+256) 256)=BitVec.ofNat 256 (window (complete (packedInput x) 0) _ _)
      rw [before_cut _ q.val _ _ (by unfold wireBits;omega),before_cut _ 0 _ _ (by unfold wireBits;omega)]
      rfl
    · simp only [batchView,if_neg z]
theorem trial_lower (H : Compression) (x : CheckInput) (q : Fin 4) (r : Nat) (br : r<128) :
    Auth.lower H (batchView x q) r=Auth.lower H (batchView x 0) r := by
  unfold Auth.lower Auth.recordAt
  rw [trial_salt x q r br]
  exact Auth.walk_congr H _ _ _ _ 15 (trial_peer x q r · br)

theorem trial_slot (x : CheckInput) (q : Fin 4) (j : Nat) (early : j<170) :
    (batchView x q).slot j=(batchView x 0).slot j := by
  change BitVec.ofNat 256 (window (complete (packedInput x) q.val) _ _)=BitVec.ofNat 256 (window (complete (packedInput x) 0) _ _)
  rw [before_cut _ q.val _ _ (by unfold wireBits;omega),before_cut _ 0 _ _ (by unfold wireBits;omega)]

private theorem select_compatible {v w : Auth.View} {a b : Nat→Late.Digest} (j : Nat)
    (same : Auth.bucket v=Auth.bucket w) (agree : ∀ r<128,a r=b r) : Auth.select v a j=Auth.select w b j := by
  unfold Auth.select;rw [same]
  cases e : (List.range 128).find? (fun r=>Auth.bucket w r==j)
  · rfl
  next r=>exact congrArg some (agree r (List.mem_range.mp (List.mem_of_find?_eq_some e)))
private theorem same_bucket (x : CheckInput) (q : Fin 4) : Auth.bucket (batchView x q)=Auth.bucket (batchView x 0):=by
  funext r;simp only [Auth.bucket,batchView]
theorem trial_select (H : Compression) (x : CheckInput) (q : Fin 4) (j : Nat) :
    Auth.select (batchView x q) (Auth.lower H (batchView x q)) j=Auth.select (batchView x 0) (Auth.lower H (batchView x 0)) j :=
  select_compatible j (same_bucket x q) (trial_lower H x q)
attribute [local irreducible] batchView Auth.lower Auth.bucket
theorem trial_pairs (H : Compression) (x : CheckInput) (q : Fin 4) (j : Nat) (early : j<170) :
    Auth.batchCap H (batchView x q) j=Auth.batchCap H (batchView x 0) j := by
  unfold Auth.batchCap Auth.pairAt Auth.pairChildren
  rw [trial_slot x q j early,trial_select H x q (2*j),trial_select H x q (2*j+1)]
theorem trial_consistent (H : Compression) (x : CheckInput) (q : Fin 4) :
    (∀ r<128,Auth.select (batchView x q) (Auth.lower H (batchView x q)) (Auth.bucket (batchView x q) r)=some (Auth.lower H (batchView x q) r)) ↔
    (∀ r<128,Auth.select (batchView x 0) (Auth.lower H (batchView x 0)) (Auth.bucket (batchView x 0) r)=some (Auth.lower H (batchView x 0) r)) := by
  constructor <;> intro h r small
  · have h':=h r small
    rw [same_bucket x q,trial_select H x q _,trial_lower H x q r small] at h'
    exact h'
  · rw [same_bucket x q,trial_select H x q _,trial_lower H x q r small]
    exact h r small

theorem upper_local (H : Compression) (a b : Nat→Late.Digest) (same : ∀ i<171,i≠170→a i=b i)
    (h i : Nat) (apart : i≠170/2^h) : Auth.upper H a h i=Auth.upper H b h i := by
  induction h generalizing i with
  | zero=>
    simp only [Auth.upper];split
    next inside=>exact same i inside (by simpa using apart)
    next=>rfl
  | succ h ih=>
    have p : i≠(170/2^h)/2:=by simpa only [Nat.div_div_eq_div_mul,pow_succ] using apart
    simp only [Auth.upper];split
    next present=>rw [ih (2*i) (by omega),ih (2*i+1) (by omega)]
    next=>rfl
end CommitGolfCandidate.S5
