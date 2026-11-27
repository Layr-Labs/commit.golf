import CommitGolfCandidate.PentaGroupedFrame
import CommitGolfCandidate.PentaGroupedScan

/-! Memory invariant (`Good`) preserved across all 16,777,215 loop leaves and the trailing leaf:
messages ahead, leaf digests written so far, all 40-byte zero prefixes of levels 0 .. 10,
the 24-byte key block `keyWord + 1..24`, and the active 11-leaf salt group buffer. -/
namespace TwoPermutationPrototype.PentaGrouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling TwoPermutationPrototype.Quad.Commit
open TwoPermutationPrototype.RV64.PackedLeaves
open CommitGolfCandidate.Permutation.CounterSalt (coord input parts salts)
set_option maxHeartbeats 2500000
set_option maxRecDepth 18000

def digestWords (v : BitVec 256) : Words 4 := fun k => v.extractLsb' (64 * k.val) 64

private theorem pinned_tag_matches (i : Index) : pinnedPositionTag i = secondTag i.val := by
  unfold pinnedPositionTag secondTag firstTag
  change BitVec.ofNat 64 (4152 + 256 * i.val) = BitVec.ofNat 64 (4056 + 256 * i.val) + BitVec.ofNat 64 96
  rw [← BitVec.ofNat_add]
  congr 1 <;> omega

theorem pinned_typed_words (i : Index) (n : Words 2) (r : Words 25) (m : Words 32) :
    pinnedSecondInput i n r m = pinnedWords (secondTag i.val) n r m := by
  unfold pinnedSecondInput pinnedWords
  rw [pinned_tag_matches]

def groupReply (o : Oracle) (k : BitVec 192) (i : Index) := o.permutation (input (coord i).1 k)

noncomputable def value (o : Oracle) (k : BitVec 192) (m : Message) (i : Index) :=
  pinnedFullLeafDigests (BiPermutation.equiv Block o.permutation) m (salts o.permutation k) i

structure Good (o : Oracle) (k : BitVec 192) (msg : Message) (m : Memory) (n : Nat) : Prop where
  messages : ∀ i : Index, n ≤ i.val → window m (msgWord i.val) = messageWords msg i
  children : ∀ i : Index, i.val < n → window m (leafWord i.val) = digestWords (value o k msg i)
  zeros : ∀ l g, l ≤ 11 → g < pentaCount (l + 1) → ∀ t, t < Quad.Commit.prefixWords l → m (pentaGroupWord l g + t) = 0
  key : KeyIntact m k
  group : ∀ i : Index, n = i.val → rank n ≠ 0 → ∀ j : Fin 11, j.val ≠ 0 →
    window m (groupBuffer n + 2 * (j.val - 1)) = Counter.slice (replyWords (groupReply o k i)) j

theorem next_coord (i j : Index) (step : j.val = i.val + 1) (active : rank j.val ≠ 0) :
    (coord j).1 = (coord i).1 := by
  have edge : i.val % 4095 ≠ 4094 := by
    intro h; apply active; unfold rank; rw [step, show (i.val + 1) % 4095 = 0 by omega]
  have a : j.val / 4095 = i.val / 4095 := by omega
  have b : j.val % 4095 = i.val % 4095 + 1 := by omega
  have c : j.val % 4095 / 11 = i.val % 4095 / 11 := by
    unfold rank at active; rw [b] at active ⊢; omega
  apply Fin.ext; simp only [coord, a, c]

theorem digest_meaning (o : Oracle) (k : BitVec 192) (msg : Message) (m : Memory)
    (i : Index) (good : Good o k msg m i.val) :
    lowDigest (replyWords (digestReply o m i.val)) = digestWords (value o k msg i) := by
  have msgEq := good.messages i le_rfl
  have tag : wordAddress (msgWord i.val + 7) = secondTag i.val := by
    change BitVec.ofNat 64 _ = BitVec.ofNat 64 _ + BitVec.ofNat 64 96
    rw [← BitVec.ofNat_add]; congr 1 <;> unfold msgWord <;> omega
  have first : firstReply o m i.val = (pinnedFirstRow o.permutation (messageWords msg i)).2 := by
    unfold firstReply; change o.permutation (packBuffer (rawPrefix (window m (msgWord i.val)))) = _
    rw [msgEq]; rfl
  have sec : window (preSecond o m i.val) (msgWord i.val + 7) =
      pinnedWords (secondTag i.val) (saltWords (salts o.permutation k i))
        (replyWords (firstReply o m i.val)) (messageWords msg i) := by
    unfold preSecond
    by_cases head : rank i.val = 0
    · rw [if_pos head, direct_argument _ _ _ i.isLt, generated_eq _ _ i k good.key head, tag, msgEq]
      have coord0 : (coord i).2 = 0 := Fin.ext head
      apply congrArg (fun ns => pinnedWords (secondTag i.val) ns (replyWords (firstReply o m i.val)) (messageWords msg i))
      exact (Counter.slice_eq (groupReply o k i) 0).trans (by unfold salts Permutation.CounterSalt.nonceAt; rw [coord0]; rfl)
    · rw [if_neg head, regular_argument _ _ _ head, tag, msgEq]
      have keep := good.group i rfl head (coord i).2 head
      rw [show sourceWord i.val = groupBuffer i.val + 2 * ((coord i).2.val - 1) from rfl, keep]
      exact congrArg (fun ns => pinnedWords (secondTag i.val) ns (replyWords (firstReply o m i.val)) (messageWords msg i))
        (Counter.slice_eq (groupReply o k i) (coord i).2)
  have reply : digestReply o m i.val = (pinnedSecondRow o.permutation i (saltWords (salts o.permutation k i))
      (pinnedFirstRow o.permutation (messageWords msg i)).2 (messageWords msg i)).2 := by
    rw [digestReply, sec, first]; simp only [pinnedSecondRow, pinned_typed_words]
  rw [reply]
  funext j; exact low_digest_word _ j

theorem good_step (o : Oracle) (k : BitVec 192) (msg : Message) (m : Memory)
    (i : Index) (h : Good o k msg m i.val) : Good o k msg (packetMem o m i.val) (i.val + 1) := by
  have hi : i.val < 16777216 := i.isLt
  have same := packet_frame o m i.val
  constructor
  · intro j hj; funext a
    apply Eq.trans _ (congrFun (h.messages j (by omega)) a)
    have t := a.isLt; have ix : j.val < 16777216 := j.isLt
    apply same _ hi <;> simp only [msgWord, keyWord, saltWord, leafWord, groupWord] <;> omega
  · intro j hj
    by_cases eq : j = i
    · subst j; exact (new_digest ..).trans (digest_meaning o k msg m i h)
    · have ne : j.val ≠ i.val := fun hh => eq (Fin.ext hh)
      apply Eq.trans _ (h.children j (by omega)); funext a
      have t := a.isLt; have ix : j.val < 16777216 := j.isLt
      have sep := leaf_digest_separate j.val i.val (by omega)
      apply same _ hi
      · unfold leafWord groupWord keyWord saltWord; omega
      · unfold leafWord groupWord msgWord; omega
      · left; omega
  · intro l g hl hg t ht
    apply Eq.trans _ (h.zeros l g hl hg t ht)
    have := Quad.Commit.prefix_words_le l
    have below := group_below_salts l g (by omega) hg 0
    have above := trapdoor_below_levels l g (by omega)
    apply same _ hi
    · unfold keyWord; omega
    · right; unfold msgWord; omega
    · by_cases z0 : l = 0
      · subst z0
        have : Quad.Commit.prefixWords 0 = 5 := rfl
        rw [← group_word_level]
        rcases leaf_zero_prefix_separate i.val g with h1 | h2
        · right; omega
        · left; omega
      · have ig : i.val / 5 < pentaCount 1 := by change i.val / 5 < 3355444; omega
        have ord := level_order 0 l (i.val / 5) (by omega) (by omega) ig g
        have endW := leaf_write_end i.val
        rw [← group_word_level] at ord
        have e : groupWord (i.val / 5 + 1) = groupWord (i.val / 5) + 46 := by unfold groupWord; omega
        right; omega
  · intro j lo up
    apply Eq.trans _ (h.key j lo up)
    have sep := leaf_salt_separate i.val 0 hi
    apply same _ hi
    · omega
    · right; unfold msgWord keyWord saltWord; omega
    · right; unfold keyWord; omega
  · intro next eq active j nz
    have ix : next.val = i.val + 1 := eq.symm
    have nbuf := buffer_next i.val active
    have nc := next_coord i next ix (by rwa [ix])
    rw [nbuf, groupReply, nc]
    by_cases head : rank i.val = 0
    · rw [keep_direct o m i.val hi head j nz, generated_eq o m i k h.key head]
    · apply Eq.trans _ (h.group i rfl head j nz)
      funext a
      have ja := j.isLt; have aa := a.isLt
      apply same _ hi <;> simp only [groupBuffer, msgWord, rank, keyWord, saltWord, leafWord, groupWord] at * <;> omega

theorem good_congr (o : Oracle) (k : BitVec 192) (msg : Message) (m m' : Memory) (n : Nat)
    (eq : ∀ w < 2^33, m' w = m w) (bound : n ≤ 16777216) (h : Good o k msg m n) : Good o k msg m' n := by
  constructor
  · intro i hi; apply Eq.trans _ (h.messages i hi); funext j
    apply eq; have := j.isLt; have ix : i.val < 16777216 := i.isLt; unfold msgWord; omega
  · intro i hi; apply Eq.trans _ (h.children i hi); funext j
    apply eq; have := j.isLt; have ix : i.val < 16777216 := i.isLt; unfold leafWord groupWord; omega
  · intro l g hl hg t ht
    have below := group_below_salts l g (by omega) hg 0
    have := Quad.Commit.prefix_words_le l
    exact (eq _ (by unfold saltWord at below; omega)).trans (h.zeros l g hl hg t ht)
  · intro j hj hi; exact (eq _ (by unfold keyWord saltWord; omega)).trans (h.key j hj hi)
  · intro i hi a j nz; apply Eq.trans _ (h.group i hi a j nz); funext v
    apply eq; have := j.isLt; have := v.isLt; unfold groupBuffer msgWord; omega

/-- The four preloaded words remain equal to their retained generator slice after each packet. -/
theorem plan_saved (o : Oracle) (v : View) (i : Nat) (hi : i < 16777215)
    (inputReg : v.regs .x10 = wordAddress (msgWord i)) (old : Prefetched v.regs v.mem i) :
    Prefetched ((plan i).foldl (viewStep o) v).regs (packetMem o v.mem i) (i + 1) := by
  intro active nextFull j
  have base := buffer_next i (by omega : rank (i + 1) ≠ 0)
  rw [base]
  have small : i % 4095 < 4092 := by unfold rank at active; omega
  have jhi := j.isLt
  by_cases direct : rank i = 0
  · have start : groupBuffer i = msgWord i - 15 := by simp [groupBuffer, direct]
    let a := msgWord i - 15 + (16 + j.val)
    have apartQ : ¬(leafWord i ≤ a ∧ a < leafWord i + 25) := by
      dsimp [a]; unfold leafWord groupWord msgWord; omega
    have apartTag : a ≠ msgWord i + 7 := by dsimp [a]; unfold msgWord; omega
    have frame : packetMem o v.mem i a =
        writeWindow (seededMem o v.mem i) (msgWord i - 15) (replyWords (generated o v.mem i)) a := by
      unfold packetMem preSecond; rw [if_pos direct]
      simp only [directState, writeWindow, apartQ, dite_false, writeWord, apartTag, ite_false]
    rw [start]
    change _ = packetMem o v.mem i a
    rw [frame]
    fin_cases j <;> by_cases shift : rebase (i % 4095) <;>
      simp [plan, within_rank, within_period, direct, show i % 4095 ≠ 4092 by omega, shift,
        cacheReg, viewStep, View.reg, View.store, View.reply, seededMem, generated, firstState, firstReply, inputReg, a]
  · have stable : packetMem o v.mem i (groupBuffer i + (16 + j.val)) = v.mem (groupBuffer i + (16 + j.val)) := by
      apply packet_frame o v.mem i _ (by omega)
      all_goals simp only [groupBuffer, msgWord, rank, keyWord, saltWord, leafWord, groupWord] at * <;> omega
    rw [stable, ← (old (by omega) small j)]
    fin_cases j <;> by_cases near : rank i ≤ 8 <;> by_cases ninth : rank i = 9 <;> by_cases shift : rebase (i % 4095) <;>
      simp [plan, within_rank, direct, near, ninth, shift, cacheReg, viewStep, View.reg, View.store, View.reply]

theorem fixed_packet_good (o : Oracle) (k : BitVec 192) (msg : Message) (s : MachineState)
    (i : Index) (hi : i.val < 16777215) (r : PacketRegs s i.val) (h : Good o k msg (memoryView s) i.val)
    (saved : Prefetched s.getReg (memoryView s) i.val) :
    let next := (plan i.val).foldl (fixedStep o) s
    Good o k msg (memoryView next) (i.val + 1) ∧ Prefetched next.getReg (memoryView next) (i.val + 1) := by
  let v : View := ⟨s.getReg, memoryView s⟩
  have mat := matches_ops o s v _ (walk_post _ _ _ (packet_walk s i.val hi r)).1 (matches_initial s)
  have eq := plan_meaning o v i.val r.msg saved
  have mm := mat.2; rw [eq] at mm
  constructor
  · exact good_congr o k msg _ _ _ mm (by omega) (good_step o k msg _ i h)
  · intro live full j
    have ji := j.isLt
    have budget : groupBuffer (i.val + 1) + (16 + j.val) < 2^33 := by unfold groupBuffer msgWord; omega
    rw [mat.1, mm _ budget]
    exact plan_saved o v i.val hi r.msg saved live full j

theorem fixed_trailing_good (o : Oracle) (k : BitVec 192) (msg : Message) (s : MachineState)
    (r : PacketRegs s 16777215) (h : Good o k msg (memoryView s) 16777215) :
    Good o k msg (memoryView (trailingPlan.foldl (fixedStep o) s)) 16777216 := by
  let v : View := ⟨s.getReg, memoryView s⟩
  have mat := matches_ops o s v _ (walk_post _ _ _ (trailing_walk s r)).1 (matches_initial s)
  have eq := trailing_plan_meaning o v r.msg
  have mm := mat.2; rw [eq] at mm
  let lastIdx : Index := ⟨16777215, by decide⟩
  exact good_congr o k msg _ _ _ mm (by decide) (good_step o k msg _ lastIdx h)

end TwoPermutationPrototype.PentaGrouped
