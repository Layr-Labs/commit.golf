import CommitGolfCandidate.Layout2FusedStep
import CommitGolfCandidate.Layout2Run
import CommitGolfCandidate.GroupOpenTableInit
import CommitGolfCandidate.GroupOpenInitial

/-! Fused opener (Layout 2 V2 Increment 4b): the loop over all `k` positions. Ordinal `j` runs in phase `j % 4`; one
iteration is the former first-pass position (head, inverse call into the record block, chained salt generator, salt to
the block) followed by the former record (the phase writer and the tail). The invariant `Ready` holds between
positions; `loop_run` executes the loop, `loop_cycles_bound`/`loop_calls_bound` count it, and under a fixed oracle
`fixed_post`/`seen_loop` give the record blocks: the written dwords (`Written`, V1's writer dwords) and the retained
bytes (`RSeen`: the linked salt and the inverse quartet reply). `exit_done` runs the exit stub to the cap stage. -/
namespace TwoPermutationPrototype.GroupedOpening.Layout2F
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.GroupedOpening TwoPermutationPrototype.GroupedOpening.Layout2
open CommitGolfCandidate.Layout2Phase (stride writerCarry recordSource)
open TwoPermutationPrototype.GroupedOpening.Layout2V2 (linkedSalts card_le)
open Opening (sortedIndex groupsBefore)
open TwoPermutationPrototype.Sampling (saltWords)
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-- Where ordinal `j` starts: its phase's first word, or the exit stub of the last phase after the last position. -/
def loopPC (p : Positions) (j : Nat) := if j=p.card then address (fexitWord ((j+3)%4)) else address (fphaseWord (j%4))

/-- The written dwords of the first `n` record blocks hold V1's writer dwords. -/
def Written (L : MachineState) (p : Positions) (s : MachineState) (n : Nat) : Prop :=
  ∀ a<n, ∀ b<stride (a%4), Layout2Phase2.written ((posAt p a).val%4) (b/8)=true →
    s.getByte (BitVec.ofNat 64 (destOf a+b))=Layout2Phase2.writtenByte (a%4) (srcAt L p a) (carryAt L p a) b

structure Ready (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (key : BitVec 192)
    (s : MachineState) (j : Nat) : Prop extends Regs s j (p.card-j) where
  pc : s.pc=loopPC p j
  dest : s.getReg .x21=BitVec.ofNat 64 (destOf j)
  carry : j%4≠0 → s.getReg .x4=carryAt (actual.initialState .opening (td,p)) p j
  input : SameOpeningInput (actual.initialState .opening (td,p)) s
  table : TableAt s
  keyFrame : KeyWords s key
  marked : ByteMarks p s j
  bytes : Written (actual.initialState .opening (td,p)) p s j

theorem input_of_ready (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (key : BitVec 192)
    (s : MachineState) (j : Nat) (r : Ready td p key s j) (hj : j<p.card) :
    Entry s (posAt p j) j (p.card-j) := by
  have card := card_le p
  refine ⟨r.toRegs,by simpa [loopPC,Nat.ne_of_lt hj,fphaseWord] using r.pc,r.dest,?_,?_,r.table⟩
  · rw [index_at]; exact index_word actual actual_layout td p s r.input j hj
  · unfold indexAt;apply Opening.aligned_access
    · omega
    · change _≤2^36;omega

theorem mark_word (i : Index) : alignToDword (markAt i)=wordAddress ((Opening.markBase+(256+i.val/65536))/8) := by
  have ix : i.val<16777216 := i.isLt
  unfold markAt; rw [table_align_eq _ (by unfold Opening.markBase; omega)]; unfold wordAddress; congr 1
  unfold Opening.markBase; omega

theorem not_mark (i : Index) (w : Nat) (hw : w<2^33) (h : w≠(Opening.markBase+(256+i.val/65536))/8) :
    wordAddress w≠alignToDword (markAt i) := by
  have ix : i.val<16777216 := i.isLt
  rw [mark_word]; intro e
  exact h (wordAddress_injective_of_bound (by omega) (by unfold Opening.markBase; omega) e)

theorem next_ready (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (key : BitVec 192)
    (s t : MachineState) (j : Nat) (r : Ready td p key s j) (hj : j<p.card)
    (hit : t∈support (perTrace s (posAt p j) j (p.card-j))) : Ready td p key t (j+1) := by
  have card := card_le p
  let L := actual.initialState .opening (td,p)
  let i := posAt p j
  have ix : i.val<16777216 := i.isLt
  have inp := input_of_ready td p key s j r hj
  obtain ⟨regs,pc,dst,cry,⟨W,wmem,wframe,wbytes⟩,_⟩ := trace_post s i j (p.card-j) (by omega) (by omega) inp t hit
  have pb : proofBase=13824430176 := rfl
  have tb : trapdoorBase=4294971424 := rfl
  have room := block_room j (by omega)
  have sw := stride_words (j%4)
  have g : 256+i.val/65536<512 := by omega
  have mk : markAt i=BitVec.ofNat 64 (Opening.markBase+(256+i.val/65536)) := rfl
  have viewT (w : Nat) (fit : w<2^33) (away : ¬Writes j w) (nm : w≠(Opening.markBase+(256+i.val/65536))/8) :
      memoryView t w=memoryView s w := by
    change t.getMem (wordAddress w)=_
    rw [mem_reads t _ wmem, set_byte_mem _ _ _ _ (not_mark i w fit nm)]
    exact wframe w fit away
  have srcEq : ∀ k<560, recordSource s (quadAddress i.val) i.val k=srcAt L p j k :=
    fun k hk => source_from_input L s r.input _ ix k hk
  refine ⟨by simpa only [show p.card-j-1=p.card-(j+1) by omega] using regs,?_,dst,?_,?_,?_,?_,?_,?_⟩
  · rw [pc]; unfold finalPC loopPC
    by_cases h : j+1=p.card
    · rw [if_pos (by omega), if_pos h, show (j+1+3)%4=j%4 by omega]
    · rw [if_neg (by omega), if_neg h]
  · intro _
    rw [cry]
    show _=writerCarry (j%4) (srcAt L p j) (carryAt L p j)
    rw [writer_carry_congr srcEq]
    by_cases z : j%4=0
    · rw [z]; exact writer_carry_phase0 _ _ _
    · rw [r.carry z]
  · intro a lo hi al
    have fa : a<2^64 := by omega
    rw [mem_reads t _ wmem, mk, set_byte_mem _ _ _ _ (mark_key_ne _ a g lo fa)]
    have ea : BitVec.ofNat 64 a=wordAddress (a/8) := by unfold wordAddress; congr 1; omega
    rw [ea]
    change memoryView W (a/8)=_
    rw [wframe (a/8) (by omega) (by rintro (h|h|h) <;> omega)]
    change s.getMem (wordAddress (a/8))=_
    rw [← ea]; exact r.input a lo hi al
  · intro e he h hh
    rw [viewT _ (by simp only [tableWord]; omega) (by rintro (x|x|x) <;> simp only [tableWord] at x <;> omega)
      (by simp only [tableWord]; unfold Opening.markBase; omega)]
    exact r.table e he h hh
  · intro k lo hi
    rw [viewT _ (by omega) (by rintro (x|x|x) <;> omega) (by unfold Opening.markBase; omega)]
    exact r.keyFrame k lo hi
  · intro i' hi'
    have fm : Opening.markBase+256+i'<2^64 := by unfold Opening.markBase; omega
    rw [byte_reads t _ wmem, Layout2.set_byte_read, Opening.groups_before_next p j hj, cap_group_pos p j hj]
    by_cases same : i'=(posAt p j).val/65536
    · subst same
      rw [if_pos (by rw [mk, Nat.add_assoc])]
      simp [Sampling.capIsMarked]
    · have ne : BitVec.ofNat 64 (Opening.markBase+256+i') ≠ markAt i := by
        rw [mk]; intro e; have := congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fm,
          Nat.mod_eq_of_lt (by unfold Opening.markBase; omega)] at this
        omega
      rw [if_neg ne]
      have kept : W.getByte (BitVec.ofNat 64 (Opening.markBase+256+i'))=s.getByte (BitVec.ofNat 64 (Opening.markBase+256+i')) :=
        byte_of_view _ (by unfold Opening.markBase; omega)
          (wframe _ (by unfold Opening.markBase; omega) (by rintro (h|h|h) <;> unfold Opening.markBase at h <;> omega))
      rw [kept, r.marked i' hi']
      have d1 : ¬(256+(posAt p j).val/65536=256+i') := by omega
      have d3 : (256+(posAt p j).val/65536 == 256+i')=false := beq_false_of_ne d1
      simp [Sampling.capIsMarked, List.any_append, d3]
  · intro a ha b hb hw
    have da := dest_bound a
    have fx : destOf a+b<2^64 := by omega
    have above : proofBase ≤ destOf a+b := by omega
    rw [byte_reads t _ wmem, mk, byte_after_mark W _ _ g above fx]
    by_cases older : a<j
    · have mono := dest_mono a j older
      have bm := block_mul j
      rw [byte_of_view _ (by omega) (wframe _ (by omega) (by rintro (h|h|h) <;> omega))]
      exact r.bytes a older b hb hw
    · have same : a=j := by omega
      subst same
      rw [wbytes b hb hw, written_byte_congr' srcEq]
      by_cases z : a%4=0
      · rw [z]; exact written_byte_phase0 _ _ _ _
      · rw [r.carry z]

/-! ### The loop -/

def loopTrace (p : Positions) : Nat → Nat → MachineState → OracleComp World MachineState
  | 0,_,s => pure s
  | n+1,j,s => do let t ← perTrace s (posAt p j) j (p.card-j);loopTrace p n (j+1) t

def loopSteps (p : Positions) : Nat → Nat → Nat
  | 0,_ => 0
  | n+1,j => perSteps (posAt p j) j (p.card-j)+loopSteps p n (j+1)

def loopCycles (p : Positions) : Nat → Nat → Nat
  | 0,_ => 0
  | n+1,j => perCycles (posAt p j) j (p.card-j)+loopCycles p n (j+1)

def loopCalls (p : Positions) : Nat → Nat → Nat
  | 0,_ => 0
  | n+1,j => perCalls (posAt p j)+loopCalls p n (j+1)

theorem loop_post (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (key : BitVec 192)
    (s t : MachineState) (n j : Nat) (r : Ready td p key s j) (bound : j+n≤p.card)
    (hit : t∈support (loopTrace p n j s)) : Ready td p key t (j+n) := by
  induction n generalizing j s with
  | zero => simp only [loopTrace,support_pure,Set.mem_singleton_iff] at hit;subst t;exact r
  | succ n ih =>
    rw [loopTrace,mem_support_bind_iff] at hit;obtain ⟨u,one,rest⟩:=hit
    exact (show j+(n+1)=(j+1)+n by omega) ▸ ih _ _ (next_ready _ _ _ _ _ _ r (by omega) one) (by omega) rest

theorem loop_run (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (key : BitVec 192)
    (s : MachineState) (n j fuel : Nat) (r : Ready td p key s j) (bound : j+n≤p.card) :
    execute openingImage (loopSteps p n j+fuel) s true=(do
      let t ← loopTrace p n j s;let z ← execute openingImage fuel t true
      return z.charge (loopCycles p n j) (loopCalls p n j)) := by
  induction n generalizing j s with
  | zero => simp [loopSteps,loopTrace,loopCycles,loopCalls,Execution.charge]
  | succ n ih =>
    have card := card_le p
    rw [loopSteps,Nat.add_assoc,per_run s (posAt p j) j _ _ (by omega) (by omega)
      (input_of_ready _ _ _ _ _ r (by omega))]
    simp only [loopTrace,bind_assoc]
    apply bind_congr_of_forall_mem_support;intro u hit
    rw [ih u (j+1) (next_ready _ _ _ _ _ _ r (by omega) hit) (by omega)]
    simp only [bind_assoc,pure_bind]
    apply bind_congr;intro t;apply bind_congr;intro z;apply congrArg (fun x : Execution => (pure x : OracleComp World Execution))
    cases z;simp [Execution.charge,loopCycles,loopCalls] <;> omega

/-! ### Counts -/

theorem chain_cycles_le (i : Index) : chainCycles i≤280 := by
  have := links_lt i; unfold chainCycles chainSteps chainCalls; omega
theorem chain_calls_le (i : Index) : chainCalls i≤34 := by
  have := links_lt i; unfold chainCalls; omega

/-- The cycle bound of ordinal `j` of `k` positions (the chain at its 280-cycle maximum). -/
def fcost (k j : Nat) : Nat := 308+(Layout2Writer3.writerLen (j%4)+tailCost (j%4) (decide (k-j=1)))

def costSum (k : Nat) : Nat → Nat → Nat
  | 0,_ => 0
  | n+1,j => fcost k j+costSum k n (j+1)

theorem cost_128 : costSum 128 128 0=65151 := by decide

theorem loop_cycles_bound (p : Positions) (n j : Nat) : loopCycles p n j≤costSum p.card n j := by
  induction n generalizing j with
  | zero => simp [loopCycles,costSum]
  | succ n ih =>
    have c := chain_cycles_le (posAt p j)
    have h := ih (j+1)
    simp only [loopCycles,costSum,perCycles,fcost,recLen]
    omega

theorem loop_calls_bound (p : Positions) (n j : Nat) : loopCalls p n j≤35*n := by
  induction n generalizing j with
  | zero => simp [loopCalls]
  | succ n ih => have := chain_calls_le (posAt p j); have := ih (j+1); simp only [loopCalls, perCalls]; omega

theorem per_steps_le (i : Index) (ord left : Nat) : perSteps i ord left≤266 := by
  have := links_lt i
  have w : Layout2Writer3.writerLen (ord%4) ≤ 196 := by
    unfold Layout2Writer3.writerLen Layout2Phase2.bodyLen; split_ifs <;> omega
  have t : tailCost (ord%4) (decide (left=1)) ≤ 7 := by unfold tailCost; split_ifs <;> omega
  unfold perSteps chainSteps recLen; omega

theorem loop_steps_bound (p : Positions) (n j : Nat) : loopSteps p n j≤266*n := by
  induction n generalizing j with
  | zero => simp [loopSteps]
  | succ n ih => have := per_steps_le (posAt p j) j (p.card-j); have := ih (j+1); simp only [loopSteps]; omega

/-! ### Fixed oracle -/

noncomputable def fixedLoop (o : Oracle) (p : Positions) (k : BitVec 192) : Nat → Nat → MachineState → MachineState
  | 0,_,s=>s
  | n+1,j,s=>fixedLoop o p k n (j+1) (fixedOne o s (posAt p j) j (p.card-j))

theorem next_fixed (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (k : BitVec 192)
    (s : MachineState) (j : Nat) (r : Ready td p k s j) (hj : j<p.card) :
    Ready td p k (fixedOne o s (posAt p j) j (p.card-j)) (j+1) :=
  next_ready td p k s _ j r hj (fixed_mem o k s _ j _ (input_of_ready td p k s j r hj) (by have := card_le p; omega)
    r.keyFrame)

theorem loop_fixed (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (k : BitVec 192)
    (s : MachineState) (j n : Nat) (bound : j+n≤p.card) (r : Ready td p k s j) :
    o.run (loopTrace p n j s)=pure (fixedLoop o p k n j s,loopCalls p n j) := by
  induction n generalizing j s with
  | zero => exact oracle_run_pure ..
  | succ n ih =>
    have one := trace_fixed o k s (posAt p j) j (p.card-j) (input_of_ready td p k s j r (by omega))
      (by have := card_le p; omega) r.keyFrame
    rw [loopTrace,oracle_run_bind,one,pure_bind];dsimp only
    rw [ih _ (j+1) (by omega) (next_fixed o td p k s j r (by omega))]
    simp [fixedLoop,loopCalls,Nat.add_comm]

theorem fixed_post (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (k : BitVec 192)
    (s : MachineState) (j n : Nat) (bound : j+n≤p.card) (r : Ready td p k s j) :
    Ready td p k (fixedLoop o p k n j s) (j+n) := by
  induction n generalizing j s with
  | zero => simpa [fixedLoop] using r
  | succ n ih =>
    simpa only [fixedLoop,show j+(n+1)=(j+1)+n by omega] using ih _ (j+1) (by omega) (next_fixed o td p k s j r (by omega))

/-- Word `d < 25` of record `a`'s block that the writer keeps: the linked salt (`d < 2`) or the inverse quartet
reply. -/
noncomputable def retainedWord (o : Oracle) (k : BitVec 192) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions)
    (a d : Nat) : Word :=
  if d<2 then saltWords (linkedSalts o k (posAt p a)) ⟨d%2,Nat.mod_lt _ (by decide)⟩
  else replyWords (o.permutation.symm (groupReply td ((posAt p a).val/4))) ⟨d%25,Nat.mod_lt _ (by decide)⟩

/-- The retained bytes of the first `n` record blocks. -/
def RSeen (o : Oracle) (k : BitVec 192) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions)
    (s : MachineState) (n : Nat) : Prop :=
  ∀ a<n, ∀ b<stride (a%4), Layout2Phase2.written ((posAt p a).val%4) (b/8)=false →
    s.getByte (BitVec.ofNat 64 (destOf a+b))=(retainedWord o k td p a (b/8)).extractLsb' (8*(b%8)) 8

theorem byte_view (s : MachineState) (w r : Nat) (hr : r<8) (hw : w<2^33) :
    s.getByte (BitVec.ofNat 64 (8*w+r))=(memoryView s w).extractLsb' (8*r) 8 := by
  have fx : 8*w+r<2^64 := by omega
  unfold MachineState.getByte
  rw [table_align_eq _ fx, table_offset_nat _ fx, show 8*w+r-(8*w+r)%8=8*w by omega, show (8*w+r)%8=r by omega]
  change extractByte (s.getMem (BitVec.ofNat 64 (8*w))) r=(s.getMem (BitVec.ofNat 64 (8*w))).extractLsb' (8*r) 8
  apply BitVec.eq_of_getLsbD_eq;intro i hi
  simp [extractByte, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb', Nat.mul_comm]

/-- The reply window of a quartet: the trapdoor's reply, untouched by the loop. -/
theorem reply_window (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (s : MachineState)
    (input : SameOpeningInput (actual.initialState .opening (td,p)) s) (q : Nat) (hq : q<4194304) :
    packBuffer (window (memoryView s) (replyWord q))=groupReply td q := by
  have off : 8*replyWord q=trapdoorBase+groupReplyOffset q := by
    unfold replyWord groupReplyOffset blockWord trapdoorBase LENGTH LOG_LENGTH; split <;> omega
  have hw : (window (memoryView s) (replyWord q) : Words 25)=
      window (memoryView (actual.initialState .opening (td,p))) (replyWord q) := by
    funext w; unfold window
    have := w.isLt
    have tb : trapdoorBase=4294971424 := rfl
    have pb : proofBase=13824430176 := rfl
    have r0 : 603980288 ≤ replyWord q ∧ replyWord q+25 ≤ 1140851204 := by
      unfold replyWord blockWord; omega
    change s.getMem (BitVec.ofNat 64 (8*(replyWord q+w.val)))=_
    exact input _ (by omega) (by omega) (by omega)
  rw [hw,←read_permutation_window,off]
  exact input_trapdoor_slice actual actual_layout td p _ 200
    (by change _≤5100273664; unfold groupReplyOffset LENGTH LOG_LENGTH; split <;> omega)

theorem next_seen (o : Oracle) (k : BitVec 192) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions)
    (s : MachineState) (j : Nat) (hj : j<p.card) (r : Ready td p k s j) (old : RSeen o k td p s j) :
    RSeen o k td p (fixedOne o s (posAt p j) j (p.card-j)) (j+1) := by
  have card := card_le p
  have ix : (posAt p j).val<16777216:=(posAt p j).isLt
  have hjb : j ≤ 16777216 := by omega
  have inp:=input_of_ready td p k s j r hj
  have mem := fixed_mem o k s (posAt p j) j (p.card-j) inp hjb r.keyFrame
  have post := trace_post s (posAt p j) j (p.card-j) (by omega) (by omega) inp _ mem
  -- the record part of the fixed outcome
  have ent := headed_entry s (posAt p j) j (p.card-j) inp hjb (fixedInverse o s (posAt p j))
  have hk : KeyWords (fixedHead o s (posAt p j) j) k :=
    head_keys s (posAt p j) j (p.card-j) inp hjb (fixedInverse o s (posAt p j)) k r.keyFrame
  have cm : chainState o (fixedHead o s (posAt p j) j) (posAt p j) (j%4) ∈
      support (chainTrace (fixedHead o s (posAt p j) j) (posAt p j) (j%4)) :=
    chain_state_support o k (fixedHead o s (posAt p j) j) (posAt p j) _ ent.1 hk
  obtain ⟨tpc,t28,t6,_,_,t18,_,_⟩ := chain_regs s (posAt p j) j (p.card-j) inp hjb (fixedInverse o s (posAt p j)) _ cm
  obtain ⟨tregs,t21,_⟩ := chain_entry_regs s (posAt p j) j (p.card-j) inp hjb (fixedInverse o s (posAt p j)) _ cm
  obtain ⟨_,_,_,_,_,_,⟨W,wmem,_,_,wret⟩⟩ :=
    finish_facts _ (posAt p j) j (p.card-j) (by omega) (by omega) tpc tregs t28 t21 t6 t18
  obtain ⟨fsalt,freply⟩ := fixed_salt_state o k s (posAt p j) j (p.card-j) inp hjb r.keyFrame
  have room := block_room j hjb
  have g : 256+(posAt p j).val/65536<512 := by omega
  have mk : markAt (posAt p j)=BitVec.ofNat 64 (Opening.markBase+(256+(posAt p j).val/65536)) := rfl
  intro a ha b hb hw
  have da := dest_bound a
  have fx : destOf a+b<2^64 := by omega
  by_cases older : a<j
  · have mono := dest_mono a j older
    rw [post.older _ (by omega) (by omega)]
    exact old a older b hb hw
  · have same : a=j := by omega
    subst same
    have y536 : b<536 := by unfold stride at hb; split at hb <;> omega
    have d25 : b/8<25 := by
      by_contra h
      have : Layout2Phase2.written ((posAt p a).val%4) (b/8)=true := by
        unfold Layout2Phase2.written; simp; omega
      rw [this] at hw; cases hw
    show (finish (chainState o (fixedHead o s (posAt p a) a) (posAt p a) (a%4)) a (p.card-a)).getByte _=_
    rw [byte_reads _ _ wmem, mk, byte_after_mark W _ _ g (by omega) fx, wret b hb hw]
    have bm := block_mul a
    rw [show destOf a+b=8*(blockW a+b/8)+b%8 by omega, byte_view _ _ _ (by omega) (by omega)]
    unfold retainedWord
    by_cases two : b/8<2
    · rw [if_pos two, fsalt ⟨b/8,two⟩]
      congr 2; apply Fin.ext; simp; omega
    · rw [if_neg two, freply (b/8) d25 (by omega), fixedInverse, inverseQuery,
        reply_window td p s r.input _ (by omega)]
      congr 2; apply Fin.ext; simp; omega

theorem seen_loop (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (k : BitVec 192)
    (s : MachineState) (j n : Nat) (b : j+n≤p.card) (r : Ready td p k s j) (seen : RSeen o k td p s j) :
    RSeen o k td p (fixedLoop o p k n j s) (j+n) := by
  induction n generalizing s j with
  | zero => simpa [fixedLoop] using seen
  | succ n ih =>
    simpa only [fixedLoop,show j+(n+1)=(j+1)+n by omega] using ih _ (j+1) (by omega)
      (next_fixed o td p k s j r (by omega)) (next_seen o k td p s j (by omega) r seen)

theorem rseen_zero (o : Oracle) (k : BitVec 192) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions)
    (s : MachineState) : RSeen o k td p s 0 := fun _ h => absurd h (Nat.not_lt_zero _)

/-! ### The exit stub, to the cap stage -/

theorem exit_done (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (key : BitVec 192) (s pass : MachineState)
    (r : Ready td p key s p.card) (positive : 0<p.card)
    (retained : ∀ j<p.card, ∀ b<stride (j%4), Layout2Phase2.written ((posAt p j).val%4) (b/8)=false →
      s.getByte (BitVec.ofNat 64 (destOf j+b))=pass.getByte (BitVec.ofNat 64 (destOf j+b))) :
    ∃ lower, RunsOpeningBlock s lower (exitCost ((p.card+3)%4)) ∧ L2Done actual td p pass lower := by
  have card := card_bound p
  have hp : (p.card+3)%4<4 := Nat.mod_lt _ (by decide)
  have bound := dest_bound p.card
  have pb : proofBase=13824430176 := by decide
  have mem : MEMORY_BYTES=68719476736 := rfl
  have pcE : s.pc=address (fexitWord ((p.card+3)%4)) := by simpa [loopPC] using r.pc
  obtain ⟨r3, pc3, x21, flushed, bytes3, mem3, regs3⟩ := exit_step ((p.card+3)%4) hp s (destOf p.card) (s.getReg .x4)
    pcE r.dest (dest_aligned p.card) (by omega) rfl
  let lower := walkRows s (fexitRows ((p.card+3)%4))
  have kr (q : Reg) (a : q ≠ .x21) (b : q ≠ .x4) : lower.getReg q=s.getReg q := regs3 q a b
  have far (x : Nat) (h : x<proofBase) : lower.getMem (BitVec.ofNat 64 x)=s.getMem (BitVec.ofNat 64 x) :=
    mem3 _ (ofNat_ne _ _ (by omega) (by omega))
  have rg := r.toRegs
  refine ⟨lower, r3, ⟨pc3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact (kr .x9 (by decide) (by decide)).trans rg.heap
  · rw [kr .x8 (by decide) (by decide), rg.index, index_at]
  · rw [kr .x22 (by decide) (by decide), rg.salt]; rfl
  · rw [x21, dest_flush p.card positive]
  · rw [kr .x19 (by decide) (by decide), rg.leaves]; rfl
  · exact (kr .x24 (by decide) (by decide)).trans rg.slots
  · rw [kr .x17 (by decide) (by decide), rg.endReg, index_at]; congr 2; omega
  · rw [kr .x26 (by decide) (by decide), rg.base]; rfl
  · rw [kr .x23 (by decide) (by decide), rg.mark]; rfl
  · exact (kr .x25 (by decide) (by decide)).trans rg.capHeap
  · rw [kr .x27 (by decide) (by decide), rg.capLeaves]; rfl
  · exact (kr .x20 (by decide) (by decide)).trans rg.start
  · intro a lo hi al
    exact (far a hi).trans (r.input a lo hi al)
  · intro i hi
    have mk : Opening.markBase+256+i<proofBase := by unfold Opening.markBase; omega
    rw [bytes3 _ (by unfold Opening.markBase; omega) (Or.inl (by omega))]
    exact r.marked i hi
  · intro j hj b hb
    have mono := dest_mono j p.card hj
    rw [bytes3 _ (by omega) (Or.inl (by omega))]
    unfold v2Byte
    by_cases hw : Layout2Phase2.written ((posAt p j).val%4) (b/8)=true
    · rw [if_pos hw]; exact r.bytes j hj b hb hw
    · rw [if_neg hw]; exact retained j hj b hb (by simpa using hw)
  · intro b hb
    rw [flushed b hb]
    by_cases z : p.card%4=0
    · exfalso
      have : (p.card+3)%4=3 := by omega
      rw [this] at hb
      unfold flushLen at hb
      simp at hb
    · rw [r.carry z]

end TwoPermutationPrototype.GroupedOpening.Layout2F
