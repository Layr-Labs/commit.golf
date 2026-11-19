import CommitGolfCandidate.GroupedContent

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.RV64.PackedLeaves
open CommitGolfCandidate.Permutation.CounterSalt (coord firstLeaf input parts salts)
set_option maxRecDepth 18000
set_option maxHeartbeats 1800000
set_option exponentiation.threshold 2048

private theorem window_outside {n : Nat} (m : Memory) (a : Nat) (ws : Words n) (w : Nat)
    (h : w<a ∨ a+n≤w) : writeWindow m a ws w=m w := by unfold writeWindow;apply dif_neg;omega

theorem packet_frame (o : Oracle) (m : Memory) (i w : Nat) (h : i<16777216)
    (counter : w≠keyWord) (src : w<msgWord i-15 ∨ msgWord i+21≤w)
    (dst : w<leafDest i ∨ leafDest i+25≤w) : packetMem o m i w=m w := by
  have sm : 15≤msgWord i := by unfold msgWord;omega
  have src1 : ¬(msgWord i-4≤w ∧ w<msgWord i-4+25) := by omega
  have src2 : ¬(msgWord i-15≤w ∧ w<msgWord i-15+25) := by omega
  rw [packetMem,window_outside _ _ _ _ dst]
  unfold preSecond
  split
  · simp only [directState,seededMem,firstState,writeWord,writeWindow,src1,src2,counter,
      show w≠msgWord i+7 by omega,ite_false,dite_false]
  · simp only [laterState,firstState,writeWord,writeWindow,src1,show w≠msgWord i+7 by omega,
      show w≠msgWord i+8 by omega,show w≠msgWord i+9 by omega,ite_false,dite_false]

theorem new_digest (o : Oracle) (m : Memory) (i : Nat) : window (packetMem o m i) (leafDest i) =
    lowDigest (replyWords (digestReply o m i)) := by
  funext k
  have h : leafDest i≤leafDest i+k.val ∧ leafDest i+k.val<leafDest i+25 := by have := k.isLt;omega
  simp [window,packetMem,writeWindow,h,lowDigest]

private theorem write_word_comm_window {n : Nat} (m : Memory) (a c : Nat) (vals : Words n) (v : Word)
    (apart : c<a ∨ a+n≤c) :
    writeWord (writeWindow m a vals) c v=writeWindow (writeWord m c v) a vals := by
  funext w;by_cases eq : w=c
  · subst w;simp [writeWord,writeWindow,show ¬(a≤c ∧ c<a+n) by omega]
  · unfold writeWord writeWindow;split <;> simp_all

theorem direct_as_window (o : Oracle) (m : Memory) (i : Nat) (hi : i<16777216) :
    let b:=msgWord i-15
    directState o m i=writeWord (Counter.directMemory m b (wordAddress (msgWord i+7))
      (replyWords (firstReply o m i)) (replyWords (generated o m i))) keyWord (wordAddress (msgWord i)) := by
  have bs : 15≤msgWord i := by unfold msgWord;omega
  have sep : msgWord i+21<keyWord := by unfold msgWord keyWord leafSalt;omega
  dsimp only;unfold directState seededMem firstState Counter.directMemory
  rw [←write_word_comm_window _ (msgWord i-15) keyWord _ _ (Or.inr (by omega)),
    show msgWord i-15+11=msgWord i-4 by omega,show msgWord i-15+22=msgWord i+7 by omega]
  funext w;by_cases hit : w=keyWord <;> by_cases tag : w=msgWord i+7 <;> simp_all [writeWord] <;> omega

private theorem near_direct (o : Oracle) (m : Memory) (i a n : Nat) (hi : i<16777216)
    (sep : a+n≤keyWord) : (window (directState o m i) a : Words n)=
      window (Counter.directMemory m (msgWord i-15) (wordAddress (msgWord i+7))
        (replyWords (firstReply o m i)) (replyWords (generated o m i))) a := by
  rw [direct_as_window _ _ _ hi]
  funext k;have := k.isLt; simp only [window,writeWord,show a+k.val≠keyWord by omega,ite_false]

theorem direct_argument (o : Oracle) (m : Memory) (i : Nat) (hi : i<16777216) :
    window (directState o m i) (msgWord i+7) =
      pinnedWords (wordAddress (msgWord i+7)) (Counter.slice (replyWords (generated o m i)) 0)
        (replyWords (firstReply o m i)) (window m (msgWord i)) := by
  have b : 15≤msgWord i := by unfold msgWord;omega
  rw [near_direct _ _ _ _ _ hi (by unfold msgWord keyWord leafSalt;omega)]
  simpa only [show msgWord i-15+22=msgWord i+7 by omega,show msgWord i-15+15=msgWord i by omega] using
    Counter.direct_second m (msgWord i-15) (wordAddress (msgWord i+7)) (replyWords (firstReply o m i)) (replyWords (generated o m i))

theorem regular_argument (o : Oracle) (m : Memory) (i : Nat) (different : rank i≠0) :
    window (laterState o m i) (msgWord i+7)=
      pinnedWords (wordAddress (msgWord i+7)) (window m (sourceWord i))
        (replyWords (firstReply o m i)) (window m (msgWord i)) := by
  rw [later_eq o m i different]
  simpa only [firstState,show leafStart i+1=msgWord i-4 by unfold leafStart msgWord;omega,
    show leafStart i+12=msgWord i+7 by unfold leafStart msgWord;omega,
    show leafStart i+5=msgWord i by unfold leafStart msgWord;omega] using
    pinned_second_window m (leafStart i) (wordAddress (msgWord i+7)) (window m (sourceWord i)) (replyWords (firstReply o m i))

theorem keep_direct (o : Oracle) (m : Memory) (i : Nat) (hi : i<16777216) (head : rank i=0)
    (j : Fin 11) (nz : j.val≠0) :
    window (packetMem o m i) (groupBuffer i+2*(j.val-1))=Counter.slice (replyWords (generated o m i)) j := by
  have jh := j.isLt
  have b : 15≤msgWord i := by unfold msgWord;omega
  have geom : groupBuffer i=msgWord i-15 := by simp [groupBuffer,head]
  rw [geom]
  let a := msgWord i-15+2*(j.val-1)
  have below : a+2≤leafDest i := by dsimp [a,msgWord,leafDest];omega
  have step : (window (packetMem o m i) a : Words 2) = window (directState o m i) a := by
    funext k;rw [window,packetMem,window_outside _ _ _ _ (Or.inl (by have:=k.isLt;omega)),preSecond,if_pos head];rfl
  rw [step,near_direct _ _ _ _ _ hi (by dsimp [a,msgWord,keyWord,leafSalt];omega)]
  exact Counter.retained_slices m (msgWord i-15) (wordAddress (msgWord i+7)) (replyWords (firstReply o m i)) (replyWords (generated o m i)) j nz

end TwoPermutationPrototype.Grouped
