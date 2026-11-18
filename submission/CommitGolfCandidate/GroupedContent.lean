import CommitGolfCandidate.GroupedEval
import CommitGolfCandidate.QuartetCommitLeafSpill
import CommitGolfCandidate.QuartetWordBridge
import CommitGolfCandidate.TaggedPinnedBitLayout
import CommitGolfCandidate.PairLeafModel
import CommitGolfCandidate.GroupedSaltMap

/-! Memory meaning of one pair packet (pair heads). Layout: `stack/PH-DESIGN.md`. -/

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.QuartetCommit (qSource qSalt qLeaf)
open TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.RV64.PackedLeaves
open CommitGolfCandidate.Permutation.CounterSalt (coord firstLeaf input parts)
set_option maxRecDepth 18000
set_option maxHeartbeats 1800000
set_option exponentiation.threshold 2048

def replyE (o : Oracle) (m : Memory) (P : Nat) := o.permutation (packBuffer (window m (msgWord (2*P)+7)))
def stateE (o : Oracle) (m : Memory) (P : Nat) := writeWindow m (msgWord (2*P)-25) (replyWords (replyE o m P))
def replyO (o : Oracle) (m : Memory) (P : Nat) := o.permutation (packBuffer (window (stateE o m P) (msgWord (2*P+1))))
def stateO (o : Oracle) (m : Memory) (P : Nat) :=
  writeWindow (stateE o m P) (msgWord (2*P+1)-4) (replyWords (replyO o m P))
def counterState (o : Oracle) (m : Memory) (P : Nat) :=
  writeWord (stateO o m P) (qSalt 0) (wordAddress (msgWord (2*P+1)))
def generatedP (o : Oracle) (m : Memory) (P : Nat) :=
  o.permutation (packBuffer (window (counterState o m P) (qSalt 0)))
def headState (o : Oracle) (m : Memory) (P : Nat) :=
  writeWindow (counterState o m P) (msgWord (2*P+1)-15) (replyWords (generatedP o m P))
/-- Copied salts: from the prefetched registers a4..a7 at pairs 11m+10, else loaded from the head's reply. -/
def copyState (o : Oracle) (rg : Reg → Word) (m : Memory) (P : Nat) :=
  let a := stateO o m P
  if fromRegs (P%2048) then
    let b := writeWord a (msgWord (2*P+1)-15) (rg .x14)
    let c := writeWord b (msgWord (2*P+1)-14) (rg .x15)
    let d := writeWord c (msgWord (2*P+1)+8) (rg .x16)
    writeWord d (msgWord (2*P+1)+9) (rg .x17)
  else
    let b := writeWord a (msgWord (2*P+1)-15) (a (srcWord (2*P)))
    let c := writeWord b (msgWord (2*P+1)-14) (b (srcWord (2*P)+1))
    let d := writeWord c (msgWord (2*P+1)+8) (c (srcWord (2*P+1)))
    writeWord d (msgWord (2*P+1)+9) (d (srcWord (2*P+1)+1))
def saltedState (o : Oracle) (rg : Reg → Word) (m : Memory) (P : Nat) :=
  if pairHead (P%2048) then headState o m P else copyState o rg m P
def taggedE (o : Oracle) (rg : Reg → Word) (m : Memory) (P : Nat) :=
  writeWord (saltedState o rg m P) (msgWord (2*P)-6) (wordAddress (msgWord (2*P)-6))
def digestE (o : Oracle) (rg : Reg → Word) (m : Memory) (P : Nat) :=
  o.permutation (packBuffer (window (taggedE o rg m P) (msgWord (2*P)-6)))
def stateE2 (o : Oracle) (rg : Reg → Word) (m : Memory) (P : Nat) :=
  writeWindow (taggedE o rg m P) (qLeaf (2*P)) (replyWords (digestE o rg m P))
def taggedO (o : Oracle) (rg : Reg → Word) (m : Memory) (P : Nat) :=
  writeWord (stateE2 o rg m P) (msgWord (2*P+1)+7) (wordAddress (msgWord (2*P+1)+7))
def digestO (o : Oracle) (rg : Reg → Word) (m : Memory) (P : Nat) :=
  o.permutation (packBuffer (window (taggedO o rg m P) (msgWord (2*P+1)+7)))
def pairPacketMem (o : Oracle) (rg : Reg → Word) (m : Memory) (P : Nat) :=
  writeWindow (taggedO o rg m P) (qLeaf (2*P+1)) (replyWords (digestO o rg m P))

attribute [local irreducible] packBuffer writeWord writeWindow window

theorem pair_plan_meaning (o : Oracle) (v : View) (P : Nat) :
    ((pairPlan P).foldl (viewStep o) v).mem=pairPacketMem o v.regs v.mem P := by
  by_cases h : pairHead (P%2048) <;> by_cases a : prefetchA (P%2048) <;> by_cases b : P%2048%11=5 <;>
    by_cases t : fromRegs (P%2048) <;> by_cases r0 : rebase (2*(P%2048)) <;> by_cases r1 : rebase (2*(P%2048)+1) <;>
    simp [pairPlan,h,a,b,t,r0,r1,pairPacketMem,taggedO,digestO,stateE2,digestE,taggedE,
      saltedState,headState,copyState,generatedP,counterState,stateO,replyO,stateE,replyE,
      viewStep,View.reg,View.store,View.reply]

/-- The prefetch registers after pair `P`: heads 11m (m ≤ 185) load a6,a7 and heads 11m+5 load a4,a5 from their
reply's table salt 8; every other pair leaves them alone. -/
theorem pair_plan_regs (o : Oracle) (v : View) (P : Nat) :
    let w := (pairPlan P).foldl (viewStep o) v
    let O := msgWord (2*P+1)
    w.regs .x14=(if P%2048%11=5 then headState o v.mem P (O+3) else v.regs .x14) ∧
    w.regs .x15=(if P%2048%11=5 then headState o v.mem P (O+4) else v.regs .x15) ∧
    w.regs .x16=(if prefetchA (P%2048) then headState o v.mem P (O+3) else v.regs .x16) ∧
    w.regs .x17=(if prefetchA (P%2048) then headState o v.mem P (O+4) else v.regs .x17) := by
  intro w O
  by_cases h : pairHead (P%2048) <;> by_cases a : prefetchA (P%2048) <;> by_cases b : P%2048%11=5 <;>
    by_cases t : fromRegs (P%2048) <;> by_cases r0 : rebase (2*(P%2048)) <;> by_cases r1 : rebase (2*(P%2048)+1) <;>
    simp [w,O,pairPlan,h,a,b,t,r0,r1,headState,generatedP,counterState,stateO,replyO,
      stateE,replyE,viewStep,View.reg,View.store,View.reply] <;>
    first | rfl | (exfalso; unfold pairHead prefetchA fromRegs at *; omega) | skip

attribute [local semireducible] window writeWord writeWindow

private theorem msg_below_quartets (P : Nat) (limit : P<2^23) (i : Nat) : msgWord (2*P+1)+32 ≤ qLeaf i := by
  unfold msgWord qLeaf qSource; omega

theorem write_window_at (m : Memory) (a : Nat) (w : Words 25) (j : Nat) :
    writeWindow m a w j = if h : a ≤ j ∧ j<a+25 then w ⟨j-a,by omega⟩ else m j := by
  unfold writeWindow; split <;> rename_i h <;> simp [h]

theorem write_word_at (m : Memory) (a : Nat) (v : Word) (j : Nat) :
    writeWord m a v j = if j=a then v else m j := by
  unfold writeWord; rfl

/-- Memory after both first calls of pair `P`. -/
theorem stateO_at (o : Oracle) (m : Memory) (P : Nat) (w : Nat) :
    stateO o m P w =
      if h : msgWord (2*P+1)-4 ≤ w ∧ w<msgWord (2*P+1)-4+25 then replyWords (replyO o m P) ⟨w-(msgWord (2*P+1)-4),by omega⟩
      else if h' : msgWord (2*P)-25 ≤ w ∧ w<msgWord (2*P)-25+25 then replyWords (replyE o m P) ⟨w-(msgWord (2*P)-25),by omega⟩
      else m w := by
  unfold stateO stateE; rw [write_window_at,write_window_at]

/-- The salt step only writes the salt words (and, at a head, the counter word and the reply window). -/
theorem salted_eq_stateO (o : Oracle) (rg : Reg → Word) (m : Memory) (P : Nat) (w : Nat)
    (out : w<msgWord (2*P+1)-15 ∨ msgWord (2*P+1)+10 ≤ w) (key : w ≠ qSalt 0) :
    saltedState o rg m P w = stateO o m P w := by
  have lo : 544 ≤ msgWord (2*P+1) := by unfold msgWord; omega
  unfold saltedState
  split
  · unfold headState counterState; rw [write_window_at,dif_neg (by omega),write_word_at,if_neg key]
  · have h1 : w ≠ msgWord (2*P+1)+9 := by omega
    have h2 : w ≠ msgWord (2*P+1)+8 := by omega
    have h3 : w ≠ msgWord (2*P+1)-14 := by omega
    have h4 : w ≠ msgWord (2*P+1)-15 := by omega
    unfold copyState; dsimp only; split <;> simp only [write_word_at,h1,h2,h3,h4,ite_false]

/-- The even leaf's second-call window (salt words abstract). -/
theorem even_window (o : Oracle) (rg : Reg → Word) (m : Memory) (P : Nat) (limit : P<2^23) (msg : Words 32)
    (hmsg : (window m (msgWord (2*P)) : Words 32)=msg) :
    (window (taggedE o rg m P) (msgWord (2*P)-6) : Words 25)=
      evenSecondInput ⟨2*P,by change 2*P<16777216; omega⟩ (fun j => saltedState o rg m P (msgWord (2*P)+17+j.val))
        (replyWords (replyE o m P)) msg := by
  have eE : msgWord (2*P)=512+64*P := by unfold msgWord; omega
  have eO : msgWord (2*P+1)=544+64*P := by unfold msgWord; omega
  have hq : msgWord (2*P+1)+32 ≤ qSalt 0 := by unfold qSalt; omega
  funext j
  have hj := j.isLt
  unfold evenSecondInput
  simp only [window,taggedE]
  rw [write_word_at]
  split
  · rename_i z
    rw [if_pos (by omega)]; unfold evenPositionTag wordAddress; dsimp only; congr 1; omega
  · rename_i nz
    rw [if_neg (by omega)]
    split
    · rename_i lt6
      rw [salted_eq_stateO o rg m P _ (Or.inl (by omega)) (by omega),stateO_at,dif_neg (by omega),dif_pos (by omega)]
      congr 2; omega
    · split
      · rename_i n6 lt23
        rw [salted_eq_stateO o rg m P _ (Or.inl (by omega)) (by omega),stateO_at,dif_neg (by omega),dif_neg (by omega)]
        have w := congrFun hmsg ⟨j.val-6,by omega⟩
        simp only [window] at w
        rw [← w]; congr 1; omega
      · congr 1; omega

/-- The odd leaf's second-call window: the pinned layout (salt words abstract). -/
theorem odd_window (o : Oracle) (rg : Reg → Word) (m : Memory) (P : Nat) (limit : P<2^23) (msg : Words 32)
    (hmsg : (window m (msgWord (2*P+1)) : Words 32)=msg) :
    (window (taggedO o rg m P) (msgWord (2*P+1)+7) : Words 25)=
      pinnedSecondInput ⟨2*P+1,by change 2*P+1<16777216; omega⟩ (fun j => saltedState o rg m P (msgWord (2*P+1)+8+j.val))
        (replyWords (replyO o m P)) msg := by
  have eE : msgWord (2*P)=512+64*P := by unfold msgWord; omega
  have eO : msgWord (2*P+1)=544+64*P := by unfold msgWord; omega
  have hq : msgWord (2*P+1)+32 ≤ qSalt 0 := by unfold qSalt; omega
  have hl := msg_below_quartets P limit (2*P)
  funext j
  have hj := j.isLt
  unfold pinnedSecondInput
  simp only [window,taggedO,stateE2,taggedE]
  rw [write_word_at]
  split
  · rename_i z
    rw [if_pos (by omega)]; unfold pinnedPositionTag wordAddress; dsimp only; congr 1; omega
  · rename_i nz
    rw [if_neg (by omega),write_window_at,dif_neg (by omega),write_word_at,if_neg (by omega)]
    split
    · congr 1; omega
    · split
      · rename_i n3 lt14
        rw [salted_eq_stateO o rg m P _ (Or.inr (by omega)) (by omega),stateO_at,dif_pos (by omega)]
        congr 2; omega
      · rename_i n3 n14
        rw [salted_eq_stateO o rg m P _ (Or.inr (by omega)) (by omega),stateO_at,dif_neg (by omega),dif_neg (by omega)]
        have w := congrFun hmsg ⟨j.val+7,by omega⟩
        simp only [window] at w
        rw [← w]; congr 1; omega

end TwoPermutationPrototype.Grouped
