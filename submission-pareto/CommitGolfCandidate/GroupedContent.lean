import CommitGolfCandidate.GroupedEval
import CommitGolfCandidate.QuartetCommitLeafSpill
import CommitGolfCandidate.QuartetWordBridge
import CommitGolfCandidate.TaggedPinnedBitLayout

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.QuartetCommit (qSource qSalt qLeaf)
open TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.RV64.PackedLeaves
open CommitGolfCandidate.Permutation.CounterSalt (coord firstLeaf input parts)
set_option maxRecDepth 18000
set_option maxHeartbeats 1800000
set_option exponentiation.threshold 2048

def firstReply (o : Oracle) (m : Memory) (i : Nat) := o.permutation (packBuffer (window m (msgWord i)))
def firstState (o : Oracle) (m : Memory) (i : Nat) :=
  writeWindow m (msgWord i-4) (replyWords (firstReply o m i))

def seededMem (o : Oracle) (m : Memory) (i : Nat) :=
  writeWord (firstState o m i) (qSalt 0) (wordAddress (msgWord i))
def generated (o : Oracle) (m : Memory) (i : Nat) :=
  o.permutation (packBuffer (window (seededMem o m i) (qSalt 0)))
def directState (o : Oracle) (m : Memory) (i : Nat) :=
  writeWord (writeWindow (seededMem o m i) (msgWord i-15) (replyWords (generated o m i)))
    (msgWord i+7) (wordAddress (msgWord i+7))

def laterState (o : Oracle) (m : Memory) (i : Nat) :=
  let a := firstState o m i
  let b := writeWord a (msgWord i+7) (wordAddress (msgWord i+7))
  let c := writeWord b (msgWord i+8) (b (sourceWord i))
  writeWord c (msgWord i+9) (c (sourceWord i+1))

def preSecond (o : Oracle) (m : Memory) (i : Nat) :=
  if rank i=0 then directState o m i else laterState o m i

def digestReply (o : Oracle) (m : Memory) (i : Nat) :=
  o.permutation (packBuffer (window (preSecond o m i) (msgWord i+7)))

def packetMem (o : Oracle) (m : Memory) (i : Nat) :=
  writeWindow (preSecond o m i) (qLeaf i) (replyWords (digestReply o m i))

attribute [local irreducible] packBuffer writeWord writeWindow window

theorem plan_meaning (o : Oracle) (v : View) (i : Nat) (inputReg : v.regs .x10=wordAddress (msgWord i)) :
    ((plan i).foldl (viewStep o) v).mem=packetMem o v.mem i := by
  by_cases d : rank i=0 <;> by_cases p : pairPos i=0 <;> by_cases shift : i%32=31 <;>
    simp [plan,within_rank,within_pair,p,d,shift,packetMem,digestReply,preSecond,directState,laterState,seededMem,
      generated,firstReply,firstState,viewStep,View.reg,View.store,View.reply,inputReg]

theorem coordinate_first (i : Index) : firstLeaf (coord i).1=i.val-rank i.val := by
  unfold firstLeaf coord rank
  dsimp only
  have small : i.val%2048/11<187 := by omega
  rw [show (187*(i.val/2048)+i.val%2048/11)/187=i.val/2048 by omega,
    show (187*(i.val/2048)+i.val%2048/11)%187=i.val%2048/11 by omega]
  omega

theorem reply_pack (v : BitVec 1600) : packBuffer (replyWords v)=v := by
  apply BitVec.eq_of_getLsbD_eq;intro k hk
  let j : Fin 25 := ⟨k/64,by omega⟩
  have h:=congrArg (fun w : BitVec 64 => w.getLsbD (k%64)) (packed_word (replyWords v) j)
  have b : k%64<64 := by omega
  unfold replyWords at h
  dsimp only [j] at h
  change ((packBuffer _).extractLsb' (64*(k/64)) 64).getLsbD (k%64) =
    (v.extractLsb' (64*(k/64)) 64).getLsbD (k%64) at h
  unfold replyWords
  simpa only [BitVec.getLsbD_extractLsb',b,decide_true,Bool.true_and,Nat.div_add_mod] using h

def keyBlock (key : BitVec 192) (j : Nat) : Word := key.extractLsb' (64*(j-1)) 64

theorem input_word (idx : Index) (key : BitVec 192) (j : Fin 25) :
    replyWords (input (coord idx).1 key) j =
      (if j.val=0 then wordAddress (msgWord (idx.val-rank idx.val)) else keyBlock key j.val) := by
  unfold input replyWords
  have h := j.isLt
  by_cases zero : j.val=0
  · simp only [zero,ite_true,Nat.mul_zero]
    rw [BitVec.extractLsb'_append_eq_of_add_le (by decide : 0+64≤256),
      BitVec.extractLsb'_append_eq_right]
    unfold Permutation.CounterSalt.ctr
    rw [coordinate_first];unfold wordAddress msgWord;congr 1 <;> omega
  · rw [if_neg zero]
    by_cases low : j.val<4
    · rw [BitVec.extractLsb'_append_eq_of_add_le (by omega : 64*j.val+64≤256),
          BitVec.extractLsb'_append_eq_of_le (by omega : 64≤64*j.val)]
      unfold keyBlock;congr 1 <;> omega
    · rw [BitVec.extractLsb'_append_eq_of_le (by omega : 256≤64*j.val)]
      unfold keyBlock
      apply BitVec.eq_of_getLsbD_eq;intro k hk
      simp [hk,show 192≤64*(j.val-1)+k by omega]

def KeyIntact (m : Memory) (key : BitVec 192) := ∀ j, 0<j → j<25 → m (qSalt 0+j)=keyBlock key j

attribute [local semireducible] window writeWord writeWindow

private theorem counter_frame (o : Oracle) (m : Memory) (i : Index) (j : Nat) :
    firstState o m i.val (qSalt 0+j)=m (qSalt 0+j) := by
  unfold firstState writeWindow
  apply dif_neg
  have v : i.val<16777216:=i.isLt
  unfold msgWord qSalt;omega

theorem generated_eq (o : Oracle) (m : Memory) (idx : Index) (key : BitVec 192)
    (intact : KeyIntact m key) (head : rank idx.val=0) :
    generated o m idx.val=o.permutation (input (coord idx).1 key) := by
  unfold generated
  apply congrArg o.permutation
  rw [←reply_pack (input (coord idx).1 key)]
  apply congrArg packBuffer;funext j
  rw [input_word];unfold seededMem window writeWord
  by_cases zero : j.val=0
  · simp [zero,head]
  · simp only [zero,ite_false,show qSalt 0+j.val≠qSalt 0 by omega]
    exact (counter_frame ..).trans (intact _ (by omega) j.isLt)

theorem earlier_buffer (i : Nat) (notHead : rank i≠0) :
    sourceWord i+2≤msgWord i-4 := by
  unfold sourceWord groupBuffer msgWord rank at *
  omega

theorem later_eq (o : Oracle) (m : Memory) (i : Nat) (notHead : rank i≠0) :
    laterState o m i = stamp (firstState o m i) (leafStart i) (wordAddress (msgWord i+7))
      (window m (sourceWord i)) := by
  have l := earlier_buffer i notHead
  have keep (j : Nat) (h : j<2) : firstState o m i (sourceWord i+j)=m (sourceWord i+j) := by
    unfold firstState writeWindow;apply dif_neg;omega
  unfold laterState stamp window
  rw [show leafStart i+12=msgWord i+7 by unfold leafStart msgWord;omega,
      show leafStart i+13=msgWord i+8 by unfold leafStart msgWord;omega,
      show leafStart i+14=msgWord i+9 by unfold leafStart msgWord;omega]
  have v0 := keep 0 (by decide);have v1 := keep 1 (by decide)
  simp only [writeWord,show sourceWord i≠msgWord i+7 by omega,show sourceWord i+1≠msgWord i+7 by omega,
    show sourceWord i+1≠msgWord i+8 by omega,ite_false,Nat.add_zero,Fin.val_zero] at *
  simp only [v0,v1];rfl

end TwoPermutationPrototype.Grouped
