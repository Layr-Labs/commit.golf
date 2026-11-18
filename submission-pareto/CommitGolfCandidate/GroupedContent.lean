import CommitGolfCandidate.GroupedEval
import CommitGolfCandidate.K3CBDefs
import CommitGolfCandidate.TwoPermutationBindingLeaf
import CommitGolfCandidate.TwoPermutationHeapInvariant

/-!
# K3-lite slot semantics in closed form

`packetMem o regs m i` is the memory after slot `i` (as a function of the memory and registers
before it); `plan_meaning` shows that the word-level plan computes it.  `c2Mem` is the memory
after the leaf's second call (K1); a fourth quartet leaf then runs the group call of its quartet
`g = i/4` on the record window `[qSource g, +25)` and writes the reply at `replyWord g`
(even `g`: over the leaf reply at `qLeaf i`; odd `g`: into the spare words of block `g-1`).
-/

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.QuartetCommit (qSource qSalt qLeaf)
open TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.RV64.PackedLeaves
open CommitGolfCandidate.Permutation.CounterSalt (coord firstLeaf input parts)
set_option maxRecDepth 18000
set_option maxHeartbeats 1800000
set_option exponentiation.threshold 2048

/-- The reply of a permutation call on the 25 words at `a`. -/
def callReply (o : Oracle) (m : Memory) (a : Nat) := o.permutation (packBuffer (window m a))

/-- A slot: the A leaf's first call `[w+7,w+32) → [w-25,w)`. -/
def aMem1 (o : Oracle) (m : Memory) (i : Nat) :=
  writeWindow m (msgWord i-25) (replyWords (callReply o m (msgWord i+7)))
/-- The C leaf's first call `[w+32,w+57) → [w+28,w+53)`. -/
def cFirst (o : Oracle) (m : Memory) (i : Nat) := callReply o (aMem1 o m i) (msgWord i+32)
def aMem2 (o : Oracle) (m : Memory) (i : Nat) :=
  writeWindow (aMem1 o m i) (msgWord i+28) (replyWords (cFirst o m i))
/-- A keyed head (a restart every 34 heads of a tile) stores the counter (byte address of the C leaf)
in word 0 of the key block; a linked head stores nothing. -/
def seededMem (o : Oracle) (m : Memory) (i : Nat) :=
  if keyed (i%4096) then writeWord (aMem2 o m i) (qSalt 0) (wordAddress (msgWord i+32)) else aMem2 o m i
/-- The generator input: the key block (keyed head) or, in place, the previous head's generator
reply `[genWord (i-11), +25)` (linked head; `= [w-336, w-311)`). -/
def genSource (i : Nat) := if keyed (i%4096) then qSalt 0 else genWord (i-11)
def generated (o : Oracle) (m : Memory) (i : Nat) := callReply o (seededMem o m i) (genSource i)
/-- The generator reply at `[w+16,w+41)` and the A tag at `w-5`. -/
def headMem (o : Oracle) (m : Memory) (i : Nat) :=
  writeWord (writeWindow (seededMem o m i) (msgWord i+16) (replyWords (generated o m i)))
    (msgWord i-5) (wordAddress (msgWord i-7))

/-- C slot: the tag (x10 on entry, the C window `w+7`) at `w+9`. -/
def cMem (regs : Reg → Word) (m : Memory) (i : Nat) := writeWord m (msgWord i+9) (regs .x10)

/-- Follower: first call `[w,w+25) → [w-4,w+21)`, tag at `w+9`. -/
def fMem1 (o : Oracle) (m : Memory) (i : Nat) :=
  writeWord (writeWindow m (msgWord i-4) (replyWords (callReply o m (msgWord i)))) (msgWord i+9)
    (wordAddress (msgWord i+7))
/-- Follower: the salt into `w+7, w+8`. -/
def followerMem (o : Oracle) (regs : Reg → Word) (m : Memory) (i : Nat) : Memory :=
  if rank i≤8 then
    writeWord (writeWord (fMem1 o m i) (msgWord i+7) (fMem1 o m i (sourceWord i))) (msgWord i+8)
      (writeWord (fMem1 o m i) (msgWord i+7) (fMem1 o m i (sourceWord i)) (sourceWord i+1))
  else if rank i=9 then writeWord (writeWord (fMem1 o m i) (msgWord i+7) (regs .x14)) (msgWord i+8) (regs .x15)
  else writeWord (writeWord (fMem1 o m i) (msgWord i+7) (regs .x16)) (msgWord i+8) (regs .x17)

def preSecond (o : Oracle) (regs : Reg → Word) (m : Memory) (i : Nat) :=
  if rank i=0 then headMem o m i else if rank i=1 then cMem regs m i else followerMem o regs m i
def digestReply (o : Oracle) (regs : Reg → Word) (m : Memory) (i : Nat) :=
  callReply o (preSecond o regs m i) (secondWord i)
/-- After the second call (the leaf digest lands at `qLeaf i`). -/
def c2Mem (o : Oracle) (regs : Reg → Word) (m : Memory) (i : Nat) :=
  writeWindow (preSecond o regs m i) (qLeaf i) (replyWords (digestReply o regs m i))
/-- The reply of the group call of quartet `i/4` (window `0^9 ‖ d0 d1 d2 d3` at `qSource (i/4)`). -/
def tailReply (o : Oracle) (regs : Reg → Word) (m : Memory) (i : Nat) :=
  callReply o (c2Mem o regs m i) (qSource (i/4))
def packetMem (o : Oracle) (regs : Reg → Word) (m : Memory) (i : Nat) :=
  if i%4=3 then writeWindow (c2Mem o regs m i) (replyWord (i/4)) (replyWords (tailReply o regs m i))
  else c2Mem o regs m i

attribute [local irreducible] packBuffer writeWord writeWindow window

theorem body_meaning (o : Oracle) (v : View) (i : Nat) :
    ((bodyPlan i).foldl (viewStep o) v).mem=c2Mem o v.regs v.mem i := by
  have hr := rank_lt i
  by_cases r0 : rank i=0
  · by_cases kd : keyed (i%4096) <;>
      simp [bodyPlan,eq_true r0,kd,viewStep,View.reg,View.store,View.reply,c2Mem,digestReply,preSecond,
        secondWord,headMem,generated,genSource,seededMem,aMem2,cFirst,aMem1,callReply]
  by_cases r1 : rank i=1
  · simp [bodyPlan,eq_false r0,eq_true r1,viewStep,View.reg,View.store,View.reply,c2Mem,digestReply,preSecond,
      secondWord,cMem,callReply]
  by_cases r8 : rank i≤8
  · by_cases e8 : rank i=8 <;>
      simp [bodyPlan,saltPlan,eq_false r0,eq_false r1,eq_true r8,e8,viewStep,View.reg,View.store,View.reply,
        c2Mem,digestReply,preSecond,secondWord,followerMem,fMem1,callReply]
  · by_cases e9 : rank i=9 <;>
      simp [bodyPlan,saltPlan,eq_false r0,eq_false r1,eq_false r8,e9,viewStep,View.reg,View.store,View.reply,
        c2Mem,digestReply,preSecond,secondWord,followerMem,fMem1,callReply]

theorem tail_meaning (o : Oracle) (v : View) (i : Nat) :
    ((tailPlan i).foldl (viewStep o) v).mem=(if i%4=3 then writeWindow v.mem (replyWord (i/4))
      (replyWords (callReply o v.mem (qSource (i/4)))) else v.mem) ∧
    (∀ r : Reg, r≠.x10 → r≠.x12 → ((tailPlan i).foldl (viewStep o) v).regs r=v.regs r) := by
  have e : i%4096%4=i%4 := by omega
  have e2 : i%4096/4%2=i/4%2 := by omega
  have q : qLeaf i=qSource (i/4)+21 ∨ i%4≠3 := by
    by_cases t : i%4=3
    · left;unfold qLeaf;rw [t]
    · right;exact t
  by_cases t : i%4=3
  · have ql : qLeaf i=qSource (i/4)+21 := by rcases q with q|q;exact q;exact absurd t q
    by_cases ev : (i/4)%2=0
    · refine ⟨?_,?_⟩
      · simp [tailPlan,e,e2,t,ev,viewStep,View.reg,View.reply,callReply,replyWord,ql]
      · intro r h10 h12
        simp [tailPlan,e,e2,t,ev,viewStep,View.reg,View.reply,Ne.symm h10]
    · refine ⟨?_,?_⟩
      · simp [tailPlan,e,e2,t,ev,viewStep,View.reg,View.reply,callReply,replyWord]
      · intro r h10 h12
        simp [tailPlan,e,e2,t,ev,viewStep,View.reg,View.reply,Ne.symm h10,Ne.symm h12]
  · refine ⟨?_,?_⟩
    · simp [tailPlan,e,t,viewStep,View.reg]
    · intro r h10 h12
      simp [tailPlan,e,t,viewStep,View.reg,Ne.symm h10]

theorem plan_meaning (o : Oracle) (v : View) (i : Nat) :
    ((plan i).foldl (viewStep o) v).mem=packetMem o v.regs v.mem i := by
  unfold plan;rw [List.foldl_append,(tail_meaning ..).1,body_meaning]
  unfold packetMem tailReply;rfl

/-- Registers x14..x17 after the body of a slot: loaded from the generator reply by rank 8, kept otherwise. -/
theorem body_prefetch (o : Oracle) (v : View) (i : Nat) :
    (rank i=8 → ((bodyPlan i).foldl (viewStep o) v).regs .x14=preSecond o v.regs v.mem i (genWord i+16) ∧
      ((bodyPlan i).foldl (viewStep o) v).regs .x15=preSecond o v.regs v.mem i (genWord i+17) ∧
      ((bodyPlan i).foldl (viewStep o) v).regs .x16=preSecond o v.regs v.mem i (genWord i+18) ∧
      ((bodyPlan i).foldl (viewStep o) v).regs .x17=preSecond o v.regs v.mem i (genWord i+19)) ∧
    (rank i≠8 → ((bodyPlan i).foldl (viewStep o) v).regs .x14=v.regs .x14 ∧
      ((bodyPlan i).foldl (viewStep o) v).regs .x15=v.regs .x15 ∧
      ((bodyPlan i).foldl (viewStep o) v).regs .x16=v.regs .x16 ∧
      ((bodyPlan i).foldl (viewStep o) v).regs .x17=v.regs .x17) := by
  have hr := rank_lt i
  constructor
  · intro e8
    have r0 : rank i≠0 := by omega
    have r1 : rank i≠1 := by omega
    have r8 : rank i≤8 := by omega
    simp [bodyPlan,saltPlan,eq_false r0,eq_false r1,eq_true r8,eq_true e8,viewStep,View.reg,View.store,View.reply,
      preSecond,followerMem,fMem1,callReply]
  · intro n8
    by_cases r0 : rank i=0
    · by_cases kd : keyed (i%4096) <;> simp [bodyPlan,eq_true r0,kd,viewStep,View.reg,View.store,View.reply]
    by_cases r1 : rank i=1
    · simp [bodyPlan,eq_false r0,eq_true r1,viewStep,View.reg,View.store,View.reply]
    by_cases r8 : rank i≤8
    · simp [bodyPlan,saltPlan,eq_false r0,eq_false r1,eq_true r8,eq_false n8,viewStep,View.reg,View.store,View.reply]
    · by_cases e9 : rank i=9 <;>
        simp [bodyPlan,saltPlan,eq_false r0,eq_false r1,eq_false r8,e9,viewStep,View.reg,View.store,View.reply]

/-- Registers x14..x17 after a slot (the group tail writes only x10, x12). -/
theorem plan_prefetch (o : Oracle) (v : View) (i : Nat) :
    (rank i=8 → ((plan i).foldl (viewStep o) v).regs .x14=preSecond o v.regs v.mem i (genWord i+16) ∧
      ((plan i).foldl (viewStep o) v).regs .x15=preSecond o v.regs v.mem i (genWord i+17) ∧
      ((plan i).foldl (viewStep o) v).regs .x16=preSecond o v.regs v.mem i (genWord i+18) ∧
      ((plan i).foldl (viewStep o) v).regs .x17=preSecond o v.regs v.mem i (genWord i+19)) ∧
    (rank i≠8 → ((plan i).foldl (viewStep o) v).regs .x14=v.regs .x14 ∧
      ((plan i).foldl (viewStep o) v).regs .x15=v.regs .x15 ∧
      ((plan i).foldl (viewStep o) v).regs .x16=v.regs .x16 ∧
      ((plan i).foldl (viewStep o) v).regs .x17=v.regs .x17) := by
  unfold plan
  simp only [List.foldl_append]
  have t := (tail_meaning o ((bodyPlan i).foldl (viewStep o) v) i).2
  rw [t .x14 (by decide) (by decide),t .x15 (by decide) (by decide),t .x16 (by decide) (by decide),
    t .x17 (by decide) (by decide)]
  exact body_prefetch o v i

theorem coordinate_first (i : Index) : firstLeaf (coord i).1=i.val-rank i.val := by
  unfold firstLeaf coord rank
  dsimp only
  have small : i.val%4096/11<373 := by omega
  rw [show (373*(i.val/4096)+i.val%4096/11)/373=i.val/4096 by omega,
    show (373*(i.val/4096)+i.val%4096/11)%373=i.val%4096/11 by omega]
  omega

def keyBlock (key : BitVec 192) (j : Nat) : Word := key.extractLsb' (64*(j-1)) 64

/-- The generator input: word 0 is the counter `4096 + 256 (first leaf + 1)` (the C leaf). -/
theorem input_word (idx : Index) (key : BitVec 192) (j : Fin 25) :
    replyWords (input (coord idx).1 key) j =
      (if j.val=0 then wordAddress (msgWord (idx.val-rank idx.val+1)) else keyBlock key j.val) := by
  unfold input replyWords
  have h := j.isLt
  by_cases zero : j.val=0
  · simp only [zero,ite_true,Nat.mul_zero]
    rw [BitVec.extractLsb'_append_eq_of_add_le (by decide : 0+64≤256),
      BitVec.extractLsb'_append_eq_right]
    unfold Permutation.CounterSalt.ctr
    rw [coordinate_first];unfold wordAddress msgWord;congr 1
    have : rank idx.val ≤ idx.val := by unfold rank;omega
    omega
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

theorem keyed_tile (i : Nat) : keyed (i%4096)=true ↔ i%4096/11%34=0 := by
  unfold keyed;rw [Nat.mod_mod];simp

theorem generated_eq (o : Oracle) (m : Memory) (idx : Index) (key : BitVec 192)
    (intact : KeyIntact m key) (head : rank idx.val=0) (kd : idx.val%4096/11%34=0) :
    generated o m idx.val=o.permutation (input (coord idx).1 key) := by
  have kt : keyed (idx.val%4096)=true := (keyed_tile _).2 kd
  unfold generated callReply genSource
  rw [if_pos kt]
  apply congrArg o.permutation
  rw [←reply_pack (input (coord idx).1 key)]
  apply congrArg packBuffer;funext j
  rw [input_word];unfold seededMem;rw [if_pos kt];unfold aMem2 aMem1 window writeWord writeWindow
  have v : idx.val<16777216 := idx.isLt
  by_cases zero : j.val=0
  · have e : msgWord (idx.val+1)=msgWord idx.val+32 := by unfold msgWord;omega
    simp [zero,head,e]
  · have far1 : ¬(msgWord idx.val-25≤qSalt 0+j.val ∧ qSalt 0+j.val<msgWord idx.val-25+25) := by
      unfold msgWord qSalt;omega
    have far2 : ¬(msgWord idx.val+28≤qSalt 0+j.val ∧ qSalt 0+j.val<msgWord idx.val+28+25) := by
      unfold msgWord qSalt;omega
    simp only [zero,ite_false,show qSalt 0+j.val≠qSalt 0 by omega,far1,far2,dite_false]
    exact intact _ (by omega) j.isLt

/-- A linked head is not the first head of its tile. -/
theorem linked_big (i : Nat) (linked : i%4096/11%34≠0) : 11 ≤ i%4096 := by
  rcases Nat.lt_or_ge (i%4096) 11 with h|h
  · exfalso;apply linked;rw [Nat.div_eq_of_lt h]
  · exact h

/-- The previous head of a linked head `i` is `i - 11`; its generator reply starts at `w - 336`. -/
theorem linked_gen (i : Nat) (r0 : rank i=0) (linked : i%4096/11%34≠0) : genWord (i-11)=msgWord i-336 := by
  unfold rank at r0
  have big := linked_big i linked
  have r : rank (i-11)=0 := by
    unfold rank
    have d := Nat.div_add_mod i 4096
    have e : (i-11)%4096=i%4096-11 := by
      rw [show i-11=4096*(i/4096)+(i%4096-11) by omega,Nat.mul_add_mod]
      exact Nat.mod_eq_of_lt (by omega)
    rw [e]
    have : (i%4096-11)%11=(i%4096)%11 := by
      rw [show i%4096=(i%4096-11)+11 by omega,Nat.add_mod_right];simp
    rw [this,r0]
  have i11 : 11 ≤ i := Nat.le_trans big (Nat.mod_le _ _)
  unfold genWord;rw [r];unfold msgWord;clear linked r0 big;omega

/-- A linked head's generator call reads the previous head's whole reply in place. -/
theorem generated_linked (o : Oracle) (m : Memory) (i : Nat) (R : BitVec 1600) (hi : i<16777216)
    (r0 : rank i=0) (linked : i%4096/11%34≠0) (prev : window m (genWord (i-11))=replyWords R) :
    generated o m i=o.permutation R := by
  have i11 : 11 ≤ i := Nat.le_trans (linked_big i linked) (Nat.mod_le _ _)
  have low : 352 ≤ msgWord i := by unfold msgWord;omega
  rw [linked_gen i r0 linked] at prev
  have kt : ¬keyed (i%4096)=true := fun h => linked ((keyed_tile i).1 h)
  unfold generated callReply genSource
  rw [if_neg kt,linked_gen i r0 linked]
  apply congrArg o.permutation
  rw [←reply_pack R,←prev]
  apply congrArg packBuffer;funext j
  unfold seededMem;rw [if_neg kt];unfold aMem2 aMem1 window writeWindow
  have hj := j.isLt
  have far1 : ¬(msgWord i-25≤msgWord i-336+j.val ∧ msgWord i-336+j.val<msgWord i-25+25) := by omega
  have far2 : ¬(msgWord i+28≤msgWord i-336+j.val ∧ msgWord i-336+j.val<msgWord i+28+25) := by omega
  simp only [far1,far2,dite_false]

end TwoPermutationPrototype.Grouped
