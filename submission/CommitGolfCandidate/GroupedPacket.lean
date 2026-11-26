import CommitGolfCandidate.GroupedKernel
import CommitGolfCandidate.GroupedCommitImage
import CommitGolfCandidate.QuartetCommitRanges
import CommitGolfCandidate.QuartetCommitLeafOps

/-!
# The K3-lite slot plans

`plan i = bodyPlan i ++ tailPlan i` is the code of slot `i` (slot `i % 4096` of its tile) with the
word address that every instruction computes.  Word indices: the message of leaf `i` is at
`msgWord i = 512 + 32 i`, quartet block `g` at `qSource g` (record cell format, digest of leaf `i`
at `qLeaf i`), the key block at `qSalt 0`.

* A leaf (rank 0), `m = msgWord i`: first call `[m+7, m+32) → [m-25, m)`, the C first call
  `[m+32, m+57) → [m+28, m+53)`, the counter `m+32` into the key block, the generator `→ [m+16, m+41)`,
  the tag `m-7` at `m-5` and the second call `[m-7, m+18) → qLeaf i`.
* C leaf (rank 1), entry `m+7`: tag `m+7` at `m+9`, second call `[m+7, m+32) → qLeaf i`.
* Follower (rank ≥ 2): first call `[m, m+25) → [m-4, m+21)`, tag `m+7` at `m+9`, salt into
  `m+7, m+8` (from the generator reply, or from x14..x17 for ranks 9 and 10), second call.
* Tail: `x10 += trail` to the next entry, or after the fourth leaf of quartet `q = i/4` the quartet
  call on `[qSource q, +25)` (even `q`: output `qLeaf i = qSource q + 21`, x12 reused; odd `q`:
  output `qSource q - 82`) and the restore `x10 += x1 | x2` to the next entry.
-/

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.QuartetCommit (qSource qSalt qLeaf)
set_option maxRecDepth 16000
set_option maxHeartbeats 1800000

def msgWord (i : Nat) := 512+32*i
/-- Word address held by x10 on entry to slot `i` (`L+56` for an A or C leaf, `L` for a follower). -/
def entryWord (i : Nat) := if rank i≤1 then msgWord i+7 else msgWord i
/-- Start of the second-call window: `B-56` for an A leaf, `L+56` otherwise. -/
def secondWord (i : Nat) := if rank i=0 then msgWord i-7 else msgWord i+7
/-- Word distance from a salt-first or C leaf's second-call input (`msgWord i + 7`) to its quartet slot. -/
def slotGap (j : Nat) := 603979782-28*j
/-- Word distance from an A leaf's second-call input (`msgWord i - 7`) to its quartet slot. -/
def aGap (j : Nat) := 603979796-28*j
/-- The same gaps for the leaves of an odd quartet, whose block sits 1,224 bytes (153 words) lower. -/
def oddGap (j : Nat) := slotGap j-153
def oddAGap (j : Nat) := aGap j-153
/-- Gap of leaf `i` (by kind and quartet parity). -/
def sgap (i : Nat) := if (i/4)%2=0 then slotGap (i%4) else oddGap (i%4)
def agap (i : Nat) := if (i/4)%2=0 then aGap (i%4) else oddAGap (i%4)
/-- Word distance from the quartet block back to the next entry (negated restore register). -/
def rGap (n : Nat) := 603979652-(if near n then 7 else 0)-(if (n/4)%2=1 then 153 else 0)
/-- First word of the generator reply of the group of `i` (byte `B+128` of its A leaf). -/
def genWord (i : Nat) := msgWord (i-rank i)+16
/-- Source of the salt of a follower of rank `2..8`: generator words `2 (rank-1)`. -/
def sourceWord (i : Nat) := genWord i+2*(rank i-1)
/-- Output of the quartet call of quartet `i/4` (`i % 4 = 3`): over the fourth digest (both parities). -/
def groupOut (i : Nat) := qLeaf i

def saltPlan (i : Nat) : List Action :=
  let m := msgWord i
  if rank i≤8 then
    [.load .x12 .x10 (saltImm (rank i)) (sourceWord i),.store .x10 .x12 0 (m+7),
     .load .x12 .x10 (saltImm (rank i)+8) (sourceWord i+1),.store .x10 .x12 8 (m+8)] ++
    (if rank i=8 then [.load .x14 .x10 (-1848) (genWord i+16),.load .x15 .x10 (-1840) (genWord i+17),
      .load .x16 .x10 (-1832) (genWord i+18),.load .x17 .x10 (-1824) (genWord i+19)] else [])
  else if rank i=9 then [.store .x10 .x14 0 (m+7),.store .x10 .x15 8 (m+8)]
  else [.store .x10 .x16 0 (m+7),.store .x10 .x17 8 (m+8)]

def bodyPlan (i : Nat) : List Action :=
  let m := msgWord i
  let n := i%4096
  if rank i=0 then
    [.offset .x12 .x10 (-256) (m-25),.perm (m+7) (m-25),.offset .x10 .x10 200 (m+32),
     .offset .x12 .x10 (-32) (m+28),.perm (m+32) (m+28)] ++
    (if keyed n then [.store .x24 .x10 0 (qSalt 0),.offset .x12 .x12 (-96) (m+16),.offset .x10 .x24 0 (qSalt 0),
       .perm (qSalt 0) (m+16)]
     else [.add .x10 .x12 .x3 (genWord (i-11)),.offset .x12 .x12 (-96) (m+16),.perm (genWord (i-11)) (m+16)]) ++
    [.offset .x10 .x12 (-184) (m-7),.store .x10 .x10 16 (m-5),
     .add .x12 .x10 (areg n) (qLeaf i),.perm (m-7) (qLeaf i)]
  else if rank i=1 then
    [.store .x10 .x10 16 (m+9),.add .x12 .x10 (sreg n) (qLeaf i),.perm (m+7) (qLeaf i)]
  else
    [.offset .x12 .x10 (-32) (m-4),.perm m (m-4),.offset .x10 .x10 56 (m+7),.store .x10 .x10 16 (m+9)] ++
    saltPlan i ++
    [.add .x12 .x10 (sreg n) (qLeaf i),.perm (m+7) (qLeaf i)]

def tailPlan (i : Nat) : List Action :=
  let n := i%4096
  if n%4=3 then
    [.offset .x10 .x12 (-168) (qSource (i/4)),.perm (qSource (i/4)) (qLeaf i),
     .add .x10 .x10 (rreg n) (entryWord (i+1))]
  else [.offset .x10 .x10 (trail n) (entryWord (i+1))]

def plan (i : Nat) : List Action := bodyPlan i ++ tailPlan i

theorem within_rank (i : Nat) : rank (i%4096)=rank i := by
  unfold rank;rw [Nat.mod_mod]

theorem plan_words (i : Nat) : (plan i).map Action.op=packet (i%4096) := by
  unfold plan bodyPlan tailPlan packet saltPlan saltCode tailCode
  rw [within_rank,List.map_append]
  congr 1
  · have h := rank_lt i
    generalize rank i=r at *
    by_cases kd : keyed (i%4096) <;> interval_cases r <;> simp [Action.op,kd]
  · have m : i%4096%4=i%4 := by omega
    by_cases t : i%4=3
    · by_cases e : i%4096/4%2=0 <;> simp [t,m,e,Action.op]
    · simp [t,m,Action.op]

theorem plan_fetch (i : Nat) : fetchOps (firstWord (i%4096)) (plan i) := by
  intro j s pc
  have len := congrArg List.length (plan_words i)
  simp only [List.length_map] at len
  have inside : j.val<(packet (i%4096)).length := len ▸ j.isLt
  have got := fetch_packet ⟨i%4096,by omega⟩ j.val inside s pc
  rw [←plan_words,List.getElem?_eq_getElem (by simpa using j.isLt)] at got
  change fetch image s=some (.base (plan i)[j.val].op)
  simpa only [List.getElem_map,Option.getD_some] using got

structure PacketRegs (s : MachineState) (i : Nat) : Prop where
  msg : s.getReg .x10=wordAddress (entryWord i)
  s0 : s.getReg .x20=wordAddress (slotGap 0)
  s1 : s.getReg .x23=wordAddress (slotGap 1)
  s2 : s.getReg .x25=wordAddress (slotGap 2)
  s3 : s.getReg .x26=wordAddress (slotGap 3)
  a0 : s.getReg .x27=wordAddress (aGap 0)
  a1 : s.getReg .x28=wordAddress (aGap 1)
  a2 : s.getReg .x29=wordAddress (aGap 2)
  a3 : s.getReg .x30=wordAddress (aGap 3)
  o0 : s.getReg .x8=wordAddress (oddGap 0)
  o1 : s.getReg .x9=wordAddress (oddGap 1)
  o2 : s.getReg .x18=wordAddress (oddGap 2)
  o3 : s.getReg .x19=wordAddress (oddGap 3)
  b0 : s.getReg .x21=wordAddress (oddAGap 0)
  b1 : s.getReg .x22=wordAddress (oddAGap 1)
  b2 : s.getReg .x4=wordAddress (oddAGap 2)
  b3 : s.getReg .x7=wordAddress (oddAGap 3)
  far : s.getReg .x1=-wordAddress 603979652
  close : s.getReg .x2=-wordAddress 603979645
  farOdd : s.getReg .x31=-wordAddress 603979499
  closeOdd : s.getReg .x6=-wordAddress 603979492
  link : s.getReg .x3=-wordAddress 364
  counter : s.getReg .x24=wordAddress (qSalt 0)
  selector : s.getReg .x5=0
  size : s.getReg .x11=200
  primitive : s.getReg .x13=1

theorem slot_address (i : Nat) : wordAddress (msgWord i+7)+wordAddress (sgap i)=wordAddress (qLeaf i) := by
  rw [←wordAddress_add];congr 1
  have h4 : i=4*(i/4)+i%4 := (Nat.div_add_mod i 4).symm
  have hm : i%4<4 := Nat.mod_lt _ (by decide)
  unfold msgWord sgap oddGap slotGap qLeaf qSource
  split_ifs <;> omega

theorem a_slot_address (i : Nat) : wordAddress (msgWord i-7)+wordAddress (agap i)=wordAddress (qLeaf i) := by
  rw [←wordAddress_add];congr 1
  have h4 : i=4*(i/4)+i%4 := (Nat.div_add_mod i 4).symm
  have hm : i%4<4 := Nat.mod_lt _ (by decide)
  unfold msgWord agap oddAGap aGap qLeaf qSource
  split_ifs <;> omega

/-- A positive displacement of `d` words. -/
theorem addr_fwd (a d : Nat) (imm : BitVec 12) (h : signExtend12 imm=wordAddress d) :
    wordAddress a+signExtend12 imm=wordAddress (a+d) := by rw [h,wordAddress_add]

/-- A negative displacement of `d` words. -/
theorem addr_back (a d : Nat) (imm : BitVec 12) (h : signExtend12 imm+wordAddress d=0) (hd : d≤a) :
    wordAddress a+signExtend12 imm=wordAddress (a-d) := by
  have e : wordAddress a=wordAddress (a-d)+wordAddress d := by rw [←wordAddress_add,Nat.sub_add_cancel hd]
  rw [e,BitVec.add_assoc,BitVec.add_comm (wordAddress d),h];exact BitVec.add_zero _

theorem salt_imm_value : ∀ r : Fin 11, 2≤r.val → r.val≤8 →
    signExtend12 (saltImm r.val)+wordAddress (30*r.val-7)=0 ∧
    signExtend12 (saltImm r.val+8)+wordAddress (30*r.val-8)=0 := by decide

theorem rank_next (i : Nat) (h : rank (i+1)≠0) : rank (i+1)=rank i+1 := by
  unfold rank at *
  have : i%4096≠4095 := by intro e;apply h;rw [show (i+1)%4096=0 by omega]
  rw [show (i+1)%4096=i%4096+1 by omega] at h ⊢
  omega

theorem rank_succ_within (i : Nat) : rank (i%4096+1)=rank (i+1) := by
  unfold rank;rw [show (i%4096+1)%4096=(i+1)%4096 by omega]

theorem head_pair (i : Nat) (h : rank i=0) : rank (i+1)=1 := by
  unfold rank at *
  have : i%4096≠4095 := by omega
  rw [show (i+1)%4096=i%4096+1 by omega];omega

theorem trail_within (i : Nat) :
    trail (i%4096)=if rank i=0 then 368 else if rank (i+1)=0 then 256 else 200 := by
  unfold trail;rw [within_rank,rank_succ_within]

/-- The next entry, seen from leaf `i`. -/
theorem entry_next (i : Nat) :
    entryWord (i+1)=if rank i=0 then msgWord i+39 else if rank (i+1)=0 then msgWord i+39 else msgWord i+32 := by
  unfold entryWord msgWord
  by_cases h0 : rank i=0
  · rw [if_pos h0,if_pos (by rw [head_pair i h0])];omega
  · rw [if_neg h0]
    by_cases z : rank (i+1)=0
    · rw [if_pos z,if_pos (by omega)];omega
    · have one : ¬ rank (i+1)≤1 := by have := rank_next i z;omega
      rw [if_neg z,if_neg one];omega

/-- x10 after the closing `addi x10,x10,trail` of a C leaf or a follower. -/
theorem trail_address (i : Nat) (h : rank i≠0) :
    wordAddress (msgWord i+7)+signExtend12 (trail (i%4096))=wordAddress (entryWord (i+1)) := by
  rw [trail_within,if_neg h,entry_next,if_neg h]
  by_cases z : rank (i+1)=0
  · rw [if_pos z,if_pos z,addr_fwd _ 32 _ (by decide)];all_goals (congr 1;try omega)
  · rw [if_neg z,if_neg z,addr_fwd _ 25 _ (by decide)];all_goals (congr 1;try omega)

/-- x10 after the A leaf's closing `addi x10,x10,368` (to the C window). -/
theorem trail_head (i : Nat) (h : rank i=0) :
    wordAddress (msgWord i-7)+signExtend12 (trail (i%4096))=wordAddress (entryWord (i+1)) := by
  have low : 512≤msgWord i := by unfold msgWord;omega
  rw [trail_within,if_pos h,entry_next,if_pos h,addr_fwd _ 46 _ (by decide)];all_goals (congr 1;try omega)

/-- The quartet call reads the block: `x10 = qLeaf i - 168` bytes. -/
theorem group_input (i : Nat) (t : i%4=3) :
    wordAddress (qLeaf i)+signExtend12 3928#12=wordAddress (qSource (i/4)) := by
  have e : qLeaf i=qSource (i/4)+21 := by unfold qLeaf;omega
  rw [e,addr_back (qSource (i/4)+21) 21 3928#12 (by decide) (by omega)];all_goals (congr 1;try omega)

theorem group_out_eq (i : Nat) : qLeaf i=groupOut i := rfl

/-- Adding a negated word address. -/
theorem addr_neg (a d : Nat) (hd : d≤a) : wordAddress a+-wordAddress d=wordAddress (a-d) := by
  have e : wordAddress a=wordAddress (a-d)+wordAddress d := by rw [←wordAddress_add,Nat.sub_add_cancel hd]
  rw [e,BitVec.add_assoc,BitVec.add_right_neg];exact BitVec.add_zero _

/-- x10 after the restore `add x10,x10,x1|x2` that follows a quartet call. -/
theorem restore_address (i : Nat) (t : i%4=3) :
    wordAddress (qSource (i/4))+-wordAddress (rGap (i%4096))=wordAddress (entryWord (i+1)) := by
  have hn : near (i%4096)=true ↔ (rank i=0 ∨ rank (i+1)=0) := by
    unfold near;rw [within_rank,rank_succ_within];simp
  have e2 : i%4096/4%2=i/4%2 := by omega
  have big : rGap (i%4096)≤qSource (i/4) := by
    unfold rGap qSource;rw [e2];split_ifs <;> omega
  rw [addr_neg _ _ big,entry_next]
  congr 1
  have i4 : i=4*(i/4)+3 := by omega
  unfold rGap qSource msgWord
  rw [e2]
  by_cases h0 : rank i=0
  · rw [if_pos (hn.mpr (Or.inl h0)),if_pos h0];split_ifs <;> omega
  · by_cases z : rank (i+1)=0
    · rw [if_pos (hn.mpr (Or.inr z)),if_neg h0,if_pos z];split_ifs <;> omega
    · rw [if_neg (show ¬near (i%4096)=true from fun e => by rcases hn.mp e with e|e <;> contradiction),
        if_neg h0,if_neg z];split_ifs <;> omega

/-- A chained head reads the previous head's generator reply: `x12 + x3 = (m+28) - 364`. -/
theorem chain_source (i : Nat) (h0 : rank i=0) (kd : ¬keyed (i%4096)) :
    wordAddress (msgWord i+28)+-wordAddress 364=wordAddress (genWord (i-11)) := by
  have big : 11 ≤ i%4096 := by
    by_contra l
    apply kd
    unfold keyed;rw [Nat.mod_mod];simp only [beq_iff_eq];omega
  have r11 : rank (i-11)=0 := by
    unfold rank at h0 ⊢
    have e1 : (i-11)%4096=i%4096-11 := by
      have d := Nat.div_add_mod i 4096
      have e : i-11=(i%4096-11)+4096*(i/4096) := by omega
      rw [e,Nat.add_mul_mod_self_left];exact Nat.mod_eq_of_lt (by omega)
    rw [e1];omega
  have i11 : 11 ≤ i := by omega
  rw [addr_neg (msgWord i+28) 364 (by unfold msgWord;omega)]
  unfold genWord msgWord;rw [r11];congr 1;omega

theorem rreg_x10 (n : Nat) : (Reg.x10=rreg n)=False := eq_false (by unfold rreg;split_ifs <;> decide)
theorem rreg_x12 (n : Nat) : (Reg.x12=rreg n)=False := eq_false (by unfold rreg;split_ifs <;> decide)

theorem genWord_rank (i : Nat) (r : Nat) (h : rank i=r) : genWord i+32*r=msgWord i+16 := by
  unfold genWord msgWord;have : r ≤ i := by rw [←h];unfold rank;omega
  rw [h];omega

end TwoPermutationPrototype.Grouped
