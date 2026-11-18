import CommitGolfCandidate.GroupedKernel
import CommitGolfCandidate.GroupedCommitImage
import CommitGolfCandidate.QuartetCommitRanges
import CommitGolfCandidate.QuartetCommitLeafOps

/-! Pair-heads leaf body: the action plan of pair packet `P` (global pair index) with word-address witnesses.
Layout notes: `stack/PH-DESIGN.md`. Even leaf `2P` has entry `E = msgWord (2P)`, odd leaf `2P+1` has `O = E + 32`. -/

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.QuartetCommit (qSource qSalt qLeaf)
set_option maxRecDepth 16000
set_option maxHeartbeats 1800000

def msgWord (i : Nat) := 512+32*i
def cursor (i : Nat) := qSource (1024*(i/4096))+512*rb (i%4096)+256

/-- Rank of pair `P` inside its body, modulo the 11-pair head period. -/
def pairRank (P : Nat) := (P%2048)%11
/-- Position of pair `P` inside its salt group (0 = the head pair). -/
def groupK (P : Nat) := if pairRank P<5 then pairRank P else pairRank P-5
/-- The head pair of pair `P`'s salt group (global index). -/
def headPair (P : Nat) := P-groupK P
/-- First word of the generator reply of head pair `h` (written at the odd entry − 120 bytes). -/
def replyWord (h : Nat) := msgWord (2*h+1)-15
/-- The salt cursor `t2` of pair `P`'s group: the head's reply − 400 bytes. -/
def anchorWord (P : Nat) := replyWord (headPair P)-50
/-- Word of leaf `n`'s copied salt (`n` global, in a non-head pair): table salt `c` of the group head's reply, or
table salt 8 of the previous head's reply for the 12th leaf of a 12-leaf group. -/
def srcWord (n : Nat) : Nat :=
  if copyIndex (n%4096)=9 then replyWord (headPair (n/2)-5)+18 else replyWord (headPair (n/2))+2+2*copyIndex (n%4096)

def pairPlan (P : Nat) : List Action :=
  let p := P%2048
  let E := msgWord (2*P)
  let O := msgWord (2*P+1)
  [.offset .x10 .x10 256 (E+7),.offset .x12 .x10 (-256) (E-25),.perm (E+7) (E-25),
   .offset .x10 .x10 200 O,.offset .x12 .x10 (-32) (O-4),.perm O (O-4)] ++
  (if pairHead p then
    [.store .x24 .x10 0 (qSalt 0),.offset .x12 .x10 (-120) (O-15),.offset .x10 .x24 0 (qSalt 0),
     .perm (qSalt 0) (O-15)] ++
    (if prefetchA p then [.load .x16 .x12 144 (O+3),.load .x17 .x12 152 (O+4)]
     else if p%11=5 then [.load .x14 .x12 144 (O+3),.load .x15 .x12 152 (O+4)] else []) ++
    [.offset .x10 .x12 (-184) (E-6)]
  else if fromRegs p then
    [.store .x10 .x14 (-120) (O-15),.store .x10 .x15 (-112) (O-14),.store .x10 .x16 64 (O+8),
     .store .x10 .x17 72 (O+9),.offset .x10 .x10 (-304) (E-6)]
  else
    [.load .x31 .x12 (srcImm (2*p)) (srcWord (2*P)),.store .x10 .x31 (-120) (O-15),
     .load .x31 .x12 (srcImm (2*p)+8) (srcWord (2*P)+1),.store .x10 .x31 (-112) (O-14),
     .load .x31 .x12 (srcImm (2*p+1)) (srcWord (2*P+1)),.store .x10 .x31 64 (O+8),
     .load .x31 .x12 (srcImm (2*p+1)+8) (srcWord (2*P+1)+1),.store .x10 .x31 72 (O+9),
     .offset .x10 .x10 (-304) (E-6)]) ++
  [.store .x10 .x10 0 (E-6),.offset .x12 .x20 (heapImm (2*p)) (qLeaf (2*P)),.perm (E-6) (qLeaf (2*P))] ++
  (if rebase (2*p) then [.add .x20 .x20 .x23 (cursor (2*P+1))] else []) ++
  [.offset .x10 .x10 360 (O+7),.store .x10 .x10 0 (O+7),.offset .x12 .x20 (heapImm (2*p+1)) (qLeaf (2*P+1)),
   .perm (O+7) (qLeaf (2*P+1))] ++
  (if rebase (2*p+1) then [.add .x20 .x20 .x23 (cursor (2*P+2))] else [])

theorem pair_plan_words (P : Nat) : (pairPlan P).map Action.op=pairPacket (P%2048) := by
  by_cases h : pairHead (P%2048) <;> by_cases a : prefetchA (P%2048) <;> by_cases b : P%2048%11=5 <;>
    by_cases t : fromRegs (P%2048) <;> by_cases r : rebase (2*(P%2048)) <;> by_cases r' : rebase (2*(P%2048)+1) <;>
    simp only [pairPlan,pairPacket,h,a,b,t,r,r',ite_true,ite_false,List.map_append,List.map_cons,List.map_nil,Action.op]

theorem pair_plan_fetch (P : Nat) : fetchOps (pairWord (P%2048)) (pairPlan P) := by
  intro j s pc
  have len := congrArg List.length (pair_plan_words P)
  simp only [List.length_map] at len
  have inside : j.val<(pairPacket (P%2048)).length := len ▸ j.isLt
  have got := fetch_pair_packet ⟨P%2048,by omega⟩ j.val inside s pc
  rw [←pair_plan_words,List.getElem?_eq_getElem (by simpa using j.isLt)] at got
  change fetch image s=some (.base (pairPlan P)[j.val].op)
  simpa only [List.getElem_map,Option.getD_some] using got

theorem centered_imm : ∀ x : Fin 4096, signExtend12 (BitVec.ofNat 12 (2048+x.val))=-(2048:Word)+BitVec.ofNat 64 x.val := by
  decide +kernel

theorem heap_address (i : Nat) : wordAddress (cursor i)+signExtend12 (heapImm (i%4096))=wordAddress (qLeaf i) := by
  have low : 4096*rb (i%4096)≤slotOff (i%4096) := by unfold rb;omega
  have bound : slotOff (i%4096)-4096*rb (i%4096)<4096 := by unfold rb;omega
  have atSlot := centered_imm ⟨slotOff (i%4096)-4096*rb (i%4096),bound⟩
  simp only [Fin.val_mk] at atSlot
  unfold heapImm
  rw [show 2048+slotOff (i%4096)-4096*rb (i%4096)=2048+(slotOff (i%4096)-4096*rb (i%4096)) by omega,atSlot]
  unfold cursor
  rw [wordAddress_add]
  change (wordAddress _+2048)+(-2048+BitVec.ofNat 64 _)=_
  refine (QuartetLeaves.centered_add (wordAddress (qSource (1024*(i/4096))+512*rb (i%4096)))
    (slotOff (i%4096)-4096*rb (i%4096))).trans ?_
  unfold wordAddress qLeaf qSource
  rw [←BitVec.ofNat_add]
  congr 1 <;> (try simp only [slotOff] at low ⊢) <;> omega

end TwoPermutationPrototype.Grouped
