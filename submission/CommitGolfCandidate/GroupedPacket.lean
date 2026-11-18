import CommitGolfCandidate.GroupedKernel
import CommitGolfCandidate.GroupedCommitImage
import CommitGolfCandidate.QuartetCommitRanges
import CommitGolfCandidate.QuartetCommitLeafOps

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.QuartetCommit (qSource qSalt qLeaf)
set_option maxRecDepth 16000
set_option maxHeartbeats 1800000

def msgWord (i : Nat) := 512+32*i
def groupBuffer (i : Nat) := msgWord (i-rank i)-15
def pairBuffer (i : Nat) := msgWord (i-pairPos i)-15
def saltAnchor (i : Nat) := pairBuffer i+192
def cursor (i : Nat) := qSource (8*(i/32))+256
def sourceWord (i : Nat) := groupBuffer i+2*(rank i-1)

def plan (i : Nat) : List Action :=
  let m := msgWord i
  let n := i%4096
  [.offset .x12 .x10 (-32) (m-4),.perm m (m-4)] ++
  (if rank n=0 then
    [.store .x24 .x10 0 (qSalt 0),.offset .x12 .x10 (-120) (m-15),
     .offset .x10 .x24 0 (qSalt 0),.perm (qSalt 0) (m-15)] ++
    (if pairPos n=0 then [.offset .x7 .x12 1536 (saltAnchor i)] else []) ++
    [.offset .x10 .x12 176 (m+7),.store .x10 .x10 0 (m+7)]
  else [.offset .x10 .x10 56 (m+7),.store .x10 .x10 0 (m+7),
     .load .x31 .x7 (sourceImm n) (sourceWord i),.store .x10 .x31 8 (m+8),
     .load .x31 .x7 (sourceImm n+8) (sourceWord i+1),.store .x10 .x31 16 (m+9)]) ++
  [.offset .x12 .x20 (heapImm n) (qLeaf i),.perm (m+7) (qLeaf i),
   .offset .x10 .x10 200 (msgWord (i+1))] ++
  (if n%32=31 then [.add .x20 .x20 .x23 (cursor (i+1))] else [])

theorem plan_words (i : Nat) : (plan i).map Action.op=packet (i%4096) := by
  by_cases h : rank (i%4096)=0 <;> by_cases p : pairPos (i%4096)=0 <;> by_cases k : i%32=31 <;>
    simp [plan,packet,h,k,Action.op,p]

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
  msg : s.getReg .x10=wordAddress (msgWord i)
  heap : s.getReg .x20=wordAddress (cursor i)
  stride : s.getReg .x23=4096
  counter : s.getReg .x24=wordAddress (qSalt 0)
  buf : pairPos i≠0 → s.getReg .x7=wordAddress (saltAnchor i)
  selector : s.getReg .x5=0
  size : s.getReg .x11=200
  primitive : s.getReg .x13=1

theorem within_rank (i : Nat) : rank (i%4096)=rank i := by
  unfold rank;rw [show i%4096%2048=i%2048 by omega]

theorem within_pair (i : Nat) : pairPos (i%4096)=pairPos i := by
  unfold pairPos;rw [show i%4096%2048=i%2048 by omega]

theorem heap_address (i : Nat) : wordAddress (cursor i)+signExtend12 (heapImm (i%4096))=wordAddress (qLeaf i) := by
  have off : ∀ k : Fin 32, signExtend12 (BitVec.ofNat 12 (2048+512*(k.val/4)+72+32*(k.val%4)))=
      -(2048:Word)+BitVec.ofNat 64 (512*(k.val/4)+72+32*(k.val%4)) := by decide
  have atSlot := off ⟨i%32,by omega⟩
  simp only [Fin.val_mk] at atSlot
  unfold heapImm
  rw [show (i%4096/4)%8=i%32/4 by omega,show i%4096%4=i%32%4 by omega,atSlot]
  unfold cursor
  rw [wordAddress_add]
  change (wordAddress _+2048)+(-2048+BitVec.ofNat 64 _)=_
  refine (QuartetLeaves.centered_add (wordAddress (qSource (8*(i/32)))) (512*(i%32/4)+72+32*(i%32%4))).trans ?_
  unfold wordAddress qLeaf qSource
  rw [←BitVec.ofNat_add]
  congr 1 <;> omega

theorem src_address (i : Nat) (d : Fin 2) :
    wordAddress (saltAnchor i)+signExtend12 (sourceImm (i%4096)+BitVec.ofNat 12 (8*d.val))=
      wordAddress (sourceWord i+d.val) := by
  have tab : ∀ i : Fin 22, ∀ d : Fin 2,
      signExtend12 (BitVec.ofNat 12 (2560+2816*(i.val/11)+16*(i.val%11-1))+BitVec.ofNat 12 (8*d.val))=
        QuartetLeaves.centeredOffset (512+2816*(i.val/11)+16*(i.val%11-1)+8*d.val) := by decide +kernel
  have val:=tab ⟨i%2048%22,by omega⟩ d
  simp only [Fin.val_mk] at val
  rw [show i%2048%22/11=i%2048/11%2 by omega, show i%2048%22%11=i%2048%11 by omega] at val
  unfold sourceImm rank;rw [show i%4096%2048=i%2048 by omega,val]
  have da : wordAddress (saltAnchor i)=wordAddress (pairBuffer i-64)+2048 := by
    change wordAddress (_+192)=wordAddress (_-64)+wordAddress 256
    rw [←wordAddress_add];congr 1;unfold pairBuffer msgWord;omega
  rw [da,QuartetLeaves.centered_add]
  change BitVec.ofNat 64 _+BitVec.ofNat 64 _=BitVec.ofNat 64 _
  rw [←BitVec.ofNat_add];congr 1
  unfold pairBuffer sourceWord groupBuffer msgWord rank pairPos
  have bound : i % 2048 ≤ i := Nat.mod_le ..
  have e : i%2048%22=i%2048%11+11*(i%2048/11%2) := by omega
  have z : i % 2048 % 22 ≤ i := by have:=Nat.mod_le (i%2048) 22;omega
  have y : i % 2048 % 11 ≤ i :=by have:=Nat.mod_le (i%2048) 11;omega
  omega

private theorem word_disp (i : Nat) (d : Nat) : wordAddress i+BitVec.ofNat 64 (8*d)=wordAddress (i+d) :=
  (wordAddress_add i d).symm

theorem packet_addrs (i : Nat) :
    wordAddress (msgWord i)+signExtend12 (-32)=wordAddress (msgWord i-4) ∧
    wordAddress (msgWord i)+signExtend12 (-120)=wordAddress (msgWord i-15) ∧
    wordAddress (msgWord i)+signExtend12 56=wordAddress (msgWord i+7) ∧
    wordAddress (msgWord i-15)+signExtend12 176=wordAddress (msgWord i+7) ∧
    wordAddress (msgWord i+7)+signExtend12 8=wordAddress (msgWord i+8) ∧
    wordAddress (msgWord i+7)+signExtend12 16=wordAddress (msgWord i+9) ∧
    wordAddress (msgWord i+7)+signExtend12 200=wordAddress (msgWord (i+1)) := by
  have m4 : msgWord i=(msgWord i-4)+4 := by unfold msgWord;omega
  have m15 : msgWord i=(msgWord i-15)+15 := by unfold msgWord;omega
  refine ⟨?_,?_,word_disp (msgWord i) 7,?_,?_,?_,?_⟩
  · conv_lhs => rw [m4,wordAddress_add]
    rw [BitVec.add_assoc];exact BitVec.add_zero _
  · conv_lhs => rw [m15,wordAddress_add]
    rw [BitVec.add_assoc];exact BitVec.add_zero _
  · exact (word_disp (msgWord i-15) 22).trans (congrArg wordAddress (by unfold msgWord;omega))
  · exact word_disp (msgWord i+7) 1
  · exact word_disp (msgWord i+7) 2
  · exact (word_disp (msgWord i+7) 25).trans (congrArg wordAddress (by unfold msgWord;omega))

end TwoPermutationPrototype.Grouped
