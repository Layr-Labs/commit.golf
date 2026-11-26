import CommitGolfCandidate.TruncSteps
import CommitGolfCandidate.TruncLane
import CommitGolfCandidate.CommitTree
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8000
set_option maxHeartbeats 180000

def heapBase : Nat := 4294971424
def threshold : Nat := 4194304
def switchPtr : Nat := heapBase+48*(threshold-32)
def bank (q : Nat) : Bank := if threshold≤q then .low else if 32≤q then .high else if 2≤q then .tail else .root
def lane (q : Nat) := 31-q%32
def word (q : Nat) := if q=0 then 785 else startWord (bank q) (lane q)
def bodySteps (q : Nat) := if masked q then 4 else 3
def suffixSteps (q : Nat) := (if q%32=0 then 3 else 0)+(if q=threshold ∨ q=2 then 1 else 0)
def treeSteps (q : Nat) := 3*q+(min q (threshold-1)-1)+3*(q/32)+(if threshold≤q then 1 else 0)+(if 2≤q then 1 else 0)

theorem laneIn (q : Nat) (pos : 0<q) : inBank (bank q) (lane q) := by
  unfold bank lane threshold;split_ifs <;> simp only [inBank] <;> omega
theorem reverseLane (q : Nat) : 31-lane q=q%32 := by unfold lane;omega
theorem correctBankMask (q : Nat) : projectedBank (bank q)=decide (masked q) := by
  unfold bank threshold masked;split_ifs <;> simp only [projectedBank] <;> apply Eq.symm <;>
    first | apply decide_eq_true;omega | apply decide_eq_false;omega
private theorem lowWord (q : Nat) (lo : threshold≤q) : word q=593+3*lane q := by
  have nz : q≠0 := by unfold threshold at lo;omega
  simp only [word,bank,if_neg nz,if_pos lo,startWord]
private theorem highWord (q : Nat) (lo : 32≤q) (hi : q<threshold) : word q=802+4*lane q := by
  simp only [word,bank,if_neg (by omega : q≠0),if_neg (by omega : ¬threshold≤q),if_pos lo,startWord]
private theorem tailWord (q : Nat) (lo : 2≤q) (hi : q<32) : word q=933+4*lane q := by
  have sm : ¬threshold≤q := by unfold threshold;omega
  simp only [word,bank,if_neg (by omega : q≠0),if_neg sm,if_neg (by omega : ¬32≤q),if_pos lo,startWord]
private theorem lowPrice (q : Nat) (lo : threshold≤q) : bodySteps q=3 := by
  unfold threshold at lo;exact if_neg (by unfold masked;omega)
private theorem highPrice (q : Nat) (lo : 2≤q) (hi : q<threshold) : bodySteps q=4 :=
  if_pos ⟨lo,hi⟩

theorem totalSucc (q : Nat) : treeSteps (q+1)=bodySteps (q+1)+suffixSteps (q+1)+treeSteps q := by
  have masks : min (q+1) (threshold-1)-1 = (min q (threshold-1)-1)+(if masked (q+1) then 1 else 0) := by
    by_cases m : masked (q+1)
    · rw [if_pos m];unfold masked at m;unfold threshold;omega
    · rw [if_neg m];unfold masked at m;unfold threshold;omega
  have groups : 3*((q+1)/32) = 3*(q/32)+(if (q+1)%32=0 then 3 else 0) := by
    by_cases m : (q+1)%32=0
    · rw [if_pos m];omega
    · rw [if_neg m];omega
  have jump (t : Nat) : (if t≤q+1 then 1 else 0)=(if t≤q then 1 else 0)+(if q+1=t then 1 else 0) := by
    by_cases h : t≤q
    · rw [if_pos h,if_pos (by omega : t≤q+1),if_neg (by omega : q+1≠t)]
    · rw [if_neg h];by_cases e : q+1=t
      · rw [if_pos e,if_pos (by omega : t≤q+1)]
      · rw [if_neg e,if_neg (by omega : ¬t≤q+1)]
  have sum : ((if q+1=threshold then 1 else 0)+(if q+1=2 then 1 else 0)) =
      (if q+1=threshold ∨ q+1=2 then 1 else 0) := by
    have ne : threshold≠2 := by decide
    by_cases t : q+1=threshold
    · rw [if_pos t,if_neg (by omega : q+1≠2),if_pos (Or.inl t)]
    · rw [if_neg t];by_cases d : q+1=2
      · rw [if_pos d,if_pos (Or.inr d)]
      · rw [if_neg d,if_neg (not_or.mpr ⟨t,d⟩)]
  unfold treeSteps bodySteps suffixSteps
  rw [masks,groups,jump threshold,jump 2]
  by_cases m : masked (q+1)
  · rw [if_pos m,if_pos m];omega
  · rw [if_neg m,if_neg m];omega

theorem straightNext (q : Nat) (pos : 0<q) (h : q%32≠0) (ne : q≠2) :
    word q+bodySteps q=word (q-1) := by
  have thr : threshold=4194304 := rfl
  by_cases low : threshold≤q
  · have prev : threshold≤q-1 := by omega
    rw [lowWord q low,lowWord _ prev,lowPrice q low];unfold lane;omega
  · have hi : q<threshold := by omega
    by_cases upper : 32≤q
    · rw [highWord q upper hi,highWord _ (by omega) (by omega),highPrice q (by omega) hi];unfold lane;omega
    · by_cases one : q=1
      · subst q;decide
      · rw [tailWord q (by omega) (by omega),tailWord _ (by omega) (by omega),highPrice q (by omega) hi];unfold lane;omega

theorem beforeLatch (q : Nat) (pos : 0<q) (h : q%32=0) :
    word q+bodySteps q=if threshold≤q then 689 else 930 := by
  by_cases low : threshold≤q
  · rw [if_pos low,lowWord q low,lowPrice q low];simp [lane,h]
  · rw [if_neg low,highWord q (by omega) (by omega),highPrice q (by omega) (by omega)];simp [lane,h]

theorem afterLatch (q : Nat) (pos : 0<q) (h : q%32=0) :
    word (q-1)=if threshold<q then 593 else if 32<q then 802 else 933 := by
  have t : threshold=4194304 := rfl
  by_cases low : threshold<q
  · rw [if_pos low,lowWord _ (by omega)];unfold lane;omega
  · rw [if_neg low];by_cases upper : 32<q
    · rw [if_pos upper,highWord _ (by omega) (by omega)];unfold lane;omega
    · have eq : q=32 := by omega
      subst q;decide

structure RegFrame (q : Nat) (s : MachineState) : Prop where
  pointers : ParentPointers s heapBase (q/32)
  switch : s.getReg .x17=BitVec.ofNat 64 switchPtr
  root : s.getReg .x26=4294971392
  r5 : s.getReg .x5=0
  r11 : s.getReg .x11=96
  r13 : s.getReg .x13=0

structure ParentFrame (q : Nat) (s : MachineState) extends RegFrame q s : Prop where
  pc : s.pc=loc (word q)

def nextState (q : Nat) (s : MachineState) :=
  (if q%32=0 then parentNextState s else s).setPC (loc (word (q-1)))

theorem nextMem (q : Nat) (s : MachineState) : (nextState q s).mem=s.mem := by
  unfold nextState;split <;> rfl

theorem laneFrame (b : Bank) (s : MachineState) (u : Nat) (v : Digest) (q : Nat) (f : RegFrame q s) :
    RegFrame q (laneState b s u v) :=
  let keep (r : Reg) (a : r≠.x10) (c : r≠.x12) := laneKept b s u v r a c
  ⟨⟨(keep .x9 (by decide) (by decide)).trans f.pointers.heap,(keep .x21 (by decide) (by decide)).trans f.pointers.src,
    (keep .x22 (by decide) (by decide)).trans f.pointers.dst,(keep .x24 (by decide) (by decide)).trans f.pointers.stride⟩,
    (keep .x17 (by decide) (by decide)).trans f.switch,(keep .x26 (by decide) (by decide)).trans f.root,
    (keep .x5 (by decide) (by decide)).trans f.r5,(keep .x11 (by decide) (by decide)).trans f.r11,
    (keep .x13 (by decide) (by decide)).trans f.r13⟩

theorem boundHeap (q : Nat) (h : q<2^24) : heapBase+3072*(q/32)+3072≤MEMORY_BYTES := by
  change 4294971424+3072*(q/32)+3072≤2^36;omega

theorem parentAddresses (q : Nat) (h : q<2^24) (s : MachineState) (f : RegFrame q s) :
    (parentSource s (31-lane q)).toNat=heapBase+96*q ∧
    (parentOutput s (31-lane q)).toNat=heapBase+heapOffset q := by
  rw [reverseLane]
  have p:=parent_addresses s heapBase (q/32) (q%32) (Nat.mod_lt _ (by decide)) f.pointers (boundHeap q h)
  rwa [show 32*(q/32)+q%32=q by omega] at p

theorem validLane (q : Nat) (h : q<2^24) (s : MachineState) (f : RegFrame q s) :
    ParentCallValid s (31-lane q) := by
  have a:=parentAddresses q h s f
  simp only [ParentCallValid,rangeValid,decide_eq_true_eq,a.1,a.2,heapBase,heapOffset,MEMORY_BYTES];omega

theorem dropPtr {s : MachineState} (k : Nat) (ptr : ParentPointers s heapBase (k+1)) :
    ParentPointers (parentNextState s) heapBase k := by
  have next:=parent_next_registers s
  refine ⟨(next.2.2.2 .x9 (by decide) (by decide)).trans ptr.heap,?_,?_,
    (next.2.2.2 .x24 (by decide) (by decide)).trans ptr.stride⟩
  · rw [next.1,ptr.src,ptr.stride]
    change BitVec.ofNat 64 (heapBase+3072*(k+1)+1536)-BitVec.ofNat 64 3072=_
    rw [word_sub_literal (heapBase+3072*(k+1)+1536) 3072 (by omega) (by decide)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  · rw [next.2.1,ptr.dst]
    change BitVec.ofNat 64 (heapBase+1536*(k+1))-BitVec.ofNat 64 1536=_
    rw [word_sub_literal (heapBase+1536*(k+1)) 1536 (by omega) (by decide)]
    exact congrArg (BitVec.ofNat 64) (by omega)

theorem nextFrame (q : Nat) (pos : 0<q) (s : MachineState) (f : RegFrame q s) :
    ParentFrame (q-1) (nextState q s) := by
  by_cases hit : q%32=0
  · have wrap : q/32=(q-1)/32+1 := by omega
    have ptr:=f.pointers;rw [wrap] at ptr
    have keep := (parent_next_registers s).2.2.2
    simp only [nextState,if_pos hit]
    refine ⟨⟨?_,(keep .x17 (by decide) (by decide)).trans f.switch,(keep .x26 (by decide) (by decide)).trans f.root,
      (keep .x5 (by decide) (by decide)).trans f.r5,(keep .x11 (by decide) (by decide)).trans f.r11,
      (keep .x13 (by decide) (by decide)).trans f.r13⟩,rfl⟩
    have p:=dropPtr ((q-1)/32) ptr
    exact ⟨p.heap,p.src,p.dst,p.stride⟩
  · have same : (q-1)/32=q/32 := by omega
    simp only [nextState,if_neg hit]
    refine ⟨⟨?_,f.switch,f.root,f.r5,f.r11,f.r13⟩,rfl⟩
    rw [same];exact ⟨f.pointers.heap,f.pointers.src,f.pointers.dst,f.pointers.stride⟩

end CommitGolfCandidate.Trunc
