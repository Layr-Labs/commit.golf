import CommitGolfCandidate.TruncCommitRun
import CommitGolfCandidate.TruncHeap
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8000
set_option maxHeartbeats 160000

def parentStep (o : Oracle) (q : Nat) (s : MachineState) :=
  advance q s (parentAnswer o s (31-lane q))

theorem stepMem (o : Oracle) (q : Nat) (s : MachineState) (f : ParentFrame q s) (small : q<2^24) :
    (parentStep o q s).mem =
      (writeBits s (BitVec.ofNat 64 (heapBase+heapOffset q)) (storeNode q (parentAnswer o s (31-lane q)))).mem := by
  have e:= (parentAddresses q small s f.toRegFrame).2
  have ptr:parentOutput s (31-lane q)=BitVec.ofNat 64 (heapBase+heapOffset q) :=
    (word_ofNat_toNat _).trans (congrArg (BitVec.ofNat 64) e)
  unfold parentStep advance
  rw [nextMem,laneMem,correctBankMask,ptr]
  by_cases m : masked q <;> simp [storeNode,m]

theorem stepValue (o : Oracle) (q : Nat) (s : MachineState) (f : ParentFrame q s) (small : q<2^24)
    (gap : readBuffer s (heapBase+96*q+64) 32=0) :
    heapDigest (parentStep o q s) heapBase q =
      parent o.compression q (heapDigest s heapBase (2*q)) (heapDigest s heapBase (2*q+1)) := by
  have a:=parentAddresses q small s f.toRegFrame
  have query:=parent_answer_combine o s (31-lane q) heapBase q a.1 (by decide) gap
  unfold heapDigest
  rw [read_buffer_memory_congr _ _ (stepMem o q s f small)]
  have w:=write_bits_digest s (heapBase+heapOffset q) 0 (storeNode q (parentAnswer o s (31-lane q))) (by decide)
    (by decide)
  simpa only [Nat.add_zero,Nat.mul_zero,BitVec.extractLsb'_eq_self,query,parent,heapDigest] using w

theorem stepOutside (o : Oracle) (q : Nat) (s : MachineState) (f : ParentFrame q s) (small : q<2^24)
    (a len : Nat) (ba : a+len≤2^64)
    (disjoint : a+len≤heapBase+heapOffset q ∨ heapBase+heapOffset q+32≤a) :
    readBuffer (parentStep o q s) a len=readBuffer s a len := by
  rw [read_buffer_memory_congr _ _ (stepMem o q s f small)]
  apply write_bits_read_outside <;> first | exact ba | exact disjoint | unfold heapBase heapOffset;omega

def Consistent (o : Oracle) (q : Nat) (s : MachineState) :=
  ∀ i,q< i → i<LENGTH → heapDigest s heapBase i=parent o.compression i (heapDigest s heapBase (2*i)) (heapDigest s heapBase (2*i+1))

theorem stepOther (o : Oracle) (q : Nat) (s : MachineState) (f : ParentFrame q s) (small : q<2^24)
    (i : Nat) (hi : i<2*LENGTH) (ne : i≠q) :
    heapDigest (parentStep o q s) heapBase i=heapDigest s heapBase i := by
  have sep:=heap_offset_disjoint i q ne
  unfold heapDigest
  apply stepOutside o q s f small _ _ (by change i<33554432 at hi;unfold heapBase heapOffset;omega)
  omega

theorem stepConsistent (o : Oracle) (k : Nat) (s : MachineState) (f : ParentFrame (k+1) s) (small : k+1<LENGTH)
    (old : Consistent o (k+1) s) (gap : readBuffer s (heapBase+96*(k+1)+64) 32=0) :
    Consistent o k (parentStep o (k+1) s) := by
  intro i lo hi
  have pos : 0< i := by omega
  rw [stepOther o (k+1) s f small (2*i) (by omega) (by omega),
      stepOther o (k+1) s f small (2*i+1) (by omega) (by omega)]
  by_cases eq : i=k+1
  · subst i;exact stepValue o _ s f small gap
  · rw [stepOther o (k+1) s f small i (by omega) eq];exact old i (by omega) hi

def Gaps (s : MachineState) := ∀ j, j<LENGTH → readBuffer s (heapBase+96*j+64) 32=0

theorem stepGaps (o : Oracle) (q : Nat) (s : MachineState) (f : ParentFrame q s) (small : q<LENGTH) (g : Gaps s) :
    Gaps (parentStep o q s) := by
  intro j hj
  rw [stepOutside o q s f small _ _ (by change j<16777216 at hj;unfold heapBase;omega)]
  · exact g j hj
  · have h:=heap_offset_gap q j
    omega

theorem parentsConsistent (o : Oracle) (q : Nat) (s : MachineState) (f : ParentFrame q s) (small : q<LENGTH)
    (c : Consistent o q s) (g : Gaps s) : Consistent o 0 (fixedParents o q s) := by
  induction q generalizing s with
  | zero => exact c
  | succ q ih =>
    exact ih _ (advanceFrame (q+1) (by omega) s _ f) (by omega)
      (stepConsistent o q s f small c (g _ small)) (stepGaps o _ s f small g)

theorem parentsOutside (o : Oracle) (q : Nat) (s : MachineState) (f : ParentFrame q s) (small : q<LENGTH)
    (a len : Nat) (b : a+len≤2^64) (away : ∀ i,0< i → i≤q → a+len≤heapBase+heapOffset i ∨ heapBase+heapOffset i+32≤a) :
    readBuffer (fixedParents o q s) a len=readBuffer s a len := by
  induction q generalizing s with
  | zero => rfl
  | succ q ih =>
    exact (ih _ (advanceFrame (q+1) (by omega) s _ f) (by omega) (fun i lo hi=>away i lo (by omega))).trans
      (stepOutside o (q+1) s f small a len b (away _ (by omega) le_rfl))

end CommitGolfCandidate.Trunc
