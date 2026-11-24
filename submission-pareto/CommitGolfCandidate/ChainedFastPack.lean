import CommitGolfCandidate.ChainedFastLayout
import CommitGolfCandidate.ChainedFirstPackValue
import CommitGolfCandidate.ChainedHeapAddress
import CommitGolfCandidate.WriteMemory
import CommitGolfCandidate.TwoPermutationInputWords

/-! Word-addressed scratch, parent and child slots for one descending node.
The child cursor addresses the first pair in the unrolled group and not necessarily
the pair at this lane. Registers x6 and x7 only move at the group latch. -/
namespace CommitGolfCandidate.Chained.Native.Fast
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

abbrev W (n : Nat) := BitVec.ofNat 64 n
abbrev Slot := Fin 20
/-- Slots 0..7 are the children, 8..11 the output, 12..19 the 64-byte chain window. -/
def address (n : Nat) (i : Slot) :=
  if i.val<8 then heapBase+64*n+8*i.val else if i.val<12 then heapBase+32*n+8*(i.val-8)
  else 224+8*(i.val-12)

structure Bounds (n : Nat) : Prop where
  lower : 65536≤n
  upper : n<2^24

theorem aligned (n : Nat) (i : Slot) : address n i % 8=0 := by
  unfold address heapBase;split_ifs <;> omega

theorem address_room {n : Nat} (b : Bounds n) (i : Slot) : address n i+64≤2^36 := by
  have := b.upper;have := i.isLt
  unfold address heapBase; split_ifs <;> omega

theorem address_inj {n : Nat} (b : Bounds n) (i j : Slot) : address n i=address n j ↔ i=j := by
  constructor
  · intro eq;apply Fin.ext;have:=b.lower;have:=i.isLt;have:=j.isLt
    unfold address heapBase at eq;split_ifs at eq <;> omega
  · rintro rfl;rfl

theorem word_addr {n : Nat} (b : Bounds n) (i : Slot) : (W (address n i)).toNat=address n i := by
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have:=address_room b i;omega)]

theorem access {n : Nat} (b : Bounds n) (i : Slot) : accessValid (W (address n i)) 8=true := by
  have := address_room b i
  simp [accessValid,rangeValid,word_addr b,aligned,MEMORY_BYTES] <;> omega

theorem childImm (k : Lane) (i : Fin 8) : signExtend12 (childOff k i.val) =
    W (8*i.val)-W (64*k.val) := by
  exact (show ∀ (a : Lane) (j : Fin 8), signExtend12 (childOff a j.val)=W (8*j.val)-W (64*a.val) by decide) k i

theorem parentImm (k : Lane) : signExtend12 (parentOff k) = -W (32*k.val) := by
  exact (show ∀ a : Lane, signExtend12 (parentOff a) = -W (32*a.val) by decide) k

theorem child_effective (n : Nat) (k : Lane) (i : Fin 8) :
    heapAddress (2*(n+k.val))+signExtend12 (childOff k i.val)=W (address n ⟨i.val,by omega⟩) := by
  rw [childImm];simp only [address,show i.val<8 from i.isLt,ite_true,heapAddress]
  have ar : heapBase+32*(2*(n+k.val))=(heapBase+64*n)+64*k.val := by ring
  unfold W
  rw [ar,BitVec.ofNat_add,BitVec.sub_eq_add_neg,BitVec.add_assoc,←BitVec.add_assoc (BitVec.ofNat 64 (64*k.val)),
    BitVec.add_comm (BitVec.ofNat 64 (64*k.val)) (BitVec.ofNat 64 (8*i.val)),BitVec.add_assoc _ (BitVec.ofNat 64 (64*k.val)),
    BitVec.add_right_neg,BitVec.add_zero,←BitVec.ofNat_add]


theorem parent_effective (n : Nat) (k : Lane) :
    heapAddress (n+k.val)+signExtend12 (parentOff k)=W (address n 8) := by
  rw [parentImm];change W (heapBase+32*(n+k.val)) + -W (32*k.val)=W (heapBase+32*n+8*(8-8))
  unfold W
  rw [show heapBase+32*(n+k.val)=(heapBase+32*n)+32*k.val by ring,BitVec.ofNat_add,BitVec.add_assoc,
    BitVec.add_right_neg,BitVec.add_zero];rfl

theorem wordplus (a o : Nat) : W a + W o=W (a+o) := (BitVec.ofNat_add ..).symm

def cat8 (f : Fin 8→Word) : Input :=
  (f 7 ++ f 6 ++ f 5 ++ f 4) ++ (f 3 ++ f 2 ++ f 1 ++ f 0)

theorem read8 (s : MachineState) (a : Nat) (align : a%8=0) :
    readBuffer s a 64=cat8 (fun i=>s.getMem (W (a+8*i.val))) := by
  rw [read_compression_halves s a align,read_digest_words s (a+32) (by omega),read_digest_words s a align]
  simp [cat8,Nat.add_assoc]

theorem chain_domain (h : Low) (j : Fin 3) (s : MachineState) (a : Output)
    (lo:readBuffer s 224 32=a)
    (tag:s.getMem 256=W (7*h.val+j.val))
    (z0:s.getMem 264=0) (z1:s.getMem 272=0) (flag:s.getMem 280=2^63) :
    readBuffer s 224 64=canonicalEncoding.next (height h) (j.val+1) a := by
  have dom : DomainWords s 224 (height h) j.val := ⟨tag,z0,z1,flag⟩
  exact (domain_input s 224 _ _ (by have:=j.isLt;omega) (by decide) dom).trans (congrArg _ lo)

theorem written_word (s : MachineState) (v : Output) (a : Nat) (i : Fin 4) (align:a%8=0) :
    (writeBits s (W a) v).getMem (W (a+8*i.val))=v.extractLsb' (64*i.val) 64 := by
  have got:=write_bits_digest s a 0 v (by decide) (by decide)
  simp only [Nat.add_zero,Nat.mul_zero,BitVec.extractLsb'_eq_self] at got
  have word:=congrArg (fun x : Output => x.extractLsb' (64*i.val) 64) got
  rwa [read_digest_word _ _ _ align i.isLt] at word

theorem written_other (s : MachineState) (v : Output) (a q : Nat) (align:q%8=0)
    (bounds:a+32≤2^64) (qb:q+32≤2^64) (outside:q+8≤a ∨ a+32≤q) :
    (writeBits s (W a) v).getMem (W q)=s.getMem (W q) := by
  have bytes:=write_bits_read_outside s v a q 8 bounds (by omega) outside
  have eq : 8*(q/8)=q := by omega
  have read (t : MachineState) : readBuffer t q 8=t.getMem (W q) := by
    simpa only [TwoPermutationPrototype.RV64.memoryView,TwoPermutationPrototype.RV64.wordAddress,eq] using
      TwoPermutationPrototype.RV64.read_word t (q/8)
  simpa only [read] using bytes

end CommitGolfCandidate.Chained.Native.Fast
