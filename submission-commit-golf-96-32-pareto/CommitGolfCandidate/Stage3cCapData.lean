import CommitGolfCandidate.Stage3cCapLayout
import CommitGolfCandidate.Stage3cSlotLoop
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W Outside)
def slotValue (x : CheckInput) (_q : Fin 4) (j : Nat) :=(Pw.batchView x).slot j
def pairValue (H : Compression) (a b : Option Late.Digest) (v : Late.Digest) : Late.Digest :=
  if a.isNone && b.isNone then v else Chained.parentDigest H (Pw.height 15) (a.getD v) (b.getD v)
theorem pair_model (H : Compression) (x : CheckInput) (q : Fin 4) (j : Nat) :
    pairValue H (lookup H x 128 (2*j)) (lookup H x 128 (2*j+1)) (slotValue x q j)=Pw.Auth.batchCap H (Pw.batchView x) j := by
  unfold Pw.Auth.batchCap Pw.Auth.pairAt Pw.Auth.pairChildren Pw.Auth.mergePair
  change pairValue H _ _ _=(if _ then _ else _)
  unfold pairValue
  have low (a : Nat) : lookup H x 128 a=Pw.Auth.select (Pw.batchView x) (Pw.Auth.lower H (Pw.batchView x)) a:=rfl
  rw [low,low];split
  · rfl
  · have material (a b : Late.Digest) : Pw.Auth.compressRow H 16 (Late.parentBlock a b)=Chained.parentDigest H (Pw.height 15) a b :=
      Pw.Auth.row_parent H 15 a b 0
    exact (material _ _).symm

structure Evidence (H : Compression) (x : CheckInput) (q : Fin 4) (s : MachineState) : Prop where
  mark : ∀ j<512,Open.byteAt s (marksBuf+j)=markBit (lookup H x 128 j)
  computed : ∀ j<512,∀ v,lookup H x 128 j=some v → readBuffer s (bucketAddress j) 32=v
  slot : ∀ j<256,readBuffer s (slotAddr j) 32=slotValue x q j
  root : readBuffer s rootBase 32=x.commitment
theorem Evidence.same {H x q s t} (old : Evidence H x q s) (mem : t.mem=s.mem) : Evidence H x q t :=
  ⟨fun j h=>(Open.byte_mem mem _).trans (old.mark j h),fun j h v e=>(read_buffer_memory_congr t s mem _ _).trans (old.computed j h v e),
    fun j h=>(read_buffer_memory_congr t s mem _ _).trans (old.slot j h),(read_buffer_memory_congr t s mem _ _).trans old.root⟩

theorem ChainOutside.byte {s t dst} (changed : ChainOutside s t dst) (a : Nat) (fit : a<MEMORY_BYTES)
    (scratch : a<rowBuf ∨ rowBuf+352≤a) (sep : a<dst ∨ dst+32≤a) (da : dst%8=0) : Open.byteAt t a=Open.byteAt s a := by
  have al : rowBuf%8=0:=by decide
  rw [Open.byte_word,Open.byte_word s,changed _ (by omega) (by omega) (by omega) (by omega)]
theorem Evidence.after_node {H x q s t dst} (old : Evidence H x q s) (frame : ChainOutside s t dst)
    (lo : capBase≤dst) (end_ : dst+32≤saltBuf) (al : dst%8=0) : Evidence H x q t := by
  constructor
  · intro j small
    apply (frame.byte _ (by dsimp [marksBuf,MEMORY_BYTES];omega) (Or.inr (by dsimp [rowBuf,marksBuf];omega))
      (Or.inl (by dsimp [marksBuf];unfold capBase at lo;omega)) al).trans (old.mark j small)
  · intro j small v e
    apply (frame.read (bucketAddress j) 32 (by dsimp [bucketAddress,compBase,MEMORY_BYTES];omega)
      (Or.inr (by dsimp [bucketAddress,compBase,rowBuf];omega)) (Or.inl (by dsimp [bucketAddress,compBase];unfold capBase at lo;omega)) al).trans (old.computed j small v e)
  · intro j small;apply (frame.read (slotAddr j) 32 (by dsimp [slotAddr,slotBase,MEMORY_BYTES];omega)
      (Or.inr (by dsimp [slotAddr,slotBase,rowBuf];omega)) (Or.inl (by dsimp [slotAddr,slotBase];unfold capBase at lo;omega)) al).trans (old.slot j small)
  · apply (frame.read rootBase 32 (by decide) (Or.inr (by decide)) (Or.inr (end_.trans (by decide))) al).trans old.root

def capVal (H : Compression) (x : CheckInput) (_q : Fin 4) (d j : Nat) :=Pw.Auth.upper H (Pw.Auth.batchCap H (Pw.batchView x)) d j
def progress (H : Compression) (x : CheckInput) (d p : Nat) : Values := fun h i=>
  if h<d ∨ h=d ∧ i<p then capVal H x 0 h i else 0
theorem write_progress (H : Compression) (x : CheckInput) (d p : Nat) :
    replaceNode (progress H x d p) d p (capVal H x 0 d p)=progress H x d (p+1):=by
  funext h j
  by_cases same : h=d
  · subst h;by_cases eq : j=p
    · subst j;simp [replaceNode,progress]
    · have before : j<p ↔ j<p+1:=by omega
      simp [replaceNode,progress,eq,before]
  · simp [replaceNode,progress,same]
theorem advance_progress (H : Compression) (x : CheckInput) (d : Nat) :
    progress H x d (layerCount d)=progress H x (d+1) 0 := by
  funext h j;unfold progress
  by_cases before : h<d
  · simp [before,show h<d+1 by omega]
  by_cases same : h=d
  · subst h;by_cases exists_ : j<layerCount d
    · simp [exists_]
    · simp only [Nat.lt_irrefl,exists_,and_false,or_false,ite_false,Nat.lt_succ_self,true_or,ite_true]
      unfold capVal;cases d
      · change 0=(if j<256 then _ else 0);rw [if_neg (show ¬j<256 from exists_)]
      · rename_i k
        rw [Pw.Auth.upper,if_neg (show ¬j<Geo.width (17+k) by simpa only [layerCount,show 16+(k+1)=17+k by omega] using exists_)]
  · have beyond : ¬h<d+1:=by omega
    simp [before,same,beyond]
end CommitGolfCandidate.Chained.BinaryMachine.Check
