import CommitGolfCandidate.S5SlotRead
import CommitGolfCandidate.S5CheckNode
namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W Outside)
def layerStart (d : Nat):=([98304,106560,110688,112800,113856,114432,114720,114912,115008] : List Nat)[d]?.getD 0
def layerCount (d : Nat):=S4.width (16+d)
def groups (d : Nat):=(layerCount d+1)/2
def paddedCount (d : Nat):=if d=8 then 1 else 2*groups d
def areaEnd (d : Nat):=layerStart d+(if d=8 then 32 else 96*groups d)
def nodeAt (d i : Nat):=layerStart d+96*(i/2)+32*(i%2)
def rowAt (d j : Nat):=layerStart d+96*j
def gapAt (d j : Nat):=rowAt d j+64

theorem cap_geometry : ∀ d : Fin 9,capBase≤layerStart d.val ∧ areaEnd d.val≤saltBuf ∧ layerStart d.val%8=0 ∧
  0<layerCount d.val ∧ layerCount d.val≤paddedCount d.val ∧ paddedCount d.val≤172 ∧
  (d.val<8 → groups d.val=layerCount (d.val+1)) ∧
  (∀ e : Fin 9,d.val<e.val → areaEnd d.val≤layerStart e.val) :=by decide +kernel

theorem node_range (d i : Nat) (hd : d<9) (hi : i<paddedCount d) :
    layerStart d≤nodeAt d i ∧ nodeAt d i+32≤areaEnd d ∧ nodeAt d i%8=0 := by
  obtain ⟨_,_,align,_⟩:=cap_geometry ⟨d,hd⟩
  change layerStart d%8=0 at align
  unfold nodeAt areaEnd;unfold paddedCount at hi;by_cases z:d=8 <;> simp only [z,ite_true,ite_false] at hi align ⊢ <;> omega

theorem gap_range (d j : Nat) (hd : d<8) (hj : j<groups d) :
    layerStart d≤gapAt d j ∧ gapAt d j+32≤areaEnd d ∧ gapAt d j%8=0 := by
  have align:=(cap_geometry ⟨d,by omega⟩).2.2.1
  change layerStart d%8=0 at align
  unfold gapAt rowAt areaEnd;rw [if_neg (by omega : d≠8)];omega

theorem node_apart (d h i j : Nat) (bd : d<9) (bh : h<9) (bi : i<paddedCount d) (bj : j<paddedCount h)
    (different : d≠h ∨ i≠j) : nodeAt d i+32≤nodeAt h j ∨ nodeAt h j+32≤nodeAt d i := by
  obtain ⟨lo,hi,_⟩:=node_range d i bd bi
  obtain ⟨lo',hi',_⟩:=node_range h j bh bj
  by_cases dl : d<h
  · have e:=(cap_geometry ⟨d,bd⟩).2.2.2.2.2.2.2 ⟨h,bh⟩ dl;exact Or.inl (hi.trans (e.trans lo'))
  by_cases hl : h<d
  · have e:=(cap_geometry ⟨h,bh⟩).2.2.2.2.2.2.2 ⟨d,bd⟩ hl;exact Or.inr (hi'.trans (e.trans lo))
  have eq : d=h:=by omega
  subst d;unfold nodeAt;omega

theorem gap_apart (d h i j : Nat) (bd : d<8) (bh : h<9) (bi : i<groups d) (bj : j<paddedCount h) :
    gapAt d i+32≤nodeAt h j ∨ nodeAt h j+32≤gapAt d i := by
  obtain ⟨lo,hi,_⟩:=gap_range d i bd bi
  obtain ⟨lo',hi',_⟩:=node_range h j bh bj
  by_cases dl : d<h
  · have e:=(cap_geometry ⟨d,by omega⟩).2.2.2.2.2.2.2 ⟨h,bh⟩ dl;exact Or.inl (hi.trans (e.trans lo'))
  by_cases hl : h<d
  · have e:=(cap_geometry ⟨h,bh⟩).2.2.2.2.2.2.2 ⟨d,by omega⟩ hl;exact Or.inr (hi'.trans (e.trans lo))
  have eq : d=h:=by omega
  subst d;unfold gapAt rowAt nodeAt;omega

theorem ChainOutside.read {s t dst} (changed : ChainOutside s t dst) (a n : Nat) (fit : a+n≤MEMORY_BYTES)
    (scratch : a+n≤rowBuf ∨ rowBuf+352≤a) (sep : a+n≤dst ∨ dst+32≤a) (da : dst%8=0) : readBuffer t a n=readBuffer s a n := by
  unfold readBuffer;apply congrArg (BitVec.ofNat _);apply Finset.sum_congr rfl;intro j hj
  have inside:=Finset.mem_range.mp hj
  apply congrArg (fun b : Byte=>b.toNat*2^(8*j))
  change Open.byteAt t (a+j)=Open.byteAt s (a+j)
  have al : rowBuf%8=0:=by decide
  rw [Open.byte_word,Open.byte_word s,changed _ (by omega) (by omega) (by omega) (by omega)]

abbrev Values := Nat→Nat→Late.Digest
structure Cache (s : MachineState) (v : Values) : Prop where
  node : ∀ d<9,∀ j<paddedCount d,readBuffer s (nodeAt d j) 32=v d j
  gap : ∀ d<8,∀ j<groups d,readBuffer s (gapAt d j) 32=0

theorem Cache.same {s t v} (old : Cache s v) (mem : t.mem=s.mem) : Cache t v :=
  ⟨fun d h i b=>(read_buffer_memory_congr t s mem _ _).trans (old.node d h i b),
    fun d h i b=>(read_buffer_memory_congr t s mem _ _).trans (old.gap d h i b)⟩
theorem blank_cache (s : MachineState) (clear : BlankTree s) : Cache s (fun _ _=>0) := by
  have zero (a : Nat) (lo : capBase≤a) (hi : a+32≤saltBuf) (al : a%8=0) : readBuffer s a 32=0 := by
    let u:=writeBits s (W a) (0#256)
    apply (read_digest_congr s u a al ?_).trans (store_read s a _)
    intro j hj;have v:=output_word s a j (0#256) al hj
    apply (clear (a+8*j) (by omega) (by omega) (by omega)).trans
    apply Eq.trans _ v.symm;simp [BitVec.extractLsb']
  constructor
  · intro d h j k;obtain ⟨lo,hi,al⟩:=node_range d j h k
    have g:=cap_geometry ⟨d,h⟩;exact zero _ (g.1.trans lo) (hi.trans g.2.1) al
  · intro d h j k;obtain ⟨lo,hi,al⟩:=gap_range d j h k
    have g:=cap_geometry ⟨d,by omega⟩;exact zero _ (g.1.trans lo) (hi.trans g.2.1) al

def replaceNode (vs : Values) (h i : Nat) (v : Late.Digest) : Values:=fun d j=>if d=h ∧ j=i then v else vs d j
theorem Cache.write {s t vs h i} (old : Cache s vs) (dh : h<9) (di : i<paddedCount h) (digest : Late.Digest)
    (data : readBuffer t (nodeAt h i) 32=digest) (frame : ChainOutside s t (nodeAt h i)) : Cache t (replaceNode vs h i digest) := by
  have al:=(node_range h i dh di).2.2
  constructor
  · intro d bd j bj;unfold replaceNode
    split
    next eq=>obtain ⟨rfl,rfl⟩:=eq;exact data
    next ne=>
      obtain ⟨lo,hi,_⟩:=node_range d j bd bj;have g:=cap_geometry ⟨d,bd⟩
      exact (frame.read _ 32 (hi.trans (g.2.1.trans (by decide))) (Or.inr ((by decide : rowBuf+352≤capBase).trans (g.1.trans lo)))
        (node_apart d h j i bd dh bj di (by tauto)) al).trans (old.node d bd j bj)
  · intro d bd j bj;obtain ⟨lo,hi,_⟩:=gap_range d j bd bj;have g:=cap_geometry ⟨d,by omega⟩
    exact (frame.read _ 32 (hi.trans (g.2.1.trans (by decide))) (Or.inr ((by decide : rowBuf+352≤capBase).trans (g.1.trans lo)))
      (gap_apart d h j i bd dh bj di) al).trans (old.gap d bd j bj)
end CommitGolfCandidate.S5Machine.Check
