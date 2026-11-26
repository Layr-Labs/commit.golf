import CommitGolfCandidate.S4RecordData

set_option Elab.async false
namespace CommitGolfCandidate.R4b
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open CommitGolfCandidate.S4
open S4.Open (initial tdBase)
open S4.Machine (W byte proofBase indexBase)

def tableBase : Nat := 68719460304
def slotWord (k : Nat) : Nat :=
  if k<2048 then
    let g:=k/1024
    let j:=k%8
    if j=7 then 0 else Late.rowAddress (7*g+j+1) ((k%1024/8)/2^(j+1))+32*(1-((k%1024/8)/2^j)%2)
  else ([32,64,0,64,0,32] : List Nat)[k-2048]?.getD 0

private def packedByte (n : Nat) : Byte :=
  if h:n<16432 then Artifact.openingData.get 8 ⟨n,h⟩ else 0
private def packedWord (k : Nat) : Word := BitVec.ofNat 64 (∑ j ∈ Finset.range 8,
    (packedByte (8*k+j)).toNat*2^(8*j))
private theorem byteLookup {m : Nat} (a : ArtifactEncoding.Packed m) (k : Nat) (h : k<m) :
    (ArtifactEncoding.decode 8 a)[k]?=some (a.get 8 ⟨k,h⟩) := by
  simp only [ArtifactEncoding.decode,List.getElem?_ofFn,dif_pos h]
attribute [local irreducible] ArtifactEncoding.decode
private theorem dataByte (td : Late.Trapdoor) (ps : Positions) (k : Nat) (hk : k<16432) :
    byte (initial td ps) (tableBase+k)=packedByte k := by
  rw [show byte (initial td ps) (tableBase+k)=inputByte Late.submission .opening (td,ps) (tableBase+k) from
    initial_input_byte _ _ _ _ (by unfold tableBase;omega)]
  let a:=tableBase+k
  let f:=fixedBuffer tdBase td
  let p:=positionsBuffer indexBase ps
  have hlen : ps.card≤16777216 := by change ps.card≤LENGTH;simpa using Finset.card_le_univ ps
  have noF : ¬(f.address≤a ∧ a<f.address+f.length):=by change ¬(4294971424≤a ∧ a<4294971424+3355443200);dsimp [a,tableBase];omega
  have noP : ¬(p.address≤a ∧ a<p.address+p.length):=by
    change ¬(7650414624≤a ∧ a<7650414624+8*(ps.sort (·≤·)).length)
    rw [Finset.length_sort];dsimp [a,tableBase];omega
  have absent : [f,p].find? (fun b=>decide (b.address≤a ∧ a<b.address+b.length))=none:=by
    simp [List.find?_cons,noF,noP]
  unfold inputByte
  change (match [f,p].find? (fun b=>decide (b.address≤a ∧ a<b.address+b.length)) with
    | some buf=>buf.byteAt (a-buf.address)
    | none=>if dataBase (Late.submission.image .opening)≤a then
        (Late.submission.image .opening).data[a-dataBase (Late.submission.image .opening)]?.getD 0 else 0)=_
  rw [absent,Late.openingDataBase,if_pos (by dsimp [a,tableBase];omega)]
  change ((ArtifactEncoding.decode 8 Artifact.openingData)[tableBase+k-tableBase]?).getD 0=_
  rw [Nat.add_sub_cancel_left]
  rw [byteLookup _ _ hk];simp only [packedByte,dif_pos hk,Option.getD_some]

def TableMem (s : MachineState) := ∀ k,k<2054 → s.getMem (W (tableBase+8*k))=W (slotWord k)

set_option maxRecDepth 6000
set_option maxHeartbeats 4000000
private theorem block0 : ∀ i : Fin 128,packedWord (0+i.val)=W (slotWord (0+i.val)) := by decide +kernel
private theorem block1 : ∀ i : Fin 128,packedWord (128+i.val)=W (slotWord (128+i.val)) := by decide +kernel
private theorem block2 : ∀ i : Fin 128,packedWord (256+i.val)=W (slotWord (256+i.val)) := by decide +kernel
private theorem block3 : ∀ i : Fin 128,packedWord (384+i.val)=W (slotWord (384+i.val)) := by decide +kernel
private theorem block4 : ∀ i : Fin 128,packedWord (512+i.val)=W (slotWord (512+i.val)) := by decide +kernel
private theorem block5 : ∀ i : Fin 128,packedWord (640+i.val)=W (slotWord (640+i.val)) := by decide +kernel
private theorem block6 : ∀ i : Fin 128,packedWord (768+i.val)=W (slotWord (768+i.val)) := by decide +kernel
private theorem block7 : ∀ i : Fin 128,packedWord (896+i.val)=W (slotWord (896+i.val)) := by decide +kernel
private theorem block8 : ∀ i : Fin 128,packedWord (1024+i.val)=W (slotWord (1024+i.val)) := by decide +kernel
private theorem block9 : ∀ i : Fin 128,packedWord (1152+i.val)=W (slotWord (1152+i.val)) := by decide +kernel
private theorem block10 : ∀ i : Fin 128,packedWord (1280+i.val)=W (slotWord (1280+i.val)) := by decide +kernel
private theorem block11 : ∀ i : Fin 128,packedWord (1408+i.val)=W (slotWord (1408+i.val)) := by decide +kernel
private theorem block12 : ∀ i : Fin 128,packedWord (1536+i.val)=W (slotWord (1536+i.val)) := by decide +kernel
private theorem block13 : ∀ i : Fin 128,packedWord (1664+i.val)=W (slotWord (1664+i.val)) := by decide +kernel
private theorem block14 : ∀ i : Fin 128,packedWord (1792+i.val)=W (slotWord (1792+i.val)) := by decide +kernel
private theorem block15 : ∀ i : Fin 128,packedWord (1920+i.val)=W (slotWord (1920+i.val)) := by decide +kernel
private theorem block16 : ∀ i : Fin 6,packedWord (2048+i.val)=W (slotWord (2048+i.val)) := by decide +kernel
private theorem wordValue (k : Nat) (h : k<2054) : packedWord k=W (slotWord k) := by
  by_cases b0 : k<128
  · simpa only [show 0+(k-0)=k by omega] using block0 ⟨k-0,by omega⟩
  by_cases b1 : k<256
  · simpa only [show 128+(k-128)=k by omega] using block1 ⟨k-128,by omega⟩
  by_cases b2 : k<384
  · simpa only [show 256+(k-256)=k by omega] using block2 ⟨k-256,by omega⟩
  by_cases b3 : k<512
  · simpa only [show 384+(k-384)=k by omega] using block3 ⟨k-384,by omega⟩
  by_cases b4 : k<640
  · simpa only [show 512+(k-512)=k by omega] using block4 ⟨k-512,by omega⟩
  by_cases b5 : k<768
  · simpa only [show 640+(k-640)=k by omega] using block5 ⟨k-640,by omega⟩
  by_cases b6 : k<896
  · simpa only [show 768+(k-768)=k by omega] using block6 ⟨k-768,by omega⟩
  by_cases b7 : k<1024
  · simpa only [show 896+(k-896)=k by omega] using block7 ⟨k-896,by omega⟩
  by_cases b8 : k<1152
  · simpa only [show 1024+(k-1024)=k by omega] using block8 ⟨k-1024,by omega⟩
  by_cases b9 : k<1280
  · simpa only [show 1152+(k-1152)=k by omega] using block9 ⟨k-1152,by omega⟩
  by_cases b10 : k<1408
  · simpa only [show 1280+(k-1280)=k by omega] using block10 ⟨k-1280,by omega⟩
  by_cases b11 : k<1536
  · simpa only [show 1408+(k-1408)=k by omega] using block11 ⟨k-1408,by omega⟩
  by_cases b12 : k<1664
  · simpa only [show 1536+(k-1536)=k by omega] using block12 ⟨k-1536,by omega⟩
  by_cases b13 : k<1792
  · simpa only [show 1664+(k-1664)=k by omega] using block13 ⟨k-1664,by omega⟩
  by_cases b14 : k<1920
  · simpa only [show 1792+(k-1792)=k by omega] using block14 ⟨k-1792,by omega⟩
  by_cases b15 : k<2048
  · simpa only [show 1920+(k-1920)=k by omega] using block15 ⟨k-1920,by omega⟩
  simpa only [show 2048+(k-2048)=k by omega] using block16 ⟨k-2048,by omega⟩

theorem initialTable (td : Late.Trapdoor) (ps : Positions) : TableMem (initial td ps) := by
  intro k h
  change Machine.wordAt (initial td ps) (tableBase+8*k)=_
  rw [←wordValue k h,S4.Open.wordExact _ _ (by unfold tableBase;omega)]
  unfold readBuffer packedWord
  apply congrArg (BitVec.ofNat 64);apply Finset.sum_congr rfl;intro j hj
  have bound:=Finset.mem_range.mp hj
  have eqv:=dataByte td ps (8*k+j) (by omega)
  rw [←Nat.add_assoc] at eqv
  exact congrArg (fun x : Byte=>x.toNat*2^(8*j)) eqv

theorem tableOfBytes {s t : MachineState} (h : TableMem s)
    (eqv : ∀ a,tableBase≤a → a<tableBase+16432 → byte t a=byte s a) : TableMem t := by
  intro k hk
  have al : (tableBase+8*k)%8=0:=by unfold tableBase;omega
  change Machine.wordAt t (tableBase+8*k)=_
  have e : Machine.wordAt s (tableBase+8*k)=_:=h k hk
  rw [S4.Open.wordExact _ _ al,←e,S4.Open.wordExact _ _ al]
  unfold readBuffer;apply congrArg (BitVec.ofNat 64);apply Finset.sum_congr rfl;intro j hj
  have:=Finset.mem_range.mp hj
  exact congrArg (fun x : Byte=>x.toNat*2^(8*j)) (eqv _ (by omega) (by omega))
end CommitGolfCandidate.R4b
