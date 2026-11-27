import CommitGolfCandidate.R1bCarrier
import CommitGolfCandidate.TwoPermutationPackedHonestInput

namespace TwoPermutationPrototype.PackedHonest
open CommitGolf CommitGolfCandidate Sampling
open CommitGolfCandidate.R1b
open PackedCertificate (honestCheckInput)

private theorem zeroHighBit (z : BitVec 238) (i : Nat) (small : i < 256) (high : 238 ≤ i) :
    (0#18 ++ z)[i]'small = false := by
  exact (BitVec.getElem_append (x:=0#18) (y:=z) (i:=i) small).trans
    (by rw [dif_neg (Nat.not_lt.mpr high)];exact BitVec.getElem_zero _)

private theorem narrowByte (o : Oracle) (m : Message) (s : CompleteSaltTape) (n : Nat) (hn : n < 524288) :
    Carry.lower ((honestHeap o m s n).extractLsb' 232 8) = (honestHeap o m s n).extractLsb' 232 8 := by
  by_cases z : n=0
  · subst n
    simp [honestHeap,Hybrid.heap,Carry.lower,LENGTH]
  · unfold honestHeap
    rw [Hybrid.heap_parent _ _ _ ⟨by omega, by change n<16777216; omega⟩, Hybrid.normalize,
      if_pos (show n<LENGTH/2 by change n<8388608;omega), if_pos hn]
    apply BitVec.eq_of_getLsbD_eq
    intro bit hb
    interval_cases bit <;> simp (config:={decide:=true}) [Carry.lower,Hybrid.pad238,BitVec.getLsbD_extractLsb',BitVec.getLsbD_append]
    · exact zeroHighBit _ 238 (by decide) (by decide)
    · exact zeroHighBit _ 239 (by decide) (by decide)

theorem batchCanonical (o : Oracle) (m : Message) (ps : Positions) (s : CompleteSaltTape)
    (batch : ps.card=128) : Carry.Canonical (Carry.read (honestCheckInput o m ps s).proof) := by
  let xs := (honestCheckInput o m ps s).proof
  have len : xs.length = 64000 + 30*(Opening.openingNodes ps).length := by
    rw [show xs.length = _ from honest_proof_length o m ps s]
    simp only [PackedOpening.proofLength,PackedOpening.recordBytes,batch]
  have footer (j : Nat) :
      Carry.lower (Carry.read xs (64000+30*j+29)) = Carry.read xs (64000+30*j+29) := by
    by_cases inRange : j < (Opening.openingNodes ps).length
    · have atByte := honest_frontier_byte o m ps s j 29 inRange (by decide)
      rw [batch] at atByte
      change xs[64000+30*j+29]? = _ at atByte
      simp only [Carry.read,atByte,proofDigestBytes,ite_true,List.getElem?_take,
        show 29<30 by decide,digestBytes,List.getElem?_ofFn,show 29<32 by decide,dite_true,Option.getD_some]
      apply narrowByte
      have small (n : Nat) (mem : n∈Opening.openingNodes ps) : n<524288 := by
        unfold Opening.openingNodes at mem
        rw [if_neg (by omega)] at mem
        exact Nat.lt_trans (Opening.cap_frontier_nodes_small _ 1 8 Opening.cap_span_root n mem) (by decide)
      exact small _ (List.getElem_mem inRange)
    · have out : xs.length≤64000+30*j+29 := by omega
      simp [Carry.read,List.getElem?_eq_none out,Carry.lower]
  constructor
  · intro c hc
    by_cases rec : c<1280
    · let j := c%10
      let r := c/10
      have hr : r<ps.card := by dsimp [r];omega
      have hj : j<10 := Nat.mod_lt _ (by decide)
      let i : Index := (honestIndex ps r hr).val
      have whereByte : Carry.carrier c=500*r+(80+30*(4+j)+29) := by
        simp only [Carry.carrier,if_pos rec,r,j];omega
      have raw := honest_record_byte o m ps s r (80+30*(4+j)+29) hr (by omega)
      rw [later_sibling_byte _ _ _ (4+j) 29 (by omega) (by decide)] at raw
      change xs[500*r+(80+30*(4+j)+29)]?=some _ at raw
      change Carry.lower (Carry.read xs _) = Carry.read xs _
      rw [whereByte,Carry.read,raw]
      apply narrowByte
      apply Nat.xor_lt_two_pow (n := 19) _ (by decide)
      change (16777216+i.val)/2^(4+j+2)<524288
      have idx : i.val <16777216 := i.isLt
      have div : 64≤2^(4+j+2) := Nat.pow_le_pow_right (by decide : 0<2) (by omega : 6≤4+j+2)
      exact (Nat.div_le_div_left div (by decide)).trans_lt (by omega)
    · rw [Carry.carrier,if_neg rec,show 64029+30*(c-1280)=64000+30*(c-1280)+29 by omega]
      exact footer _
  · intro k hk special
    have atByte : 67488+k=64000+30*((3488+k)/30)+29 := by omega
    rw [atByte]
    exact footer _

theorem batchDecoderHonest (o : Oracle) (m : Message) (ps : Positions) (s : CompleteSaltTape)
    (batch : ps.card=128) :
    let xs := (honestCheckInput o m ps s).proof
    Carry.batchDecode (Carry.batchEncode xs)=xs := by
  apply Carry.canonical_roundtrip _ _ (Opening.opening_nodes_bound ps) _ (batchCanonical o m ps s batch)
  rw [honest_proof_length,PackedOpening.proofLength,PackedOpening.recordBytes,batch]

theorem wideWireInput (o : Oracle) (m : Message) (ps : Positions) (s : CompleteSaltTape) :
    let x:=PackedCertificate.wireCheckInput o m ps s
    {x with proof:=Hybrid.wideProof ps x.proof}=honestCheckInput o m ps s := by
  unfold PackedCertificate.wireCheckInput Hybrid.wideProof Hybrid.wireProof
  by_cases batch : ps.card=BATCH
  · simp only [if_pos batch,batchDecoderHonest o m ps s batch]
  · simp only [if_neg batch]

end TwoPermutationPrototype.PackedHonest

namespace TwoPermutationPrototype.PackedHonest
open CommitGolf CommitGolfCandidate R1b Sampling

theorem tagHonest (o : Oracle) (m : Message) (ps : Positions) (s : CompleteSaltTape) (batch : ps.card=BATCH)
    (len : (PackedCertificate.wireCheckInput o m ps s).proof.length=67489) :
    let wire:=(PackedCertificate.wireCheckInput o m ps s).proof
    117≤(Carry.read wire 67488).toNat ∧ (Carry.read wire 67488).toNat≤128 := by
  let xs:=(PackedCertificate.honestCheckInput o m ps s).proof
  let f:=(Opening.openingNodes ps).length
  have size : xs.length=64000+30*f := by
    rw [show xs.length=_ from honest_proof_length o m ps s];simp [PackedOpening.proofLength,PackedOpening.recordBytes,batch,BATCH,f]
  have max : f≤128:=Opening.opening_nodes_bound ps
  have eq : (PackedCertificate.wireCheckInput o m ps s).proof=Carry.batchEncode xs := by simp [PackedCertificate.wireCheckInput,Hybrid.wireProof,batch,xs]
  rw [eq] at len ⊢
  unfold Carry.batchEncode at len ⊢
  split at len
  · omega
  · rename_i long
    rw [if_neg long]
    have tag : (xs.length-64000)/30=f := by omega
    simp [Carry.read,List.getElem?_append,Carry.packed_length,tag,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show f<256 by omega)] <;> omega

end TwoPermutationPrototype.PackedHonest
