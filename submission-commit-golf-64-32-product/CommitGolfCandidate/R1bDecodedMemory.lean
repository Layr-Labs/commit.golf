import CommitGolfCandidate.TwoPermutationCollectTable
import CommitGolfCandidate.R1bCodecRun
import CommitGolfCandidate.TwoPermutationPackedInputFrame
import CommitGolfCandidate.TwoPermutationPackedTrustedInput
import CommitGolfCandidate.R1bWire

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 RV64
open CommitGolfCandidate.R1b
open Machine (W byte proofBase)
open TwoPermutationPrototype.Checker (RecordInputFrame)

def wideInput (x : CheckInput) : CheckInput := {x with proof:=Hybrid.wideProof x.positions x.proof}
def initial (x : CheckInput) := Assembly.submission.initialState .check x

def ByteImage (s : MachineState) (x : CheckInput) : Prop :=
  ∀ a, a<2^64 → byte s a=byte (initial x) a

private theorem wordOf (s : MachineState) (a : Nat) (align : a%8=0) :
    readBuffer s a 8=s.getMem (W a) := by
  have lo:=read_buffer_slice s a 32 0 8 (by decide)
  have w:=read_digest_word s a 0 align (by decide)
  simpa only [Nat.mul_zero,Nat.add_zero] using lo.symm.trans w

theorem ByteImage.word {s : MachineState} {x : CheckInput} (image : ByteImage s x) (w : Nat) (bound : w<2^33) :
    memoryView s w=memoryView (initial x) w := by
  change s.getMem (W (8*w))=(initial x).getMem (W (8*w))
  rw [←wordOf s (8*w) (by omega),←wordOf (initial x) (8*w) (by omega)]
  unfold readBuffer;congr 1;apply Finset.sum_congr rfl
  intro j hj;have := Finset.mem_range.mp hj
  exact congrArg (fun v : Byte=>v.toNat*2^(8*j)) (image (8*w+j) (by omega))

private theorem outside (x : CheckInput) (xs : Proof) (a : Nat) (bound : a<2^64)
    (h : (a<proofBase ∨ proofBase+x.proof.length≤a) ∧ (a<proofBase ∨ proofBase+xs.length≤a)) :
    byte (initial x) a=byte (initial {x with proof:=xs}) a := by
  apply (initial_input_byte _ _ _ _ bound).trans
  apply Eq.trans _ (initial_input_byte _ _ _ _ bound).symm
  let head:=[fixedBuffer 4294971392 x.commitment,positionsBuffer 8187289632 x.positions,valuesBuffer 8321507424 x.positions x.values]
  let pf (bs : Proof) : InputBuffer:=⟨proofBase,bs.length,fun j=>Carry.read bs j⟩
  let pred (buf : InputBuffer):=decide (buf.address≤a ∧ a<buf.address+buf.length)
  have no (bs : Proof) (h : a<proofBase ∨ proofBase+bs.length≤a) :
      (head++[pf bs]).find? pred=head.find? pred:=by
    have bad : pred (pf bs)=false:=decide_eq_false (by change ¬(proofBase≤a ∧ a<proofBase+bs.length);omega)
    rw [List.find?_append];cases hit : head.find? pred <;> simp [bad]
  unfold inputByte
  change (match (head++[pf x.proof]).find? pred with | some b=>b.byteAt (a-b.address) | none=>_)=
    (match (head++[pf xs]).find? pred with | some b=>b.byteAt (a-b.address) | none=>_)
  rw [no _ h.1,no _ h.2]

attribute [local irreducible] Carry.wide Carry.packed
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

private theorem proofByte (x : CheckInput) (j : Nat) (room : x.proof.length≤Assembly.submission.sizes.proof)
    (inside : j<x.proof.length) : byte (initial x) (proofBase+j)=Carry.read x.proof j := by
  have h:=TwoPermutationPrototype.Checker.check_input_proof_byte x room j inside
  exact h.trans (by simp only [Carry.read,List.getElem?_eq_getElem inside,Option.getD_some])

private theorem restoredByte (x : CheckInput) (s t : MachineState) (prev : ByteImage s x)
    (len : x.proof.length=67489) (run : Codec.Mem true s t 352 1396) (j : Nat) (small : j<67840) :
    byte t (proofBase+j)=Carry.read (Carry.wide x.proof) j := by
  have fits : x.proof.length≤Assembly.submission.sizes.proof := by rw [len];decide
  have old (i : Nat) (hi : i<67488) : Codec.original s i=Carry.read x.proof i := by
    have ix : i<x.proof.length := by rw [len];omega
    exact (prev (proofBase+i) (by unfold proofBase;omega)).trans (proofByte x i fits ix)
  calc
    byte t (proofBase+j) = Carry.state true (Codec.original s) 352 1396 j := run.atByte j small
    _ = Carry.wideAt (Codec.original s) j := Carry.decoded (Codec.original s) j small
    _ = Carry.wideAt (Carry.read x.proof) j := Codec.decoded_agrees _ _ old j small
    _ = Carry.read (Carry.wide x.proof) j := (Carry.wide_byte x.proof j small).symm

private theorem decodedOutside (x : CheckInput) (len : x.proof.length=67489) (a : Nat) (bound : a<2^64)
    (notInside : ¬(proofBase≤a ∧ a<proofBase+67840)) :
    byte (initial x) a=byte (initial {x with proof:=Carry.wide x.proof}) a := by
  apply outside x (Carry.wide x.proof) a bound
  rw [len,Carry.wide_length];omega

theorem decodedImage (x : CheckInput) (s t : MachineState) (before : ByteImage s x) (len : x.proof.length=67489)
    (run : Codec.Mem true s t 352 1396) : ByteImage t {x with proof:=Carry.wide x.proof} := by
  let y:CheckInput:={x with proof:=Carry.wide x.proof}
  have size : y.proof.length=67840 := Carry.wide_length x.proof
  have fits : y.proof.length≤Assembly.submission.sizes.proof := by rw [size];decide
  intro a bound
  by_cases region : proofBase≤a ∧ a<proofBase+67840
  · let j:=a-proofBase
    have small : j<67840 := by dsimp only [j];omega
    have inside : j<y.proof.length := size.symm ▸ small
    have hit:= (restoredByte x s t before len run j small).trans (proofByte y j fits inside).symm
    rw [show proofBase+j=a from Nat.add_sub_of_le region.1] at hit
    exact hit
  · exact ((run a bound).trans (if_neg region)).trans ((before a bound).trans (decodedOutside x len a bound region))

structure DecoderFrame (s : MachineState) (x : CheckInput) : Prop where
  input : InputFrame x 0 s
  marks : ∀ n<512, s.getMem (wordAddress (512+n))=0

theorem decodedFrame (x : CheckInput) (s : MachineState) (batch : x.positions.card=BATCH)
    (len : x.proof.length=67489) (mem : ByteImage s {x with proof:=Carry.wide x.proof}) : DecoderFrame s (wideInput x) := by
  let xs:=Carry.wide x.proof
  let k:=64000+30*(Carry.read x.proof 67488).toNat
  have prefixEq : (wideInput x).proof=xs.take k := by simp [wideInput,Hybrid.wideProof,Carry.batchDecode,batch,len,xs,k]
  have recon : (wideInput x).proof++xs.drop k=xs := by rw [prefixEq,List.take_append_drop]
  constructor
  · refine ⟨xs.drop k,?_,?_⟩
    · rw [←List.length_append,recon,show xs.length=67840 from Carry.wide_length x.proof];decide
    · intro w hw _
      have equal : {(wideInput x) with proof:=(wideInput x).proof++xs.drop k}={x with proof:=xs} := by rw [recon] <;> rfl
      rw [equal];exact mem.word w hw
  · intro n hn
    have same:=mem.word (512+n) (by omega)
    exact same.trans (TwoPermutationPrototype.Checker.check_mark_zero {x with proof:=xs} n hn)

end TwoPermutationPrototype.Packed.Checker
