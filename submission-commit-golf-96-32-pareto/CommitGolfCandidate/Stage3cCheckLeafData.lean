import CommitGolfCandidate.Stage3cLeafWrites
import CommitGolfCandidate.Stage3cCheckStore
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (Salt Digest)
open Open (W Outside)
def leafBuf:=65536
def rowBuf:=65792
def chainBuf:=66048
def digestBuf:=66304
def marksBuf:=66560
def saltBuf:=131072
def laneOffset (odd : Bool) := if odd then 32 else 0
def saltOffset (odd : Bool) := if odd then 0 else 72
def padOffset (odd : Bool) := if odd then 24 else 64
def leafEffect (H : Compression) (s : MachineState) (odd : Bool) :=
  let u:=compressAt H s leafBuf (leafBuf+64)
  let z:=compressAt H u (leafBuf+64) (rowBuf+laneOffset odd)
  let w:=compressAt H z (leafBuf+160) (rowBuf+laneOffset odd+32)
  compressAt H w rowBuf digestBuf

theorem reply_outside (s : MachineState) (a : Nat) (v : Digest) (space : a+32≤MEMORY_BYTES) (al : a%8=0) :
    Outside s (BinaryMachine.store s a v) a 32 := by
  intro q lim align apart
  apply writeBits_memory_outside
  intro j hj
  rw [←BitVec.ofNat_add,word_address a j al]
  change j<32 at hj
  intro eq;have h:=congrArg BitVec.toNat eq
  change q<2^36 at lim;change a+32≤2^36 at space
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show q<2^64 by omega),Nat.mod_eq_of_lt (show a+8*(j/8)<2^64 by omega)] at h;omega

theorem leaf_frame (H : Compression) (s : MachineState) (odd : Bool) : Outside s (leafEffect H s odd) leafBuf 800 := by
  intro q h al away
  have pass (s : MachineState) (r a : Nat) (lo : leafBuf≤a) (hi : a+32≤leafBuf+800) (aa : a%8=0) :
      Open.wordAt (compressAt H s r a) q=Open.wordAt s q :=
    reply_outside _ _ _ (hi.trans (by decide)) aa q h al (by omega)
  unfold leafEffect
  apply (pass _ _ _ (by decide) (by decide) (by decide)).trans
  apply (pass _ _ _ (by cases odd <;> decide) (by cases odd <;> decide) (by cases odd <;> decide)).trans
  apply (pass _ _ _ (by cases odd <;> decide) (by cases odd <;> decide) (by cases odd <;> decide)).trans
  exact pass _ _ _ (by decide) (by decide) (by decide)

private theorem installed (s : MachineState) (odd : Bool) (a b : Digest) (salt : Salt)
    (pad : readBuffer s (rowBuf+padOffset odd) 8=0) (random : readBuffer s (rowBuf+saltOffset odd) 24=salt) :
    readBuffer (BinaryMachine.store (BinaryMachine.store s (rowBuf+laneOffset odd) a) (rowBuf+laneOffset odd+32) b) rowBuf 96=Late.finalBlock odd salt a b := by
  cases odd <;> simp only [laneOffset,saltOffset,padOffset,Bool.false_eq_true,ite_false,ite_true,Nat.add_zero] at pad random ⊢
  · apply even_row
    · apply (store_away _ _ _ _ _ (by decide) (by decide) (by decide)).trans;exact store_read ..
    · exact store_read _ _ _
    · apply (store_away _ _ _ _ _ (by decide) (by decide) (by decide)).trans;apply (store_away _ _ _ _ _ (by decide) (by decide) (by decide)).trans;exact pad
    · apply (store_away _ _ _ _ _ (by decide) (by decide) (by decide)).trans;apply (store_away _ _ _ _ _ (by decide) (by decide) (by decide)).trans;exact random
  · apply odd_row
    · apply (store_away _ _ _ _ _ (by decide) (by decide) (by decide)).trans;apply (store_away _ _ _ _ _ (by decide) (by decide) (by decide)).trans;exact random
    · apply (store_away _ _ _ _ _ (by decide) (by decide) (by decide)).trans;apply (store_away _ _ _ _ _ (by decide) (by decide) (by decide)).trans;exact pad
    · apply (store_away _ _ _ _ _ (by decide) (by decide) (by decide)).trans;exact store_read ..
    · exact store_read _ _ _

theorem leaf_value (H : Compression) (s : MachineState) (odd : Bool) (value : Entry) (salt : Salt)
    (msg : readBuffer s leafBuf 256=value) (pad : readBuffer s (rowBuf+padOffset odd) 8=0)
    (random : readBuffer s (rowBuf+saltOffset odd) 24=salt) :
    readBuffer (leafEffect H s odd) digestBuf 32=Late.leaf H odd salt value := by
  let first:=H (Late.firstBlock value)
  let u:=BinaryMachine.store s (leafBuf+64) first
  let d0:=H (Late.middleBlock value first)
  let d1:=H (Late.lastBlock value)
  let z:=BinaryMachine.store u (rowBuf+laneOffset odd) d0
  let t:=BinaryMachine.store z (rowBuf+laneOffset odd+32) d1
  obtain ⟨q₀,q₁,q₂⟩:=first_two_inputs s leafBuf value msg H (by decide)
  have p : readBuffer u (rowBuf+padOffset odd) 8=0 :=
    (store_away _ _ _ _ _ (by decide) (by cases odd <;> decide) (Or.inr (by cases odd <;> decide))).trans pad
  have r : readBuffer u (rowBuf+saltOffset odd) 24=salt :=
    (store_away _ _ _ _ _ (by decide) (by cases odd <;> decide) (Or.inr (by cases odd <;> decide))).trans random
  have third : readBuffer z (leafBuf+160) 96=Late.lastBlock value :=
    (store_away _ _ _ _ _ (by cases odd <;> decide) (by decide) (Or.inl (by cases odd <;> decide))).trans q₂
  have four : readBuffer t rowBuf 96=Late.finalBlock odd salt d0 d1:=installed u odd d0 d1 salt p r
  apply (store_read _ digestBuf _).trans
  apply congrArg H
  have step1 : compressAt H s leafBuf (leafBuf+64)=u:=congrArg (BinaryMachine.store s (leafBuf+64)) (congrArg H q₀)
  have step2 : compressAt H u (leafBuf+64) (rowBuf+laneOffset odd)=z:=congrArg (BinaryMachine.store u _) (congrArg H q₁)
  have step3 : compressAt H z (leafBuf+160) (rowBuf+laneOffset odd+32)=t:=congrArg (BinaryMachine.store z _) (congrArg H third)
  change readBuffer (compressAt H (compressAt H (compressAt H s leafBuf (leafBuf+64)) (leafBuf+64) (rowBuf+laneOffset odd)) (leafBuf+160) (rowBuf+laneOffset odd+32)) rowBuf 96=_
  rw [step1,step2,step3];exact four
end CommitGolfCandidate.Chained.BinaryMachine.Check
