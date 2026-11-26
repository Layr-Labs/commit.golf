import CommitGolfCandidate.ReconstructedCheckRecordWrite
import CommitGolfCandidate.ReconstructedCheckRecordImmutable
import CommitGolfCandidate.ReconstructedCheckSlotCompare
import CommitGolfCandidate.ReconstructedHonestFlagState

namespace CommitGolfCandidate.Reconstruction.CheckRecordSlots
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding CheckRecordAccess CheckParentWords CheckWalkValues
open TwoPermutationPrototype TwoPermutationPrototype.RV64
set_option maxRecDepth 15000
set_option maxHeartbeats 1300000
abbrev W:=BitVec.ofNat 64

abbrev Slots:=Nat→Option Binding.Digest

def present (x : Option Binding.Digest) : Byte := if x.isSome then 1 else 0
def replace (a : Slots) (k : Nat) (v : Binding.Digest) : Slots:=fun j=>if j=k then some v else a j

structure Holds (s : MachineState) (a : Slots) : Prop where
  flag : ∀ k,k<1024→s.getByte (CheckRecordAccess.flag k)=present (a k)
  words : ∀ k,k<1024→∀ v,a k=some v→∀ j : Fin 4,s.getMem (wordAddress (capWord k j))=digWord v j

theorem empty (s : MachineState) (flags : ∀ k<1024,s.getByte (CheckRecordAccess.flag k)=0) : Holds s (fun _=>none) :=
  ⟨flags,fun _ _ _ eq=>by cases eq⟩

theorem hashRange (idx : Index) : 512≤heap idx 9 ∧ heap idx 9<1024 := by
  have h : idx.val<2^24:=idx.isLt;change 512≤(2^24+idx.val)/32768 ∧ (2^24+idx.val)/32768<1024;omega

theorem physical (s : MachineState) (k : Nat) (x : Binding.Digest)
    (words : ∀ j : Fin 4,s.getMem (wordAddress (capWord k j))=digWord x j) : CommitParents.cell s (4194304+32*k)=x := by
  have w (j : Nat) (lim : j<4) : s.getMem (W ((4194304+32*k)+8*j))=digWord x j:=by
    rw [show (4194304+32*k)+8*j=8*(capWord k j) by unfold capWord;omega]
    exact words ⟨j,lim⟩
  have read:=CheckParentCall.read_words_eq s (4194304+32*k) 4 (pack x) (by omega) w
  change (readBuffer s _ 32).cast _=pack x at read
  rw [BitVec.cast_eq] at read;exact (congrArg unpack read).trans (unpack_pack x)

theorem sameWord {s t : MachineState} {a : Slots} (h : Holds s a) (m : Mem s t) : Holds t a :=
  ⟨fun k hk=>(CheckRecordAccess.bytes m _ (by omega)).trans (h.flag k hk),
    fun k hk v hv j=>(m _ (by unfold capWord;have:=j.isLt;omega)).trans (h.words k hk v hv j)⟩

theorem sameFrame {s t : MachineState} {a : Slots} (h : Holds s a) (m : CheckRecordFrame.Frame s t) : Holds t a := by
  constructor
  · intro k small
    apply Eq.trans _ (h.flag k small)
    change extractByte (t.getMem (alignToDword (W (4259840+k)))) _=extractByte (s.getMem (alignToDword (W (4259840+k)))) _
    rw [OpeningCursor.aligned];apply congrArg (fun x=>extractByte x _);apply m <;> first | omega | unfold CheckRecordFrame.Safe;omega
  · intro k hk v hv j;apply Eq.trans _ (h.words k hk v hv j);change t.getMem (W (8*(capWord k j)))=_
    have b:=j.isLt;apply m <;> first | unfold CheckRecordFrame.Safe capWord;omega | unfold capWord;omega

theorem cellAgree (s : MachineState) (k : Nat) (x : Binding.Digest) (words : CheckPairPhysical.child s CheckPair.current x)
    (old : Binding.Digest) (slot : ∀ j : Fin 4,s.getMem (wordAddress (capWord k j))=digWord old j) :
    (∀ j : Fin 4,CheckSlotCompare.EqualAt s k j) ↔ old=x := by
  constructor
  · intro h
    have a:=physical s k old slot
    have b:=physical s k x (fun j=>(h j).symm.trans (words j))
    exact a.symm.trans b
  · rintro rfl;intro j;exact (words j).trans (slot j).symm

theorem capStart {s : MachineState} {a : Slots} (h : Holds s a) (b : ∀ k<512,a k=none) :
    HonestFlagState.Initial (fun j=>(a (512+j)).isSome) s ∧
    ∀ k<512,∀ v,a (512+k)=some v→CommitParents.cell s (4194304+32*(512+k))=v := by
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro k hk;change s.getByte (CheckRecordAccess.flag k)=0;rw [h.flag k (by omega),b k hk];rfl
  · intro k hk;change s.getByte (CheckRecordAccess.flag (512+k))=_;rw [h.flag _ (by omega)]
    change present (a (512+k))=HonestFlagState.code (a (512+k)).isSome
    cases a (512+k) <;> rfl
  · intro k hk v hv;exact physical s _ v (h.words _ (by omega) v hv)

end CommitGolfCandidate.Reconstruction.CheckRecordSlots
