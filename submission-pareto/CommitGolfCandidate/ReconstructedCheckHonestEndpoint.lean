import CommitGolfCandidate.ReconstructedCheckCapHonest
import CommitGolfCandidate.ReconstructedCheckTailPadding

namespace CommitGolfCandidate.Reconstruction.CheckHonestEndpoint
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding CheckCapLevel
open TwoPermutationPrototype TwoPermutationPrototype.RV64
abbrev W:=BitVec.ofNat 64
set_option maxRecDepth 12500
set_option maxHeartbeats 950000

theorem padding (fs : List Wire.Field) : CheckTailPadding.Padded (Wire.bits fs) (Wire.pack fs) := by
  right
  let c:=Wire.bits fs
  let a:=Wire.pack fs
  change W (HonestStream.word a (c/64)) >>> (c%64)=(0:Word)
  have split : 64*(c/64)+c%64=c:=Nat.div_add_mod c 64
  have zero := Wire.zero_padding fs
  change a >>> c=0 at zero
  have le : (HonestStream.word a (c/64))/2^(c%64) ≤ (a >>> (64*(c/64)))/2^(c%64):=
    Nat.div_le_div_right (Nat.mod_le ..)
  rw [Nat.shiftRight_eq_div_pow] at zero
  rw [Nat.shiftRight_eq_div_pow,Nat.div_div_eq_div_mul,←Nat.pow_add,split,zero] at le
  apply BitVec.eq_of_toNat_eq
  have bounded : HonestStream.word a (c/64)<2^64:=Nat.mod_lt _ (by decide)
  rw [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.mod_eq_of_lt bounded,Nat.shiftRight_eq_div_pow]
  exact Nat.le_zero.mp le

theorem saved {s t : MachineState} (fr : Frame s t) (q : Nat) (bound : q<2^33) (ok : clear q) :
    t.getMem (W (8*q))=s.getMem (W (8*q)) := fr q bound ok

theorem root_word (t : MachineState) (x : Binding.Digest) (value : node t 1=x) (j : Fin 4) :
    t.getMem (W (4194336+8*j.val))=CheckParentWords.digWord x j := by
  have raw : CheckCapLevel.view (memoryView t) 1=x := (CheckCapPhysical.physical t 1).symm.trans value
  have eq:=congrArg (fun y=>CheckParentWords.digWord y j) raw
  change CheckParentWords.digWord (CheckEdge.digest _ _ _ _) j=_ at eq
  rw [CheckLowerInput.digWords] at eq
  fin_cases j <;> exact eq

structure TailData (t : MachineState) (input : CheckInput) : Prop where
  root : ∀ j : Fin 4,t.getMem (W (4294971392+8*j.val))=input.commitment.extractLsb' (64*j.val) 64
  length : t.getMem (W (CheckLayout.fp-2424))=W input.proof.length
  ret : t.getMem (W (CheckLayout.fp-8))=CommitBlocks.addr 20
  stream : CheckLayout.StreamMemory t (Wire.unpackBytes input.proof)

theorem transfer {s t : MachineState} {input : CheckInput} (fr : Frame s t) (kept : CheckRecordABI.Persistent s input) :
    TailData t input := by
  constructor
  · intro j;apply Eq.trans _ (kept.commitment j)
    have eq : 4294971392+8*j.val=8*(536871424+j.val):=by omega
    rw [eq];apply saved fr
    · have h:=j.isLt;omega
    · unfold clear CheckCapLowMemory.Outside CheckCapScanData.cap;have h:=j.isLt;omega
  · exact (saved fr 8589934163 (by decide) (by unfold clear CheckCapLowMemory.Outside;decide)).trans kept.length
  · exact (saved fr 8589934465 (by decide) (by unfold clear CheckCapLowMemory.Outside;decide)).trans kept.returnPC
  · intro i hi;apply Eq.trans _ (kept.stream i hi)
    have eq : CheckLayout.proofBase+8*i=8*(1291846156+i):=by unfold CheckLayout.proofBase;omega
    rw [eq];apply saved fr
    · omega
    · unfold clear CheckCapLowMemory.Outside CheckCapScanData.cap;omega

theorem comparisons {t : MachineState} {input : CheckInput} (info : TailData t input) (x : Binding.Digest)
    (heap : node t 1=x) (commitment : input.commitment=Binding.pack x) :
    ∀ j : Fin 4, CheckRoot.EqualAt t j := by
  intro j;exact (root_word t x heap j).trans ((info.root j).trans (congrArg (fun v : Commitment=>v.extractLsb' (64*j.val) 64) commitment)).symm

end CommitGolfCandidate.Reconstruction.CheckHonestEndpoint

