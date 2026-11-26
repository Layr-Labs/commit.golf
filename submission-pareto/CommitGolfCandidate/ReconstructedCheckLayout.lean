import CommitGolfCandidate.ReconstructedCheckLowerRound

namespace CommitGolfCandidate.Reconstruction.CheckLayout
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding CheckParentGeometry CheckLowerRound
open TwoPermutationPrototype.RV64
set_option maxRecDepth 14000
set_option maxHeartbeats 1150000
abbrev W:=BitVec.ofNat 64

def fp:=68719475728
def sp:=68719473296
def proofBase:=10334769248
def maskCell:=68719473360
def geo : Geometry := ⟨68719473152,68719473368,68719475416⟩
def lowCell (i : Fin 15):=2097160+8*(10+i.val)
def divCell (i : Fin 15):=262170+(10+i.val)
def reader (c : Nat) (i : Fin 15) : CheckStream.Reader:=⟨proofBase,c/64,lowCell i,maskCell⟩
def residue (c : Nat) : Fin 64:=⟨c%64,by omega⟩

theorem geoPlaced : Placed geo:=by constructor <;> decide

theorem placed (c : Nat) (bound : c≤70000000000) (i : Fin 15) : CheckLowerGeometry.Placed (reader c i) := by
  have hi:=i.isLt
  constructor
  · constructor
    · change 10334769248%8=0;decide
    · change 10334769248+8*(c/64)+40≤2^36;omega
  · change (2097160+8*(10+i.val))%8=0;omega
  · change 68719473360%8=0;decide
  · change 2097160+8*(10+i.val)+8≤2^36;omega
  · change 68719473360+8≤2^36;decide
  · change 2097160+8*(10+i.val)≠68719473360;omega
  · left;change 2097160+8*(10+i.val)+8≤10334769248+8*(c/64);omega
  · right;change 10334769248+8*(c/64)+40≤68719473360;omega

/-- These words are owned by the program's parent subroutine and by its lower-path caller. -/
theorem outside (a : Nat) (bound : a<2^36) (pair : a<geo.pair ∨ geo.pair+64≤a)
    (stack : a<geo.stack ∨ geo.stack+144≤a) (out : a<geo.out ∨ geo.out+32≤a) : Outside geo (W a) := by
  have diff (n len : Nat) (base : Nat) (r : n<len) (high : base+8*len≤2^36) (away : a<base ∨ base+8*len≤a) :
      W a≠W (base+8*n) := by
    intro h;have eq:=congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : a<2^64),Nat.mod_eq_of_lt (by omega : base+8*n<2^64)] at eq;omega
  exact ⟨fun i=>diff i.val 8 geo.pair i.isLt (by decide) pair,fun i=>diff i.val 18 geo.stack i.isLt (by decide) stack,
    fun i=>diff i.val 4 geo.out i.isLt (by decide) out⟩

def StreamMemory (s : MachineState) (bits : Nat) := ∀ i, i<1100000000 →
  s.getMem (W (proofBase+8*i))=W (HonestStream.word bits i)

structure Tables (s : MachineState) : Prop where
  lows : ∀ i : Fin 15, s.getMem (W (lowCell i))=W (CheckMixed.width i)
  bases : ∀ i : Fin 15, s.getMem (wordAddress (divCell i))=W (CheckMixed.base i)
  mask : s.getMem (W maskCell)=0xffffffff
  ro : constants s

theorem source (s : MachineState) (bits c : Nat) (i : Fin 15) (bound : c≤70000000000) (stream : StreamMemory s bits) :
    CheckStream.Source s (reader c i) bits := by
  intro k hk
  have h:=stream (c/64+k) (by omega)
  change s.getMem (W ((proofBase+8*(c/64))+8*k))=W (HonestStream.word bits (c/64+k))
  rw [show proofBase+8*(c/64)+8*k=proofBase+8*(c/64+k) by omega];exact h

def Untouched (s t : MachineState) := ∀ a,a<2^33→Outside geo (wordAddress a)→t.getMem (wordAddress a)=s.getMem (wordAddress a)

theorem readFrame (s t : MachineState) (fr : Untouched s t) (a : Nat) (aligned : a%8=0) (small : a<2^36) (away : Outside geo (W a)) :
    t.getMem (W a)=s.getMem (W a) := by
  have q : wordAddress (a/8)=W a := by unfold wordAddress;congr 1;omega
  rw [←q] at away ⊢;exact fr _ (by omega) away

theorem stream_frame (s t : MachineState) (bits : Nat) (fr : Untouched s t) (ins : StreamMemory s bits) : StreamMemory t bits := by
  intro i small;apply Eq.trans _ (ins i small)
  apply readFrame s t fr _ (by unfold proofBase;omega) (by unfold proofBase;omega)
  apply outside <;> simp only [proofBase,geo] <;> omega

theorem table_frame (s t : MachineState) (fr : Untouched s t) (saved : Tables s) : Tables t := by
  constructor
  · intro i;apply Eq.trans _ (saved.lows i)
    have hi:=i.isLt;apply readFrame s t fr _ (by unfold lowCell;omega) (by unfold lowCell;omega)
    apply outside <;> simp only [lowCell,geo] <;> omega
  · intro i;apply Eq.trans _ (saved.bases i)
    have hi:=i.isLt;apply fr _ (by unfold divCell;omega)
    change Outside geo (W (8*(divCell i)));apply outside <;> simp only [divCell,geo] <;> omega
  · apply Eq.trans _ saved.mask
    apply readFrame s t fr _ (by decide) (by decide);apply outside <;> decide
  · intro a v al known
    apply Eq.trans _ (saved.ro a v al known)
    have lo : 2097560≤a ∧ a<2098152 :=by unfold CheckParentRun.ro at known;split_ifs at known <;> first | contradiction | omega
    change t.getMem (W a)=s.getMem (W a);apply readFrame s t fr _ al (by omega)
    apply outside <;> (try simp only [geo]) <;> omega

end CommitGolfCandidate.Reconstruction.CheckLayout
