import CommitGolfCandidate.ReconstructedCheckCapSlots
import CommitGolfCandidate.ReconstructedCapScanMemory
import CommitGolfCandidate.ReconstructedHonestSizeRows

namespace CommitGolfCandidate.Reconstruction.CheckCapScanData
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype TwoPermutationPrototype.RV64
open HonestFlagState (code atByte)
abbrev W := BitVec.ofNat 64
abbrev fp : Nat := 68719475728
abbrev scratch : Nat := fp-2360
abbrev active : Nat := 4259840
abbrev cap : Nat := 4194304
def flag (k : Nat) := W (active+k)
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

def scanned (s : MachineState) (dst : Word) (p k : Nat) (l r : Bool) :=
  let m:=CapScanMemory.marked s dst (l||r)
  if l=r then m else m.setWord32 (CheckCapSlots.address scratch p) (BitVec.ofNat 32 (k+l.toNat))

private theorem flag_word (k : Nat) (bound : k<1024) :
    active≤(alignToDword (flag k)).toNat ∧ (alignToDword (flag k)).toNat<active+1024 := by
  unfold flag
  simp only [OpeningCursor.aligned,BitVec.toNat_ofNat]
  dsimp [active] at *
  omega

private theorem slot_word (p : Nat) (bound : p<257) :
    scratch≤(alignToDword (CheckCapSlots.address scratch p)).toNat ∧
    (alignToDword (CheckCapSlots.address scratch p)).toNat<scratch+1032 := by
  unfold CheckCapSlots.address
  simp only [OpeningCursor.aligned,BitVec.toNat_ofNat]
  dsimp [scratch,fp] at *
  omega

theorem flag_valid (k : Nat) (bound : k<1024) : accessValid (flag k) 1=true := by
  simp only [accessValid,rangeValid,flag,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by dsimp [active];omega : active+k<2^64),
    Bool.and_eq_true,decide_eq_true_eq,Nat.mod_one]
  constructor
  · unfold MEMORY_BYTES active;omega
  · trivial

theorem mark_read (s : MachineState) (q : Nat) (small : q<1024) (on : Bool) (j : Nat) (bound : j<512) :
    CheckCapSlots.read (memoryView (CapScanMemory.marked s (flag q) on)) scratch j =
    CheckCapSlots.read (memoryView s) scratch j := by
  cases on with
  | false=>rfl
  | true=>
    apply congrArg (fun y=>extractWord32 y (CheckCapSlots.half j))
    apply MachineState.getMem_setMem_ne
    intro eq
    have h:=congrArg BitVec.toNat eq
    have lim:=flag_word q small
    change (8*(scratch/8+j/2))%2^64=_ at h
    dsimp [scratch,fp,active] at *
    omega

theorem flag_effect (s : MachineState) (p k dst : Nat) (l r : Bool) (bd : dst<1024) (bp : p<257)
    (q : Nat) (bq : q<1024) :
    atByte (scanned s (flag dst) p k l r) q=if (l||r) && q==dst then 1 else atByte s q := by
  let m:=CapScanMemory.marked s (flag dst) (l||r)
  have away : alignToDword (flag q)≠alignToDword (CheckCapSlots.address scratch p) := by
    intro eq;have h:=congrArg BitVec.toNat eq;have a:=flag_word q bq;have b:=slot_word p bp
    dsimp [scratch,fp,active] at *;omega
  have plain : atByte (scanned s (flag dst) p k l r) q=atByte m q := by
    unfold scanned;by_cases eq : l=r
    · rw [ite_eq_left eq]
    · rw [ite_eq_right eq]
      apply congrArg (fun x => extractByte x (byteOffset (flag q)))
      exact MachineState.getMem_setMem_ne away
  rw [plain]
  cases on : l||r with
  | false=>simp [m,CapScanMemory.marked,on]
  | true=>
    change (if l||r then s.setByte (flag dst) 1 else s).getByte (flag q)=_
    simp only [on,Bool.true_and]
    rw [ite_true,set_byte_read]
    have test : (flag q==flag dst)=(q==dst):=HonestSizeRows.addr_eq bq bd
    rw [←test]
    by_cases eq : flag q=flag dst <;> simp [eq] <;> rfl

def Frame (s t : MachineState) :=
  ∀ a : Word, (a.toNat<active ∨ active+1024≤a.toNat) → (a.toNat<scratch ∨ scratch+1032≤a.toNat) →
    t.getMem a=s.getMem a

theorem frame (s : MachineState) (p k dst : Nat) (l r : Bool) (bd : dst<1024) (bp : p<257) :
    Frame s (scanned s (flag dst) p k l r) := by
  intro a aFlag aSlot
  have nf : a≠alignToDword (flag dst) := by rintro rfl;have h:=flag_word dst bd;omega
  have ns : a≠alignToDword (CheckCapSlots.address scratch p) := by rintro rfl;have h:=slot_word p bp;omega
  let m:=CapScanMemory.marked s (flag dst) (l||r)
  have clean : m.getMem a=s.getMem a := by
    unfold m CapScanMemory.marked;split
    · exact MachineState.getMem_setMem_ne nf
    · rfl
  unfold scanned
  split
  · exact clean
  · exact (MachineState.getMem_setMem_ne ns).trans clean

theorem refl (s : MachineState) : Frame s s := fun _ _ _=>rfl

theorem trans {s t u : MachineState} (a : Frame s t) (b : Frame t u) : Frame s u :=
  fun p hp hs => (b p hp hs).trans (a p hp hs)

end CommitGolfCandidate.Reconstruction.CheckCapScanData
