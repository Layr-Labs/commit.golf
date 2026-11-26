import CommitGolfCandidate.TruncCodec
import CommitGolfCandidate.TruncHalf
import CommitGolfCandidate.TruncWireImage
namespace CommitGolfCandidate.Trunc.Wire
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 14000
set_option maxHeartbeats 250000
structure Move where
  source : Option Nat
  dest : Nat
deriving Repr, DecidableEq

def wide (record : Bool) : Nat := if record then 536 else 32
def short (record : Bool) : Nat := if record then 510 else 30
def count (back record : Bool) := (if back then wide record else short record)/2
def item (back record : Bool) (j : Nat) : Move :=
  if back then
    let d:=2*(count back record-1-j)
    ⟨localShort record d,d⟩
  else ⟨some (localWide record (2*j)),2*j⟩
def moves (back record : Bool) : List Move := (List.range (count back record)).map (item back record)

def instructions (m : Move) : List Instr :=
  match m.source with
  | none=>[.SH .x19 .x0 (BitVec.ofNat 12 m.dest)]
  | some a=>[.LHU .x6 .x18 (BitVec.ofNat 12 a),.SH .x19 .x6 (BitVec.ofNat 12 m.dest)]

def sequence (back record : Bool) := (moves back record).flatMap instructions
def after (m : Move) (s : MachineState) := (instructions m).foldl execInstrBr s

def byte (s : MachineState) (a : Nat) := s.getByte (BitVec.ofNat 64 a)
def copy (s : MachineState) (src : Option Nat) (dst : Nat) :=
  s.setHalfword (BitVec.ofNat 64 dst) ((src.map fun n=>s.getHalfword (BitVec.ofNat 64 n)).getD 0)

theorem wordEq (a b : Nat) (ba : a<2^64) (bb : b<2^64) :
    (BitVec.ofNat 64 a=BitVec.ofNat 64 b) ↔ a=b := by
  constructor
  · intro eq;have h:=congrArg BitVec.toNat eq
    rwa [BitVec.toNat_ofNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt ba,Nat.mod_eq_of_lt bb] at h
  · rintro rfl;rfl

theorem outside (s : MachineState) (src : Option Nat) (d q : Nat) (bd : d+2≤2^64) (bq : q<2^64)
    (even : d%2=0) (away : q≠d ∧ q≠d+1) : byte (copy s src d) q=byte s q := by
  unfold copy byte
  apply store_outside
  · rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : d<2^64)];exact even
  · refine ⟨fun bad=>away.1 ((wordEq q d bq (by omega)).mp bad),?_⟩
    intro eq;apply away.2;apply (wordEq q (d+1) bq (by omega)).mp
    rw [BitVec.ofNat_add];exact eq

theorem copied (s : MachineState) (d a : Nat) (bd : d+2≤2^64) (ba : a+2≤2^64)
    (ed : d%2=0) (ea : a%2=0) :
    byte (copy s (some a) d) d=byte s a ∧ byte (copy s (some a) d) (d+1)=byte s (a+1) := by
  have h:=copy_bytes s (BitVec.ofNat 64 a) (BitVec.ofNat 64 d)
    (by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : a<2^64)];exact ea)
    (by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : d<2^64)];exact ed)
  simpa only [copy,byte,Option.map_some,Option.getD_some,BitVec.ofNat_add,show BitVec.ofNat 64 1=(1 : Word) by decide] using h

theorem cleared (s : MachineState) (d : Nat) (bd : d+2≤2^64) (ed : d%2=0) :
    byte (copy s none d) d=0 ∧ byte (copy s none d) (d+1)=0 := by
  have h:=zero_bytes s (BitVec.ofNat 64 d) (by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : d<2^64)];exact ed)
  simpa only [copy,byte,Option.map_none,Option.getD_none,BitVec.ofNat_add,show BitVec.ofNat 64 1=(1 : Word) by decide] using h

theorem shortImm : ∀ i : Fin 537,signExtend12 (BitVec.ofNat 12 i.val)=BitVec.ofNat 64 i.val := by decide

theorem moveMem (s : MachineState) (src dst : Nat) (r : Move) (hb : r.dest≤536)
    (sb : ∀ i∈r.source,i≤536) (s18 : s.getReg .x18=BitVec.ofNat 64 src) (s19 : s.getReg .x19=BitVec.ofNat 64 dst) :
    (after r s).mem=(copy s (r.source.map (src+·)) (dst+r.dest)).mem := by
  rcases r with ⟨x,d⟩
  change d≤536 at hb
  have immD := shortImm ⟨d,by omega⟩
  cases x with
  | none =>
    change (s.setHalfword (s.getReg .x19+signExtend12 (BitVec.ofNat 12 d)) 0).mem=(s.setHalfword (BitVec.ofNat 64 (dst+d)) 0).mem
    rw [s19,show signExtend12 (BitVec.ofNat 12 d)=BitVec.ofNat 64 d from immD,BitVec.ofNat_add]
  | some i =>
    have bi : i≤536 := sb i (by simp)
    have immI : signExtend12 (BitVec.ofNat 12 i)=BitVec.ofNat 64 i := shortImm ⟨i,by omega⟩
    let t:=execInstrBr s (.LHU .x6 .x18 (BitVec.ofNat 12 i))
    have dm : t.mem=s.mem := rfl
    have dr : t.getReg .x19=s.getReg .x19 := rfl
    have vr : (t.getReg .x6).truncate 16=s.getHalfword (s.getReg .x18+signExtend12 (BitVec.ofNat 12 i)) := by
      change ((s.getHalfword _).zeroExtend 64).truncate 16=_
      simp
    change (t.setHalfword (t.getReg .x19+signExtend12 (BitVec.ofNat 12 d)) ((t.getReg .x6).truncate 16)).mem =
      (s.setHalfword (BitVec.ofNat 64 (dst+d)) (s.getHalfword (BitVec.ofNat 64 (src+i)))).mem
    rw [dr,vr,s18,s19,show signExtend12 (BitVec.ofNat 12 d)=BitVec.ofNat 64 d from immD,immI,
      BitVec.ofNat_add dst d,BitVec.ofNat_add src i]
    simp only [MachineState.setHalfword,MachineState.getMem,MachineState.setMem,dm]

theorem cores (back record : Bool) : (sequence back record).length =
    if record then (if back then 523 else 510) else (if back then 31 else 30) := by cases back <;> cases record <;> decide

end CommitGolfCandidate.Trunc.Wire
