import CommitGolfCandidate.ReconstructedCapScanWrite
import CommitGolfCandidate.ReconstructedHonestScanForward
import CommitGolfCandidate.ReconstructedHonestScanBytes

namespace CommitGolfCandidate.Reconstruction.CapScanMemory
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype TwoPermutationPrototype.RV64
open HonestCapTables (scratch addrSlot w)
open HonestScanBytes (after combine)
open CommitBlocks (addr)
set_option maxRecDepth 12000
set_option maxHeartbeats 1800000

def marked (s : MachineState) (x : Word) (active : Bool) := if active then s.setByte x 1 else s

theorem byte_congr {s t : MachineState} (same : s.mem=t.mem) (q : Word) (v : BitVec 8) :
    (s.setByte q v).mem=(t.setByte q v).mem := by
  cases s; cases t; cases same; rfl

theorem word_congr {s t : MachineState} (same : s.mem=t.mem) (q : Word) (v : BitVec 32) :
    (s.setWord32 q v).mem=(t.setWord32 q v).mem := by
  cases s; cases t; cases same; rfl

theorem read_congr {s t : MachineState} (same : s.mem=t.mem) (q : Nat) : memoryView s q=memoryView t q :=
  congrFun same (wordAddress q)

private theorem branch_model (s : MachineState) (b : Bool) (a z : Word) :
    (if b then s.setPC a else s.setPC z).mem=s.mem ∧ ∀ r, (if b then s.setPC a else s.setPC z).getReg r=s.getReg r := by
  cases b <;> exact ⟨rfl,fun _ => rfl⟩

theorem after_model (s : MachineState) (active : Bool) (one : s.getReg .x11=1) :
    (after s active).mem=(marked s (s.getReg .x24) active).mem := by
  let c := HonestScanBytes.combine s
  let b := HonestScanBytes.branch s
  have equiv : b.mem=c.mem ∧ ∀ x, b.getReg x=c.getReg x :=
    branch_model c _ _ _
  have mem : b.mem=s.mem := equiv.1
  cases active with
  | false => exact mem
  | true =>
    change (b.setByte (b.getReg .x24+signExtend12 0) ((b.getReg .x11).truncate 8)).mem=(s.setByte (s.getReg .x24) 1).mem
    have ptr : b.getReg .x24=s.getReg .x24 := equiv.2 _
    have unit : b.getReg .x11=1 := (equiv.2 _).trans one
    rw [ptr,unit,show signExtend12 0=0#64 from rfl,BitVec.add_zero]
    exact byte_congr mem _ _

def scanned (s : MachineState) (x : Word) (p k : Nat) (l r : Bool) :=
  let previous := marked s x (l||r)
  if l=r then previous else previous.setWord32 (addrSlot p) (BitVec.ofNat 32 (k+l.toNat))

theorem exact (s t : MachineState) (coins : Bool) (pc : s.pc=addr 1470) (path : HonestCapState.Path coins s t)
    (p : Fin 257) (k : Nat) (l r : Bool) (lo : s.getByte (s.getReg .x23)=HonestFlagState.code l)
    (hi : s.getByte (s.getReg .x16)=HonestFlagState.code r) (unit : s.getReg .x11=1)
    (count : s.getReg .x20=w p.val) (scratchPtr : s.getReg .x9=w scratch) (idbase : s.getReg .x21=w k) :
    t.mem=(scanned s (s.getReg .x24) p.val k l r).mem := by
  let u := after s (l||r)
  obtain ⟨rest,loc⟩ := HonestScanBytes.afterPath s t coins pc path l r lo hi
  obtain ⟨_,ll,rr⟩ := HonestScanBytes.getCombine s l r lo hi
  have rg (x : Reg) : u.getReg x=(HonestScanBytes.combine s).getReg x := HonestScanBytes.after_reg .. 
  have write := CapScanWrite.effects u t coins loc rest p k l r ((rg _).trans ll) ((rg _).trans rr)
    ((rg _).trans idbase) ((rg _).trans scratchPtr) ((rg _).trans count)
  have m := after_model s (l||r) unit
  by_cases same : l=r
  · exact write.trans ((ite_eq_left same).trans (m.trans (by simp only [scanned,ite_eq_left same])))
  · rw [ite_eq_right same] at write
    simp only [scanned,ite_eq_right same]
    exact write.trans (word_congr m _ _)

private theorem slot_away (j : Fin 512) (x : Word) (bound : x.toNat<2^24) :
    wordAddress (CapSlots.cell j.val)≠alignToDword x := by
  intro same
  have eq := congrArg BitVec.toNat same
  have small := (HonestMemoryRanges.aligned_window x).1
  change (8*(8589934272+j.val/2))%2^64=(alignToDword x).toNat at eq
  have hi := j.isLt
  omega

theorem mark_read (s : MachineState) (x : Word) (active : Bool) (j : Fin 512) (low : x.toNat<2^24) :
    CapSlots.read (memoryView (marked s x active)) j.val=CapSlots.read (memoryView s) j.val := by
  cases active with
  | false => rfl
  | true =>
    unfold CapSlots.read
    apply congrArg (fun y => extractWord32 y (CapSlots.half j.val))
    exact MachineState.getMem_setMem_ne (slot_away j x low)

theorem ordered (s t : MachineState) (parent : Word) (below : parent.toNat<2^24) (f : Nat→Bool)
    (base j : Nat) (p : Fin 257) (length : (CapOrder.ids base f 0 j).length=p.val)
    (old : CapSlots.Contains (memoryView s) (CapOrder.ids base f 0 j))
    (effect : t.mem=(scanned s parent p.val (base+2*j) (f (2*j)) (f (2*j+1))).mem) :
    CapSlots.Contains (memoryView t) (CapOrder.ids base f 0 (j+1)) := by
  classical
  let xs := CapOrder.ids base f 0 j
  let l := f (2*j)
  let r := f (2*j+1)
  let m := marked s parent (l||r)
  have previous : CapSlots.Contains (memoryView m) xs := by
    intro i
    have inRange : i.val<512 := by have a := i.isLt; change xs.length=p.val at length; have b := p.isLt; omega
    exact (mark_read s parent (l||r) ⟨i.val,inRange⟩ below).trans (old i)
  rw [CapOrder.ids_snoc,Nat.zero_add]
  change CapSlots.Contains (memoryView t) (xs ++ (if l==r then [] else [base+2*j+l.toNat]))
  by_cases same : l=r
  · have e : (l==r)=true := beq_iff_eq.mpr same
    change t.mem=(if l=r then m else _).mem at effect
    rw [ite_eq_left same] at effect
    simp only [e,ite_true,List.append_nil]
    intro i
    exact (congrArg (fun y => extractWord32 y (CapSlots.half i.val)) (read_congr effect _)).trans (previous i)
  · let value := base+2*j+l.toNat
    have e : (l==r)=false := beq_eq_false_iff_ne.mpr same
    have typed : t.mem=(m.setWord32 (addrSlot p.val) (BitVec.ofNat 32 value)).mem := by
      change t.mem=(if l=r then m else m.setWord32 (addrSlot p.val) (BitVec.ofNat 32 value)).mem at effect
      rwa [ite_eq_right same] at effect
    have appended := CapSlots.append (memoryView m) xs value previous
    change xs.length=p.val at length
    rw [length] at appended
    simp only [e,Bool.false_eq_true,ite_false]
    intro i
    have span : i.val<512 := by
      have a := i.isLt
      change i.val<(xs++[value]).length at a
      have ln : (xs++[value]).length=p.val+1 := by rw [List.length_append,length,List.length_singleton]
      have a2 := a.trans_le ln.le
      have b := p.isLt
      omega
    have cells := (read_congr typed (CapSlots.cell i.val)).trans
      (CapSlots.store_id m ⟨p.val,by have b := p.isLt;omega⟩ (BitVec.ofNat 32 value) (CapSlots.cell i.val)
        (by change 8589934272+i.val/2<2^33; omega))
    exact (congrArg (fun z => extractWord32 z (CapSlots.half i.val)) cells).trans (appended i)

end CommitGolfCandidate.Reconstruction.CapScanMemory
