import CommitGolfCandidate.ReconstructedCheckCapScanData

namespace CommitGolfCandidate.Reconstruction.CheckCapScanData
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype TwoPermutationPrototype.RV64
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

theorem ordered (s t : MachineState) (dst : Nat) (below : dst<1024) (f : Nat→Bool)
    (base j : Nat) (p : Fin 257) (length : (CapOrder.ids base f 0 j).length=p.val)
    (old : CheckCapSlots.Contains (memoryView s) scratch (CapOrder.ids base f 0 j))
    (effect : t.mem=(scanned s (flag dst) p.val (base+2*j) (f (2*j)) (f (2*j+1))).mem) :
    CheckCapSlots.Contains (memoryView t) scratch (CapOrder.ids base f 0 (j+1)) := by
  classical
  let xs := CapOrder.ids base f 0 j
  let l := f (2*j)
  let r := f (2*j+1)
  let m := CapScanMemory.marked s (flag dst) (l||r)
  have previous : CheckCapSlots.Contains (memoryView m) scratch xs := by
    intro i
    have inRange : i.val<512 := by have a := i.isLt; change xs.length=p.val at length; have b := p.isLt; omega
    exact (mark_read s dst below (l||r) i.val inRange).trans (old i)
  rw [CapOrder.ids_snoc,Nat.zero_add]
  change CheckCapSlots.Contains (memoryView t) scratch (xs ++ (if l==r then [] else [base+2*j+l.toNat]))
  by_cases same : l=r
  · have e : (l==r)=true := beq_iff_eq.mpr same
    change t.mem=(if l=r then m else _).mem at effect
    rw [ite_eq_left same] at effect
    simp only [e,ite_true,List.append_nil]
    intro i
    exact (congrArg (fun y => extractWord32 y (CheckCapSlots.half i.val)) (CapScanMemory.read_congr effect _)).trans (previous i)
  · let value := base+2*j+l.toNat
    have e : (l==r)=false := beq_eq_false_iff_ne.mpr same
    have typed : t.mem=(m.setWord32 (CheckCapSlots.address scratch p.val) (BitVec.ofNat 32 value)).mem := by
      change t.mem=(if l=r then m else m.setWord32 (CheckCapSlots.address scratch p.val) (BitVec.ofNat 32 value)).mem at effect
      rwa [ite_eq_right same] at effect
    have appended := CheckCapSlots.append (memoryView m) scratch xs value previous
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
    have cells := (CapScanMemory.read_congr typed (CheckCapSlots.cell scratch i.val)).trans
      (CheckCapSlots.store_id m scratch p.val (BitVec.ofNat 32 value) (by decide) (by have h:=p.isLt;change 68719473368+4*p.val+4≤68719476736;omega) (CheckCapSlots.cell scratch i.val)
        (by change 8589934171+i.val/2<2^33; omega))
    exact (congrArg (fun z => extractWord32 z (CheckCapSlots.half i.val)) cells).trans (appended i)

end CommitGolfCandidate.Reconstruction.CheckCapScanData
