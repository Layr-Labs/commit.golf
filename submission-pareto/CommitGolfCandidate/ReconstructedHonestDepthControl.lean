import CommitGolfCandidate.ReconstructedHonestDepthPair

namespace CommitGolfCandidate.Reconstruction.HonestDepthControl
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp HonestCapPlan HonestCapState HonestSizeSchedule HonestCapStages
open TwoPermutationPrototype.RV64 HonestDepthPair
open HonestCapTables (w)
open HonestCapRam (activeBase)
open HonestSizeRows (Rows)
open CommitBlocks (addr)
set_option maxRecDepth 16384
attribute [local irreducible] ArtifactEncoding.decode execute

private theorem quiet (v : Phase) (d j n : Nat) (s t : MachineState) (f : Nat→Bool) (trap : CommitStorage.Trapdoor)
    (ps : Positions) (fs : List Wire.Field) (small : pairs d≤256) (old : Data f d j s trap ps fs)
    (start : s.pc=addr (pc v)) (path : HonestCapState.Path true s t) (notStart : v≠.enter) (live : v≠.returned)
    (registered : (pc v,n)∈CapControlMemory.prices) (cursor : t.getReg .x7=s.getReg .x7) : Data f d j t trap ps fs := by
  have mem := CapControlMemory.actual (pc v) n registered s t true start path
  have view : memoryView t=memoryView s := funext (CapScanMemory.read_congr mem)
  refine ⟨CapEvidence.rows_of_outside s t f d j small old.rows (fun q _ _ => congrFun view q),view ▸ old.slots,
    CapGlobal.transferred v s t trap ps old.global notStart live start path (CapFrame.stored s t mem),
    ⟨cursor.trans old.buffer.cursor,view ▸ old.buffer.output⟩⟩

theorem enter (o : Oracle) (f : Nat→Bool) (d : Nat) (pos : 0<d) (small : d≤9) (s : MachineState)
    (trap : CommitStorage.Trapdoor) (ps : Positions) (fs : List Wire.Field) (start : Matches ⟨d,.level⟩ s)
    (rows : Rows f d 0 s) (common : CapGlobal.Common s trap ps) (buf : CapEvidence.Buffer s fs) :
    ∃ k t, k≤14 ∧ CommitExact.Segment o image k s t ∧ Matches ⟨d,.scan 0 (prefixCount f d 0)⟩ t ∧
      Ptr d 0 t ∧ Data f d 0 t trap ps fs := by
  obtain ⟨k,t,time,path,run⟩ := CapControlForward.forward o s 1451 14 [] (CapControlForward.arithmetic _ _ (by decide))
    start.atPc (holds_nil _)
  have legal0 : legal ⟨d,.level⟩ := ⟨⟨pos,small⟩,trivial⟩
  obtain ⟨v,edge,know⟩ := HonestCapScan.level_start d s t true legal0 start path
  simp only [next,List.mem_singleton] at edge;subst v
  let q : Fin 9 := ⟨d-1,by omega⟩
  have eq : q.val+1=d := by dsimp [q];omega
  have inp : holds s [(.x0,0),(.x10,w d),(.x11,1),(.x13,w activeBase),(.x26,2)] := by
    simp only [holds_cons,holds_nil,and_true]
    exact ⟨rfl,start.base.2.1,start.base.2.2,common.regs _ _ (by decide),
        ((holds_cons ..).mp start.fields).1⟩
  have child := HonestCapOperands.children_start q
  have pr := HonestCapMetadata.pair_start q
  rw [eq] at child pr
  have c := (applyTable child start.atPc inp path).2
  have p := (applyTable pr start.atPc inp path).2
  simp only [holds_cons,holds_nil,and_true] at p
  have slots : CapSlots.Contains (memoryView s) (ids f d 0) := by intro j;have n := j.isLt;change j.val<0 at n;omega
  have cursor := HonestCapMetadata.frame 1451 14 (by decide) s t true start.atPc path .x7 (by decide)
  exact ⟨k,t,time,run,know,⟨by simpa only [Nat.add_zero] using c,by simpa only [HonestCapMetadata.scanPtr,Nat.add_zero] using p⟩,
    quiet .level d 0 14 s t f trap ps fs (width_bound d small) ⟨rows,slots,common,buf⟩ start.atPc path
      (by simp) (by simp) (by decide) cursor⟩

theorem guard (o : Oracle) (f : Nat→Bool) (d j : Nat) (pos : 0<d) (small : d≤9) (passed : 0<j) (limit : j≤pairs d)
    (s : MachineState) (trap : CommitStorage.Trapdoor) (ps : Positions) (fs : List Wire.Field)
    (start : Matches ⟨d,.scanGuard j (prefixCount f d j)⟩ s) (ptr : Ptr d j s) (data : Data f d j s trap ps fs) :
    ∃ k t, k≤1 ∧ CommitExact.Segment o image k s t ∧
      Matches ⟨d,if j<pairs d then .scan j (prefixCount f d j) else .collected (prefixCount f d j)⟩ t ∧
      Ptr d j t ∧ Data f d j t trap ps fs := by
  obtain ⟨k,t,time,path,run⟩ := CapControlForward.forward o s 1469 1 [] (CapControlForward.arithmetic _ _ (by decide))
    start.atPc (holds_nil _)
  have legal0 : legal ⟨d,.scanGuard j (prefixCount f d j)⟩ := ⟨⟨pos,small⟩,passed,limit,size f d j⟩
  obtain ⟨v,edge,know⟩ := HonestCapScan.scan_guard d j _ s t true legal0 start path
  simp only [next,List.mem_singleton] at edge;subst v
  have parent := HonestFrame.sound Artifact.openingCode image (Eq.refl (ArtifactEncoding.decode 32 _)) (by decide)
    stops [.x24] 1 (addr 1469) (by decide +kernel) true s t start.atPc path .x24 (by simp)
  have cursor := HonestCapMetadata.frame 1469 1 (by decide) s t true start.atPc path .x7 (by decide)
  exact ⟨k,t,time,run,know,⟨HonestCapOperands.guard_children _ _ _ true start.atPc ptr.child path,parent.trans ptr.parent⟩,
    quiet (.scanGuard j (prefixCount f d j)) d j 1 s t f trap ps fs (width_bound d small) data start.atPc path
      (by simp) (by simp) (by change (1469,1)∈CapControlMemory.prices; decide) cursor⟩

end CommitGolfCandidate.Reconstruction.HonestDepthControl
