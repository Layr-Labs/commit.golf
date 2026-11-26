import CommitGolfCandidate.ReconstructedCapLowLoop
import CommitGolfCandidate.ReconstructedCapHeaderPiece
import CommitGolfCandidate.ReconstructedCapControlValues
import CommitGolfCandidate.ReconstructedHonestCapEmit

namespace CommitGolfCandidate.Reconstruction.CapLevelSetup
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 HonestCapPlan HonestCapState HonestCapStages OpeningCursor
open TwoPermutationPrototype.RV64
open CommitBlocks (addr)
set_option maxRecDepth 20000
set_option maxHeartbeats 1900000

private theorem carry (d : Nat) (xs : List Nat) (fs : List Wire.Field) (s t : MachineState) (which : Bool)
    (trap : CommitStorage.Trapdoor) (ps : Positions) (f : Nat→Bool) (data : CapLevelData.Packed s trap ps f d xs fs)
    (small : pairs d≤256) (bound : xs.length≤256)
    (start : s.pc=addr (if which then 1483 else 1581)) (walk : HonestCapState.Path true s t) :
    CapLevelData.Packed t trap ps f d xs fs := by
  let i := if which then 1483 else 1581
  let n := if which then 26 else 16
  have item : (i,n)∈CapControlMemory.prices := by cases which <;> decide
  have exactMem := CapControlMemory.actual i n item s t true start walk
  have cert : HonestFrame.check Artifact.openingCode stops (.x7::CapLevelData.kept) n (addr i)=true := by
    cases which <;> decide +kernel
  have keep := HonestFrame.sound Artifact.openingCode HonestCapState.image (Eq.refl (ArtifactEncoding.decode 32 _)) (by decide)
    stops (.x7::CapLevelData.kept) n _ cert true s t start walk
  apply CapLevelData.change s t trap ps f d xs fs fs data small (by omega)
  · exact CapEvidence.direct s t fs data.buffer (keep _ List.mem_cons_self) (fun q _ => CapScanMemory.read_congr exactMem _)
  · exact fun q h => keep q (List.mem_cons_of_mem _ h)
  · exact fun q _ _ => CapScanMemory.read_congr exactMem q

theorem collected (o : Oracle) (d : Fin 10) (pos : 0<d.val) (xs : List Nat) (size : xs.length≤pairs d.val)
    (s : MachineState) (trap : CommitStorage.Trapdoor) (ps : Positions) (f : Nat→Bool) (fs : List Wire.Field)
    (known : Matches ⟨d.val,.collected xs.length⟩ s) (data : CapLevelData.Packed s trap ps f d.val xs fs) :
    ∃ n t, n≤26 ∧ CommitExact.Segment o HonestCapState.image n s t ∧ CapLevelData.Packed t trap ps f d.val xs fs ∧
      (xs=[] → Matches ⟨d.val,.finish⟩ t) ∧ (xs≠[] → t.pc=addr 1512 ∧ CapLowLoop.Local t d.val xs.length 0) := by
  have high := d.isLt
  have width := width_bound d.val (by omega)
  have initial : holds s (CapControlForward.beforeWidth d.val) := by
    simp only [CapControlForward.beforeWidth,holds_cons,holds_nil,and_true];exact ⟨rfl,data.common.source.frame,data.depth⟩
  obtain ⟨n,t,limit,path,seg⟩ := CapControlForward.forward o s 1483 26 _ (CapControlForward.masks d) known.atPc initial
  have preserved := carry d.val xs fs s t true trap ps f data width (by omega) known.atPc path
  obtain ⟨v,node,atEnd⟩ := HonestCapEmit.collected d.val xs.length s t true ⟨⟨pos,by change d.val≤9;omega⟩,size⟩ known path
  simp only [next,List.mem_singleton] at node
  subst v
  refine ⟨n,t,limit,seg,preserved,?_,?_⟩
  · intro empty
    have len : xs.length=0 := empty ▸ rfl
    simpa only [len,ite_true] using atEnd
  · intro full
    have len : xs.length≠0 := fun h => full (List.length_eq_zero_iff.mp h)
    simp only [ite_eq_right len] at atEnd
    have outPC : t.pc=addr 1512 := atEnd.atPc
    let q : Fin 9 := ⟨d.val-1,by omega⟩
    have direct : q.val+1=d.val := by dsimp [q];omega
    have table := CapControlValues.lowTable q
    rw [direct] at table
    have mem : CapControlValues.reads s (CapControlValues.lowCells d.val) := by
      intro a v h
      simp only [CapControlValues.lowCells,List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with h|h <;> cases h
      · exact data.common.source.lows d
      · exact data.common.source.shiftMask
    have masks := CapControlValues.compute s t true 1483 26 1512 _ _ _ table known.atPc outPC initial mem path
    have fields := atEnd.fields
    simp only [CapControlValues.lowOut,holds_cons,holds_nil,and_true] at masks
    simp only [localFacts,emitFacts,holds_cons,holds_nil,and_true] at fields
    exact ⟨outPC,fields.1,fields.2.1,fields.2.2,masks.2.2,masks.2.1,masks.1⟩

theorem doneLow (o : Oracle) (d : Fin 10) (pos : 0<d.val) (xs : List Nat) (count : 0<xs.length) (size : xs.length≤pairs d.val)
    (s : MachineState) (trap : CommitStorage.Trapdoor) (ps : Positions) (f : Nat→Bool) (fs : List Wire.Field)
    (pc : s.pc=addr 1581) (local_ : CapLowLoop.Local s d.val xs.length xs.length) (data : CapLevelData.Packed s trap ps f d.val xs fs) :
    ∃ n t, n≤16 ∧ CommitExact.Segment o HonestCapState.image n s t ∧ CapLevelData.Packed t trap ps f d.val xs fs ∧
      (d.val<8 → Matches ⟨d.val,.finish⟩ t) ∧ (8≤d.val → t.pc=addr 1603 ∧ CapHeaderPiece.Local t d.val xs.length 0) := by
  have high := d.isLt
  have width := width_bound d.val (by omega)
  have known : Matches ⟨d.val,.lowDone xs.length⟩ s :=
    ⟨pc,⟨data.common.source.frame,data.depth,data.one⟩,by simp only [localFacts,holds_cons,holds_nil,and_true];exact local_.pending⟩
  have initial : holds s (CapControlForward.beforeGroup d.val) := by
    simp only [CapControlForward.beforeGroup,holds_cons,holds_nil,and_true];exact ⟨rfl,data.common.source.frame,data.depth,local_.table⟩
  obtain ⟨n,t,limit,path,seg⟩ := CapControlForward.forward o s 1581 16 _ (CapControlForward.groups d) known.atPc initial
  have preserved := carry d.val xs fs s t false trap ps f data width (by omega) pc path
  obtain ⟨v,node,atEnd⟩ := HonestCapEmit.low_done d.val xs.length s t true ⟨⟨pos,by change d.val≤9;omega⟩,size,count⟩ known path
  simp only [next,List.mem_singleton] at node
  subst v
  refine ⟨n,t,limit,seg,preserved,?_,?_⟩
  · intro small;simpa only [ite_eq_left small] using atEnd
  · intro paid
    simp only [ite_eq_right (show ¬d.val<8 by omega)] at atEnd
    have outPC : t.pc=addr 1603 := atEnd.atPc
    let q : Fin 2 := ⟨d.val-8,by omega⟩
    have direct : q.val+8=d.val := by dsimp [q];omega
    have table := CapControlValues.paidTable q
    rw [direct] at table
    have mem : CapControlValues.reads s (CapControlValues.paidCells d.val) := by
      intro a v h
      simp only [CapControlValues.paidCells,List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with h|h <;> cases h
      · exact data.common.source.widths d
      · exact data.common.source.headerMask
    have masks := CapControlValues.compute s t true 1581 16 1603 _ _ _ table known.atPc outPC initial mem path
    have fields := atEnd.fields
    simp only [CapControlValues.paidOut,holds_cons,holds_nil,and_true] at masks
    simp only [localFacts,groupFacts,holds_cons,holds_nil,Nat.mul_zero,Nat.sub_zero,and_true] at fields
    exact ⟨outPC,fields.2.1,masks.1,masks.2.1,fields.2.2.2,masks.2.2.1,masks.2.2.2,fields.1⟩

end CommitGolfCandidate.Reconstruction.CapLevelSetup
