import CommitGolfCandidate.ReconstructedHonestCapState

namespace CommitGolfCandidate.Reconstruction.HonestCapScan
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 HonestCapPlan HonestCapState HonestCapTables HonestCapStages
open CommitBlocks (addr)

abbrev Step (d : Nat) (p : Phase) := ∀ (s t : MachineState) (coins : Bool), legal ⟨d,p⟩ →
    Matches ⟨d,p⟩ s → Path coins s t → ∃ v ∈ next d p, Matches v t

macro "common_after" : tactic => `(tactic| exact common_next _ _ _ (by assumption) (by simp) (by simp) (by simp) (by assumption))
macro "frame_for" r:term : tactic => `(tactic|exact frame _ _ _ (by assumption) (by simp) (by assumption) $r (by simp only [pc]; decide))
macro "reg_fields" : tactic => `(tactic| simp only [localFacts,scanFacts,emitFacts,groupFacts,holds_cons,holds_nil,and_true])
macro "reg_input" : tactic => `(tactic| simp only [holds_cons,holds_nil,and_true])
macro "lands" : tactic => `(tactic|simp only [next,List.mem_singleton])

theorem enter (d : Nat) : Step d .enter := by
  intro s t coins ok known walk
  have zero : s.getReg .x0 = 0 := rfl
  have a := applyTable init known.atPc (by reg_input; exact zero) walk
  obtain ⟨pcOut,h⟩ := a
  simp only [level,holds_cons,holds_nil,and_true] at h
  have kept : t.getReg .x8 = s.getReg .x8 := by frame_for .x8
  refine ⟨⟨9,.level⟩,by lands,pcOut,⟨kept.trans known.base,h.2.1,h.2.2.1⟩,?_⟩
  reg_fields
  exact h.2.2.2

theorem level_start (d : Nat) : Step d .level := by
  intro s t coins ok known walk
  obtain ⟨lo,hi,_,_⟩ := bounds (by simp) ok
  let q : Fin 9 := ⟨d-1,by omega⟩
  have eq : q.val+1=d := by dsimp [q]; omega
  have cert := start q
  rw [eq] at cert
  have old : Common d s := known.base
  have unit : s.getReg .x26=2 := by simpa only [localFacts,holds_cons,holds_nil,and_true] using known.fields
  have a := applyTable cert known.atPc (by
    simp only [level,holds_cons,holds_nil,and_true]; exact ⟨rfl,old.2.1,old.2.2,unit⟩) walk
  obtain ⟨pcOut,h⟩ := a
  simp only [first_pair,holds_cons,holds_nil,and_true] at h
  obtain ⟨p1,p2⟩ := powers d lo
  rw [p1,p2] at h
  have kept : t.getReg .x26=s.getReg .x26 := by frame_for .x26
  refine ⟨⟨d,.scan 0 0⟩,by lands,pcOut,by common_after,?_⟩
  reg_fields
  exact ⟨kept.trans unit,h.1,by simpa only [scanIndex,Nat.add_zero] using h.2.1,h.2.2⟩

theorem scan (d j p : Nat) : Step d (.scan j p) := by
  intro s t coins ok known walk
  obtain ⟨_,_,width,limits⟩ := bounds (by simp) ok
  change j < pairs d ∧ p ≤ j at limits
  have fields := known.fields
  simp only [localFacts,scanFacts,holds_cons,holds_nil,and_true] at fields
  have count := scan_pending ⟨p,by omega⟩ s t coins known.atPc fields.2.1 walk
  have idx := applyTable (pair_advance ⟨pairs d+j,by omega⟩) known.atPc (by reg_input; exact fields.2.2.1) walk
  have shift : (2*(pairs d+j)+2) = 2*(pairs d+(j+1)) := by omega
  have newIndex : t.getReg .x21=scanIndex d (j+1) := by
    have h := idx.2; rw [holds_cons] at h; unfold scanIndex; rw [← shift]; exact h.1
  have kept26 : t.getReg .x26=s.getReg .x26 := by frame_for .x26
  have kept22 : t.getReg .x22=s.getReg .x22 := by frame_for .x22
  have base : Common d t := by common_after
  rcases count.2 with equal | incr
  · refine ⟨⟨d,.scanGuard (j+1) p⟩,by simp [next],count.1,base,?_⟩
    reg_fields; exact ⟨kept26.trans fields.1,equal,newIndex,kept22.trans fields.2.2.2⟩
  · refine ⟨⟨d,.scanGuard (j+1) (p+1)⟩,by simp [next],count.1,base,?_⟩
    reg_fields; exact ⟨kept26.trans fields.1,incr,newIndex,kept22.trans fields.2.2.2⟩

theorem scan_guard (d k p : Nat) : Step d (.scanGuard k p) := by
  intro s t coins ok known walk
  obtain ⟨_,_,width,limits⟩ := bounds (by simp) ok
  change 0<k ∧ k≤pairs d ∧ p≤k at limits
  have f := known.fields
  simp only [localFacts,scanFacts,holds_cons,holds_nil,and_true] at f
  have dest := HonestCapGuards.scan s t coins known.atPc walk
  rw [f.2.2.1,f.2.2.2,scanIndex,unsigned (by omega) (by omega)] at dest
  have iff : 2*(pairs d+k) < 4*pairs d ↔ k<pairs d := by omega
  simp only [decide_eq_true_eq,iff] at dest
  have kept26 : t.getReg .x26=s.getReg .x26 := by frame_for .x26
  have kept20 : t.getReg .x20=s.getReg .x20 := by frame_for .x20
  have kept21 : t.getReg .x21=s.getReg .x21 := by frame_for .x21
  have kept22 : t.getReg .x22=s.getReg .x22 := by frame_for .x22
  by_cases more : k<pairs d
  · refine ⟨⟨d,.scan k p⟩,by simp [next,more],by simpa only [ite_eq_left more,pc] using dest,by common_after,?_⟩
    reg_fields; exact ⟨kept26.trans f.1,kept20.trans f.2.1,kept21.trans f.2.2.1,kept22.trans f.2.2.2⟩
  · refine ⟨⟨d,.collected p⟩,by simp [next,more],by simpa only [ite_eq_right more,pc] using dest,by common_after,?_⟩
    reg_fields; exact ⟨kept26.trans f.1,kept20.trans f.2.1⟩

end CommitGolfCandidate.Reconstruction.HonestCapScan
