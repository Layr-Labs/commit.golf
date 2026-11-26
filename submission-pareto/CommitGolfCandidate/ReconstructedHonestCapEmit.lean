import CommitGolfCandidate.ReconstructedHonestCapScan

namespace CommitGolfCandidate.Reconstruction.HonestCapEmit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 HonestCapPlan HonestCapState HonestCapTables HonestCapStages HonestCapScan
open CommitBlocks (addr)

theorem collected (d n : Nat) : Step d (.collected n) := by
  intro s t coins ok known walk
  obtain ⟨_,_,width,limits⟩ := bounds (by simp) ok
  change n ≤ pairs d at limits
  have f := known.fields
  simp only [localFacts,holds_cons,holds_nil,and_true] at f
  have base : Common d s := known.base
  have dest := applyTable (emit_setup ⟨n,by omega⟩) known.atPc (by
    simp only [emitInput,holds_cons,holds_nil,and_true]; exact ⟨rfl,f.2,base.1⟩) walk
  have kept26 : t.getReg .x26=s.getReg .x26 := by frame_for .x26
  have kept20 : t.getReg .x20=s.getReg .x20 := by frame_for .x20
  by_cases empty : n=0
  · simp only [emitOutput,empty,ite_true] at dest
    refine ⟨⟨d,.finish⟩,by simp [next,empty],dest.1,by common_after,?_⟩
    reg_fields; exact kept26.trans f.1
  · simp only [emitOutput,ite_eq_right empty,holds_cons,holds_nil,and_true] at dest
    refine ⟨⟨d,.emit n 0⟩,by simp [next,empty],dest.1,by common_after,?_⟩
    reg_fields; exact ⟨kept20.trans f.2,dest.2.1,dest.2.2⟩

theorem emit (d n j : Nat) : Step d (.emit n j) := by
  intro s t coins ok known walk
  obtain ⟨_,_,width,limits⟩ := bounds (by simp) ok
  change n≤pairs d ∧ j<n at limits
  have f := known.fields
  simp only [localFacts,emitFacts,holds_cons,holds_nil,and_true] at f
  have dest := applyTable (emit_advance ⟨j,by omega⟩) known.atPc (by reg_input; exact f.2.1) walk
  have kept20 : t.getReg .x20=s.getReg .x20 := by frame_for .x20
  have kept25 : t.getReg .x25=s.getReg .x25 := by frame_for .x25
  refine ⟨⟨d,.emitGuard n (j+1)⟩,by lands,dest.1,by common_after,?_⟩
  reg_fields; exact ⟨kept20.trans f.1,(holds_cons ..).mp dest.2 |>.1,kept25.trans f.2.2⟩

theorem emit_guard (d n k : Nat) : Step d (.emitGuard n k) := by
  intro s t coins ok known walk
  obtain ⟨_,_,width,limits⟩ := bounds (by simp) ok
  change n≤pairs d ∧ 0<k ∧ k≤n at limits
  have f := known.fields
  simp only [localFacts,emitFacts,holds_cons,holds_nil,and_true] at f
  have dest := HonestCapGuards.emit s t coins known.atPc walk
  simp only [f.2.1,f.2.2,slots (n:=n) (j:=k) (by omega) (by omega)] at dest
  have kept20 : t.getReg .x20=s.getReg .x20 := by frame_for .x20
  have kept24 : t.getReg .x24=s.getReg .x24 := by frame_for .x24
  have kept25 : t.getReg .x25=s.getReg .x25 := by frame_for .x25
  by_cases done : k=n
  · refine ⟨⟨d,.lowDone n⟩,by simp [next,done],by simpa only [pc,ite_eq_left done] using dest,by common_after,?_⟩
    reg_fields; exact kept20.trans f.1
  · refine ⟨⟨d,.emit n k⟩,by simp [next,done],by simpa only [pc,ite_eq_right done] using dest,by common_after,?_⟩
    reg_fields; exact ⟨kept20.trans f.1,kept24.trans f.2.1,kept25.trans f.2.2⟩

theorem low_done (d n : Nat) : Step d (.lowDone n) := by
  intro s t coins ok known walk
  obtain ⟨lo,hi,width,limits⟩ := bounds (by simp) ok
  change n≤pairs d ∧ 0<n at limits
  have f := known.fields
  simp only [localFacts,holds_cons,holds_nil,and_true] at f
  have base : Common d s := known.base
  by_cases small : d<8
  · let q : Fin 7 := ⟨d-1,by omega⟩
    have eq : q.val+1=d := by dsimp [q]; omega
    have cert := ungrouped q
    rw [eq] at cert
    have dest := applyTable cert known.atPc (by
      simp only [ungroupedInput,holds_cons,holds_nil,and_true]; exact ⟨rfl,base.2.1⟩) walk
    refine ⟨⟨d,.finish⟩,by simp [next,small],dest.1,by common_after,?_⟩
    exact dest.2
  · let q : Fin 2 := ⟨d-8,by omega⟩
    have eq : q.val+8=d := by dsimp [q]; omega
    have cert := grouped q ⟨n,by omega⟩
    rw [eq] at cert
    have dest := applyTable cert known.atPc (by
      simp only [groupedInput,holds_cons,holds_nil,and_true]; exact ⟨rfl,base.2.1,f⟩) walk
    have kept20 : t.getReg .x20=s.getReg .x20 := by frame_for .x20
    simp only [groupedOutput,holds_cons,holds_nil,and_true] at dest
    refine ⟨⟨d,.group n 0⟩,by simp [next,small],dest.1,by common_after,?_⟩
    reg_fields
    exact ⟨dest.2.1,kept20.trans f,dest.2.2.1,by simpa only [Nat.mul_zero,Nat.sub_zero] using dest.2.2.2⟩

end CommitGolfCandidate.Reconstruction.HonestCapEmit
