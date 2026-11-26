import CommitGolfCandidate.ReconstructedHonestCapScan

namespace CommitGolfCandidate.Reconstruction.HonestCapGroups
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 HonestCapPlan HonestCapState HonestCapTables HonestCapStages HonestCapScan
open CommitBlocks (addr)

private theorem keepGroup {d n j : Nat} {phase : Phase} (s t : MachineState) (coins : Bool)
    (known : Matches ⟨d,phase⟩ s) (walk : Path coins s t) (old : holds s (groupFacts n j))
    (part : phase = .group n j ∨ (∃ r, phase = .inner n j r) ∨ (∃ r, phase = .digitGuard n j r)) :
    holds t (groupFacts n j) := by
  have fr : ∀ r ∈ [Reg.x26,.x20,.x21,.x24], t.getReg r=s.getReg r := by
    intro r hr
    apply frame _ _ _ known (by rcases part with e|⟨k,e⟩|⟨k,e⟩ <;> simp [e]) walk
    rcases part with rfl|⟨k,rfl⟩|⟨k,rfl⟩ <;>
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr <;>
      rcases hr with rfl|rfl|rfl|rfl <;> simp only [pc] <;> decide
  simp only [groupFacts,holds_cons,holds_nil,and_true] at old ⊢
  exact ⟨(fr .x26 (by decide)).trans old.1,(fr .x20 (by decide)).trans old.2.1,
    (fr .x21 (by decide)).trans old.2.2.1,(fr .x24 (by decide)).trans old.2.2.2⟩

theorem group (d n j : Nat) : Step d (.group n j) := by
  intro s t coins ok known walk
  obtain ⟨_,_,width,limits⟩ := bounds (by simp) ok
  change 8≤d ∧ n≤pairs d ∧ 4*j<n at limits
  have f := known.fields
  simp only [localFacts,groupFacts,holds_cons,holds_nil,and_true] at f
  have dest := applyTable (group_size ⟨n-4*j,by omega⟩) known.atPc (by reg_input; exact ⟨rfl,f.2.2.2⟩) walk
  refine ⟨⟨d,.inner n j (min 4 (n-4*j))⟩,by lands,dest.1,by common_after,?_⟩
  apply (holds_cons ..).mpr
  exact ⟨((holds_cons ..).mp dest.2).1,keepGroup s t coins known walk known.fields (Or.inl rfl)⟩

theorem inner (d n j r : Nat) : Step d (.inner n j r) := by
  intro s t coins ok known walk
  obtain ⟨_,_,_,limits⟩ := bounds (by simp) ok
  change 8≤d ∧ n≤pairs d ∧ 4*j<n ∧ 0<r ∧ r≤4 at limits
  have f := (holds_cons ..).mp known.fields
  let i : Fin 4 := ⟨r-1,by omega⟩
  have eq : i.val+1=r := by dsimp [i]; omega
  have cert := take_digit i
  rw [eq] at cert
  have dest := applyTable cert known.atPc (by reg_input; exact f.1) walk
  refine ⟨⟨d,.digitGuard n j (r-1)⟩,by lands,dest.1,by common_after,?_⟩
  apply (holds_cons ..).mpr
  exact ⟨((holds_cons ..).mp dest.2).1,keepGroup s t coins known walk f.2 (Or.inr (Or.inl ⟨r,rfl⟩))⟩

theorem digit_guard (d n j r : Nat) : Step d (.digitGuard n j r) := by
  intro s t coins ok known walk
  obtain ⟨_,_,_,limits⟩ := bounds (by simp) ok
  change 8≤d ∧ n≤pairs d ∧ 4*j<n ∧ r<4 at limits
  have f := (holds_cons ..).mp known.fields
  have dest := applyTable (HonestCapTables.digit_guard ⟨r,limits.2.2.2⟩) known.atPc
    (by reg_input; exact ⟨rfl,f.1⟩) walk
  have fields := keepGroup s t coins known walk f.2 (Or.inr (Or.inr ⟨r,rfl⟩))
  by_cases done : r=0
  · refine ⟨⟨d,.flush n j⟩,by simp [next,done],?_,by common_after,fields⟩
    simpa only [nextDigit,ite_eq_left done,pc] using dest.1
  · refine ⟨⟨d,.inner n j r⟩,by simp [next,done],?_,by common_after,?_⟩
    · simpa only [nextDigit,ite_eq_right done,pc] using dest.1
    · have kept : t.getReg .x30=s.getReg .x30 := by frame_for .x30
      exact (holds_cons ..).mpr ⟨kept.trans f.1,fields⟩

theorem flush (d n j : Nat) : Step d (.flush n j) := by
  intro s t coins ok known walk
  obtain ⟨_,_,width,limits⟩ := bounds (by simp) ok
  change 8≤d ∧ n≤pairs d ∧ 4*j<n at limits
  have f := known.fields
  simp only [localFacts,groupFacts,holds_cons,holds_nil,and_true] at f
  have dest := applyTable (flush_index ⟨j,by omega⟩) known.atPc (by reg_input; exact f.2.2.1) walk
  have kept26 : t.getReg .x26=s.getReg .x26 := by frame_for .x26
  have kept20 : t.getReg .x20=s.getReg .x20 := by frame_for .x20
  refine ⟨⟨d,.groupGuard n (j+1)⟩,by lands,dest.1,by common_after,?_⟩
  have new21 := ((holds_cons ..).mp dest.2).1
  by_cases rest : 4*(j+1)<n
  · let k : Fin 253 := ⟨n-4*(j+1),by omega⟩
    have eq : k.val+4=n-4*j := by dsimp [k]; omega
    have cert := flush_remaining k
    rw [eq] at cert
    have tail := applyTable cert known.atPc (by reg_input; exact f.2.2.2) walk
    simp only [localFacts,ite_eq_left rest,List.cons_append,List.nil_append,holds_cons,holds_nil,and_true]
    exact ⟨kept26.trans f.1,kept20.trans f.2.1,new21,((holds_cons ..).mp tail.2).1⟩
  · simp only [localFacts,ite_eq_right rest,List.append_nil,holds_cons,holds_nil,and_true]
    exact ⟨kept26.trans f.1,kept20.trans f.2.1,new21⟩

theorem group_guard (d n k : Nat) : Step d (.groupGuard n k) := by
  intro s t coins ok known walk
  obtain ⟨_,_,width,limits⟩ := bounds (by simp) ok
  change 8≤d ∧ n≤pairs d ∧ 0<k ∧ 4*(k-1)<n at limits
  have f := known.fields
  have kept26 : t.getReg .x26=s.getReg .x26 := by frame_for .x26
  have kept20 : t.getReg .x20=s.getReg .x20 := by frame_for .x20
  have kept21 : t.getReg .x21=s.getReg .x21 := by frame_for .x21
  have kept24 : t.getReg .x24=s.getReg .x24 := by frame_for .x24
  have dest := HonestCapGuards.group s t coins known.atPc walk
  by_cases rest : 4*k<n
  · simp only [localFacts,ite_eq_left rest,List.cons_append,List.nil_append,holds_cons,holds_nil,and_true] at f
    rw [f.2.2.1,f.2.1,unsigned (by omega) (by omega)] at dest
    refine ⟨⟨d,.group n k⟩,by simp [next,rest],by simpa only [pc,decide_eq_true_eq,ite_eq_left rest] using dest,by common_after,?_⟩
    reg_fields; exact ⟨kept26.trans f.1,kept20.trans f.2.1,kept21.trans f.2.2.1,kept24.trans f.2.2.2⟩
  · simp only [localFacts,ite_eq_right rest,List.append_nil,holds_cons,holds_nil,and_true] at f
    rw [f.2.2,f.2.1,unsigned (by omega) (by omega)] at dest
    refine ⟨⟨d,.finish⟩,by simp [next,rest],by simpa only [pc,decide_eq_true_eq,ite_eq_right rest] using dest,by common_after,?_⟩
    reg_fields; exact kept26.trans f.1

theorem finish (d : Nat) : Step d .finish := by
  intro s t coins ok known walk
  obtain ⟨lo,hi,_,_⟩ := bounds (by simp) ok
  let q : Fin 9 := ⟨d-1,by omega⟩
  have eq : q.val+1=d := by dsimp [q]; omega
  have cert := next_level q
  rw [eq] at cert
  have b : Common d s := known.base
  have dest := applyTable cert known.atPc (by reg_input; exact ⟨rfl,b.2.1⟩) walk
  by_cases last : d=1
  · have done : q.val=0 := by dsimp [q]; omega
    refine ⟨⟨0,.returned⟩,by simp [next,last],?_,trivial,holds_nil _⟩
    simpa only [below,ite_eq_left done,pc] using dest.1
  · have more : q.val≠0 := by dsimp [q]; omega
    have kept8 : t.getReg .x8=s.getReg .x8 := by frame_for .x8
    have kept11 : t.getReg .x11=s.getReg .x11 := by frame_for .x11
    have kept26 : t.getReg .x26=s.getReg .x26 := by frame_for .x26
    refine ⟨⟨d-1,.level⟩,by simp [next,last],?_,⟨kept8.trans b.1,((holds_cons ..).mp dest.2).1,kept11.trans b.2.2⟩,?_⟩
    · simpa only [below,ite_eq_right more,pc] using dest.1
    · reg_fields; exact kept26.trans (((holds_cons ..).mp known.fields).1)

end CommitGolfCandidate.Reconstruction.HonestCapGroups
