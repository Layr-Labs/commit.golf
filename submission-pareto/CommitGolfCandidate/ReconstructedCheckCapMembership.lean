import CommitGolfCandidate.ReconstructedCapSchedule

namespace CommitGolfCandidate.Reconstruction.CheckCapMembership
open HonestSizeSchedule HonestCapPlan
set_option maxRecDepth 14000
set_option maxHeartbeats 950000

theorem mem (base : Nat) (f : Nat→Bool) (j n id : Nat) :
    id∈CapOrder.ids base f j n ↔ ∃ k,j≤k ∧ k<j+n ∧ f (2*k)≠f (2*k+1) ∧ id=base+2*k+(f (2*k)).toNat := by
  induction n generalizing j with
  | zero=>simp [CapOrder.ids];omega
  | succ n ih=>
    rw [CapOrder.ids,List.mem_append,ih]
    have head : id∈CapOrder.entry base f j ↔ f (2*j)≠f (2*j+1) ∧ id=base+2*j+(f (2*j)).toNat := by
      by_cases eq : f (2*j)=f (2*j+1)
      · simp [CapOrder.entry,eq]
      · simp [CapOrder.entry,beq_eq_false_iff_ne.mpr eq,eq]
    rw [head]
    constructor
    · rintro (head|⟨k,lo,hi,tail⟩)
      · exact ⟨j,by omega,by omega,head⟩
      · exact ⟨k,by omega,by omega,tail⟩
    · rintro ⟨k,lo,hi,tail⟩
      by_cases same : k=j
      · subst k;exact Or.inl tail
      · exact Or.inr ⟨k,by omega,by omega,tail⟩

theorem nodup (base : Nat) (f : Nat→Bool) (j n : Nat) : (CapOrder.ids base f j n).Nodup := by
  induction n generalizing j with
  | zero=>simp [CapOrder.ids]
  | succ n ih=>
    rw [CapOrder.ids]
    by_cases eq : f (2*j)=f (2*j+1)
    · simpa [CapOrder.entry,eq] using ih (j+1)
    · simp only [CapOrder.entry,beq_eq_false_iff_ne.mpr eq,Bool.false_eq_true,ite_false,List.singleton_append,List.nodup_cons]
      refine ⟨?_,ih (j+1)⟩
      intro found
      have val:=CapOrder.id_bounds _ _ _ _ _ found
      have b : (f (2*j)).toNat≤1:=by cases f (2*j) <;> decide
      omega

def child (f : Nat→Bool) (d p : Nat) (right : Bool) := row f (9-d) (2*(p-pairs d)+right.toNat)
def used (f : Nat→Bool) (d p : Nat) := child f d p false || child f d p true

theorem decision (f : Nat→Bool) (d p : Nat) (pos : 0<d) (lo : pairs d≤p) (hi : p<2*pairs d) (side : Bool) :
    2*p+side.toNat∈CapSchedule.pending f d ↔ used f d p=true ∧ child f d p side=false := by
  let j:=p-pairs d
  have pdef : p=pairs d+j:=by dsimp [j];omega
  have bound : j<pairs d:=by omega
  have width:=(HonestCapState.powers d pos).1
  unfold CapSchedule.pending
  rw [mem]
  let a:=row f (9-d)
  change (∃ k,0≤k ∧ k<0+pairs d ∧ a (2*k)≠a (2*k+1) ∧ 2*p+side.toNat=2^d+2*k+(a (2*k)).toNat) ↔ _
  have parity (b : Bool) : b.toNat≤1:=by cases b <;> decide
  constructor
  · rintro ⟨k,_,hk,different,equal⟩
    have same : k=j := by have h1:=parity side;have h2:=parity (a (2*k));omega
    subst k
    change (a (2*j+0)||a (2*j+1))=true ∧ a (2*j+side.toNat)=false
    simp only [Nat.add_zero]
    cases side <;> cases l : a (2*j) <;> cases r : a (2*j+1) <;>
      simp_all [Bool.toNat_false,Bool.toNat_true] <;> omega
  · change (a (2*j+0)||a (2*j+1))=true ∧ a (2*j+side.toNat)=false → _
    rintro ⟨present,absent⟩
    refine ⟨j,by omega,by omega,?_,?_⟩
    all_goals cases side <;> cases l : a (2*j) <;> cases r : a (2*j+1) <;>
      simp_all [Bool.toNat_false,Bool.toNat_true] <;> omega

end CommitGolfCandidate.Reconstruction.CheckCapMembership
