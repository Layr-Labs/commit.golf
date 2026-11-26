import CommitGolfCandidate.ReconstructedHonestCapOperands
import CommitGolfCandidate.ReconstructedHonestCapInvariant

namespace CommitGolfCandidate.Reconstruction.HonestSizeCursor
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 HonestCapStages HonestCapTables HonestCapInvariant
open HonestCapState HonestCapOperands HonestCapPlan
open CommitBlocks (addr)

set_option maxRecDepth 32768
attribute [local irreducible] ArtifactEncoding.decode

def detail (d : Nat) (p : Phase) (s : MachineState) : Prop := match p with
  | .scan j _ | .scanGuard j _ => holds s (children (pairs d+j))
  | .emit .. | .emitGuard .. => s.getReg .x23=w (if d<8 then 48 else 32)
  | _ => True

theorem maintained {v w' : Node} {s t : MachineState} {coins : Bool} (ok : legal v)
    (known : Matches v s) (ext : Extra v s) (more : detail v.depth v.phase s) (live : v.phase≠.returned)
    (path : Path coins s t) (edge : w'∈next v.depth v.phase) (matched : Matches w' t) :
    detail w'.depth w'.phase t := by
  obtain ⟨d,p⟩ := v
  have bits := bounds live ok
  cases p <;> simp only [next,List.mem_cons,List.not_mem_nil,or_false] at edge
  all_goals try (obtain rfl := edge; trivial)
  case level =>
    obtain rfl := edge
    let q : Fin 9 := ⟨d-1,by omega⟩
    have eq : q.val+1=d := by dsimp [q]; omega
    have cert := children_start q
    rw [eq] at cert
    have base : Common d s := known.base
    have pointers := ext.pointers (by simp)
    have unit := ((holds_cons ..).mp known.fields).1
    exact (applyTable cert known.atPc (by
      simp only [holds_cons,holds_nil,and_true]; exact ⟨rfl,base.2.1,base.2.2,pointers.2.1,unit⟩) path).2
  case scan j c =>
    change 0<d ∧ d≤9 ∧ pairs d≤256 ∧ j<pairs d ∧ c≤j at bits
    have out := applyTable (children_next ⟨pairs d+j,by omega⟩) known.atPc more path
    rcases edge with rfl|rfl <;> simpa only [detail,Nat.add_assoc] using out.2
  case scanGuard k c =>
    obtain rfl := edge
    split <;> try trivial
    exact guard_children _ _ _ _ known.atPc more path
  case collected n =>
    obtain rfl := edge
    split <;> try trivial
    rename_i nonempty
    let q : Fin 9 := ⟨d-1,by omega⟩
    have eq : q.val+1=d := by dsimp [q]; omega
    have base : Common d s := known.base
    have out := emit_width q s t coins known.atPc base.1 (by rw [eq]; exact base.2.1) ext.frozen path
      (by simpa only [ite_eq_right nonempty,pc] using matched.atPc)
    simpa only [detail,eq] using out
  case emit n j =>
    obtain rfl := edge
    exact (HonestCapMetadata.frame _ _ (registered _ live) _ _ _ known.atPc path .x23
      (by change _∈HonestCapMetadata.kept 1512; decide)).trans more
  case emitGuard n k =>
    obtain rfl := edge
    split <;> try trivial
    exact (HonestCapMetadata.frame _ _ (registered _ live) _ _ _ known.atPc path .x23
      (by change _∈HonestCapMetadata.kept 1511; decide)).trans more
  all_goals obtain rfl := edge; split <;> trivial

theorem paid {v : Node} {s t : MachineState} {coins : Bool} (known : Matches v s)
    (ext : Extra v s) (more : detail v.depth v.phase s) (live : v.phase≠.returned) (path : Path coins s t) :
    (t.getReg .x7).toNat=(s.getReg .x7).toNat+HonestSizeSchedule.paid v.depth v.phase := by
  have frame := HonestCapMetadata.frame _ _ (registered _ live) _ _ _ known.atPc path
  have small := ext.cursor
  obtain ⟨d,p⟩ := v
  cases p <;> first
    | (rw [frame .x7 (by simp only [pc]; decide)]; rfl)
    | contradiction | skip
  case emit n j =>
    rw [HonestCapCursor.emit s t coins known.atPc path]
    change s.getReg .x23=w (if d<8 then 48 else 32) at more
    rw [more]
    simp only [BitVec.toNat_add,HonestSizeSchedule.paid,HonestSizeSchedule.width,show (192:Word).toNat=192 from rfl]
    split <;> simp only [show (w 32).toNat=32 from rfl,show (w 48).toNat=48 from rfl] <;> omega
  case flush n j =>
    rw [HonestCapCursor.flush s t coins known.atPc path]
    simp only [BitVec.toNat_add,HonestSizeSchedule.paid,show (31:Word).toNat=31 from rfl]
    omega

end CommitGolfCandidate.Reconstruction.HonestSizeCursor
