import CommitGolfCandidate.ReconstructedHonestCapTables
import CommitGolfCandidate.ReconstructedHonestCapGuards
import CommitGolfCandidate.ReconstructedHonestCapPrices
import CommitGolfCandidate.ReconstructedHonestCapPlan

namespace CommitGolfCandidate.Reconstruction.HonestCapState
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 HonestCapStages HonestCapTables HonestCapPlan HonestCuts
open CommitBlocks (addr)

abbrev image := Artifact.submission.image .opening
abbrev Path (coins : Bool) := Reaches image coins stops
abbrev W := BitVec.ofNat 64

def Common (d : Nat) (s : MachineState) := s.getReg .x8 = sp ∧ s.getReg .x10 = W d ∧ s.getReg .x11 = 1

def core (d : Nat) : Phase → MachineState → Prop
  | .enter, s => s.getReg .x8 = sp
  | .returned, _ => True
  | _, s => Common d s

def scanIndex (d j : Nat) := W (2*(pairs d+j))
def scanFacts (d j p : Nat) : Facts := [(.x26,2),(.x20,W p),(.x21,scanIndex d j),(.x22,W (4*pairs d))]
def emitFacts (n j : Nat) : Facts := [(.x20,W n),(.x24,addrSlot j),(.x25,addrSlot n)]
def groupFacts (n j : Nat) : Facts := [(.x26,2),(.x20,W n),(.x21,W (4*j)),(.x24,W (n-4*j))]

def localFacts (d : Nat) : Phase → Facts
  | .enter | .returned => []
  | .level | .finish => [(.x26,2)]
  | .scan j p | .scanGuard j p => scanFacts d j p
  | .collected n => [(.x26,2),(.x20,W n)]
  | .lowDone n => [(.x20,W n)]
  | .emit n j | .emitGuard n j => emitFacts n j
  | .group n j | .flush n j => groupFacts n j
  | .inner n j r | .digitGuard n j r => (.x30,0-W r)::groupFacts n j
  | .groupGuard n k => [(.x26,2),(.x20,W n),(.x21,W (4*k))] ++
      (if 4*k<n then [(.x24,W (n-4*k))] else [])

structure Matches (v : Node) (s : MachineState) : Prop where
  atPc : s.pc = addr (pc v.phase)
  base : core v.depth v.phase s
  fields : holds s (localFacts v.depth v.phase)

theorem registered (p : Phase) (live : p ≠ .returned) : (pc p,fee p) ∈ HonestCapFrame.prices := by
  cases p <;> first | contradiction | (simp only [pc,fee]; decide)

theorem frame {v : Node} (s t : MachineState) (coins : Bool) (known : Matches v s)
    (live : v.phase ≠ .returned) (path : Path coins s t) :
    ∀ r ∈ HonestCapFrame.registers (pc v.phase), t.getReg r = s.getReg r :=
  HonestCapFrame.frame _ _ (registered _ live) s t coins known.atPc path

private theorem common_regs (p : Phase) (enter : p ≠ .enter) (finish : p ≠ .finish) (live : p ≠ .returned) :
    .x8 ∈ HonestCapFrame.registers (pc p) ∧ .x10 ∈ HonestCapFrame.registers (pc p) ∧
      .x11 ∈ HonestCapFrame.registers (pc p) := by
  cases p <;> first | contradiction | (simp only [pc]; decide)

theorem common_next {d : Nat} {p : Phase} (s t : MachineState) (coins : Bool) (known : Matches ⟨d,p⟩ s)
    (enter : p ≠ .enter) (finish : p ≠ .finish) (live : p ≠ .returned) (path : Path coins s t) : Common d t := by
  have f := frame s t coins known live path
  have base : Common d s := by
    have b := known.base
    cases p <;> first | contradiction | exact b
  obtain ⟨a,b,c⟩ := common_regs p enter finish live
  exact ⟨(f _ a).trans base.1,(f _ b).trans base.2.1,(f _ c).trans base.2.2⟩

/-- Any certified singleton table entry can be read as a statement about the
concrete final PC and listed values. -/
theorem applyTable {start cost : Nat} {input : Facts} {tracked : List Reg} {output : Choice}
    (cert : checked start input tracked [output] cost = true)
    {s t : MachineState} {coins : Bool} (pc0 : s.pc = addr start)
    (given : holds s input) (walk : Path coins s t) : t.pc = addr output.1 ∧ holds t output.2 :=
  transfer_single _ _ _ _ _ _ cert s t coins pc0 given walk

private theorem positive_depth (d : Nat) (p : Phase) (live : p ≠ .returned) (ok : legal ⟨d,p⟩) :
    0 < d ∧ d ≤ 9 := by simpa only [legal,live,ite_false] using ok.1

theorem bounds {d : Nat} {p : Phase} (live : p ≠ .returned) (ok : legal ⟨d,p⟩) :
    0 < d ∧ d ≤ 9 ∧ pairs d ≤ 256 ∧ allowed d p := by
  have h := positive_depth d p live ok
  exact ⟨h.1,h.2,width_bound d h.2,ok.2⟩

theorem powers (d : Nat) (pos : 0 < d) : 2^d=2*pairs d ∧ 2^(d+1)=4*pairs d := by
  cases d with
  | zero => contradiction
  | succ d => simp [pairs,Nat.pow_succ]; omega

theorem unsigned {n m : Nat} (a : n < 2^64) (b : m < 2^64) :
    (W n).ult (W m) = decide (n < m) := by
  simp only [W,BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt a,Nat.mod_eq_of_lt b]

theorem slots {n j : Nat} (a : n ≤ 256) (b : j ≤ 256) : addrSlot j = addrSlot n ↔ j=n := by
  constructor
  · intro he; have h := congrArg BitVec.toNat he
    change (scratch+4*j)%2^64 = (scratch+4*n)%2^64 at h
    unfold scratch at h
    omega
  · rintro rfl; rfl

end CommitGolfCandidate.Reconstruction.HonestCapState
