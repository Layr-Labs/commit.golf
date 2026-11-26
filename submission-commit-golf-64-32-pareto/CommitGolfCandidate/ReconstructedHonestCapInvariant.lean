import CommitGolfCandidate.ReconstructedHonestCapMetadata
import CommitGolfCandidate.ReconstructedHonestCapGrowth
import CommitGolfCandidate.ReconstructedHonestCapCursor
import CommitGolfCandidate.ReconstructedHonestCapExecution
import CommitGolfCandidate.ReconstructedHonestBudget

namespace CommitGolfCandidate.Reconstruction.HonestCapInvariant
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open HonestCapState HonestCapPlan HonestCapMetadata HonestCapRam HonestCapStages HonestCapTables
open HonestProtected HonestRanges HonestCapGrowth
open HonestRecordMemory (constant context)
open CommitBlocks (addr)

set_option maxRecDepth 32768
attribute [local irreducible] ArtifactEncoding.decode

def auxiliary (d : Nat) (p : Phase) (s : MachineState) : Prop := match p with
  | .scan k _ | .scanGuard k _ => s.getReg .x24=scanPtr d k
  | .emit .. | .emitGuard .. => (s.getReg .x23).toNat≤64
  | _ => True

structure ExtraAt (limit : Nat) (v : Node) (s : MachineState) : Prop where
  stack : s.getReg .x2 = 68719474016
  frozen : Frozen s
  cursor : (s.getReg .x7).toNat+remaining v≤limit
  pointers : v.phase≠.enter → Pointers s
  state : auxiliary v.depth v.phase s

abbrev Extra := ExtraAt 600000

private theorem regFrame {v : Node} {s t : MachineState} {coins : Bool} (known : Matches v s)
    (live : v.phase≠.returned) (path : Path coins s t) : ∀ r∈kept (pc v.phase), t.getReg r=s.getReg r :=
  HonestCapMetadata.frame _ _ (registered _ live) s t coins known.atPc path

theorem needingWide {limit : Nat} (limitOk : limit≤70000000000) {v : Node} {s : MachineState} (ok : legal v) (live : v.phase≠.returned)
    (known : Matches v s) (extra : ExtraAt limit v s) : RegFacts.hold s (needed (pc v.phase)) := by
  rcases v with ⟨d,p⟩
  cases p <;> try (solve | intro r val h; cases h)
  case scan j c =>
    obtain ⟨_,_,width,allowed⟩ := bounds live ok
    change j<pairs d ∧ c≤j at allowed
    have ptr := extra.pointers (by simp)
    have count := known.fields
    simp only [localFacts,scanFacts,holds_cons,holds_nil,and_true] at count
    intro r val member
    change (r,val) ∈ [(Reg.x24,⟨activeBase,activeBase+1024⟩),(.x20,⟨0,256⟩),(.x9,constant scratch)] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h|h|h <;> cases h
    · have x : s.getReg .x24=scanPtr d j := extra.state
      rw [x]; simp only [Contains,scanPtr,w,BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by dsimp [activeBase] at *; omega)]; omega
    · rw [count.2.1]; simp only [Contains,W,BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    · rw [ptr.1]; exact precise _
  all_goals
    have ptr := extra.pointers (by simp)
    intro r val member
    change (r,val)∈[(Reg.x7,⟨0,70000000000⟩),(.x17,constant HonestRecordMemory.proofBase)] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h|h <;> cases h
    · exact ⟨Nat.zero_le _,((Nat.le_add_right _ _).trans extra.cursor).trans limitOk⟩
    · rw [ptr.2.2]; exact precise _

theorem needing {v : Node} {s : MachineState} (ok : legal v) (live : v.phase≠.returned)
    (known : Matches v s) (extra : Extra v s) : RegFacts.hold s (needed (pc v.phase)) :=
  needingWide (by decide : 600000≤70000000000) ok live known extra

private theorem pastPointers (p : Phase) (start : p≠.enter) :
    .x9∈kept (pc p) ∧ .x13∈kept (pc p) ∧ .x17∈kept (pc p) := by
  cases p <;> first | contradiction | (simp only [pc]; decide)

private theorem ptrAfter {limit : Nat} {v : Node} {s t : MachineState} {coins : Bool} (known : Matches v s) (ext : ExtraAt limit v s)
    (live : v.phase≠.returned) (path : Path coins s t) : Pointers t := by
  by_cases entry : v.phase=.enter
  · have p0 := known.atPc; rw [entry] at p0
    have fp := known.base; rw [entry] at fp
    exact init_pointers s t coins p0 fp path
  · have old := ext.pointers entry
    have frame := regFrame known live path
    obtain ⟨a,b,c⟩ := pastPointers _ entry
    exact ⟨(frame _ a).trans old.1,(frame _ b).trans old.2.1,(frame _ c).trans old.2.2⟩

private theorem cursorAfter {limit : Nat} {v : Node} {s t : MachineState} {coins : Bool} (known : Matches v s)
    (ext : ExtraAt limit v s) (live : v.phase≠.returned) (path : Path coins s t) :
    (t.getReg .x7).toNat≤(s.getReg .x7).toNat+delta v.phase := by
  have frame := regFrame known live path
  rcases v with ⟨d,p⟩
  cases p <;> first
    | (rw [frame .x7 (by simp only [pc]; decide)]; exact Nat.le_add_right _ _)
    | contradiction | skip
  case emit n j =>
    rw [HonestCapCursor.emit s t coins known.atPc path]
    have small : (s.getReg .x23).toNat≤64 := ext.state
    simp only [BitVec.toNat_add,delta,show (192:Word).toNat=192 from rfl]
    omega
  case flush n j =>
    rw [HonestCapCursor.flush s t coins known.atPc path]
    simp only [BitVec.toNat_add,delta,show (31:Word).toNat=31 from rfl]
    exact Nat.mod_le _ _

private theorem auxAfter {limit : Nat} {v w' : Node} {s t : MachineState} {coins : Bool} (ok : legal v)
    (known : Matches v s) (ext : ExtraAt limit v s) (live : v.phase≠.returned) (path : Path coins s t)
    (edge : w'∈next v.depth v.phase) (matched : Matches w' t) :
    auxiliary w'.depth w'.phase t := by
  obtain ⟨d,p⟩ := v
  have bits := bounds live ok
  cases p <;> simp only [next,List.mem_cons,List.not_mem_nil,or_false] at edge
  all_goals try (obtain rfl := edge; trivial)
  case level =>
    obtain rfl := edge
    let q : Fin 9 := ⟨d-1,by omega⟩
    have eq : q.val+1=d := by dsimp [q]; omega
    have cert := pair_start q
    rw [eq] at cert
    have base : Common d s := known.base
    have pointers := ext.pointers (by simp)
    have unit := ((holds_cons ..).mp known.fields).1
    have out := applyTable cert known.atPc (by
      simp only [holds_cons,holds_nil,and_true]; exact ⟨rfl,base.2.1,base.2.2,pointers.2.1,unit⟩) path
    exact ((holds_cons ..).mp out.2).1
  case scan j c =>
    change 0<d ∧ d≤9 ∧ pairs d≤256 ∧ j<pairs d ∧ c≤j at bits
    have src : s.getReg .x24=scanPtr d j := ext.state
    have out := applyTable (pair_next ⟨pairs d+j,by omega⟩) known.atPc (by
      simp only [holds_cons,holds_nil,and_true]
      simpa only [scanPtr,Nat.add_assoc] using src) path
    have endReg := ((holds_cons ..).mp out.2).1
    rcases edge with rfl|rfl <;> simpa only [auxiliary,scanPtr,Nat.add_assoc] using endReg
  case scanGuard k c =>
    obtain rfl := edge
    split <;> try trivial
    have held := HonestCapState.frame s t coins known live path .x24 (by change _∈HonestCapFrame.registers 1469; decide)
    exact held.trans ext.state
  case collected n =>
    obtain rfl := edge
    split <;> try trivial
    rename_i nonempty
    let q : Fin 9 := ⟨d-1,by omega⟩
    have eq : q.val+1=d := by dsimp [q]; omega
    have base : Common d s := known.base
    apply HonestCapRam.width q s t coins known.atPc base.1 (by rw [eq]; exact base.2.1) ext.frozen path
    simpa only [ite_eq_right nonempty,pc] using matched.atPc
  case emit n j =>
    obtain rfl := edge
    have held := regFrame known live path .x23 (by change _∈kept 1512; decide)
    change (t.getReg .x23).toNat≤64
    rw [held]; exact ext.state
  case emitGuard n k =>
    obtain rfl := edge
    split <;> try trivial
    have held := regFrame known live path .x23 (by change _∈kept 1511; decide)
    change (t.getReg .x23).toNat≤64
    rw [held]; exact ext.state
  all_goals obtain rfl := edge; split <;> trivial

theorem maintainedWide {limit : Nat} (limitOk : limit≤70000000000) (v w' : Node) (s t : MachineState) {coins : Bool} (ok : legal v)
    (live : v.phase≠.returned) (known : Matches v s) (ext : ExtraAt limit v s) (path : Path coins s t)
    (edge : w'∈next v.depth v.phase) (matched : Matches w' t) : ExtraAt limit w' t := by
  have stackMem (p : Phase) : .x2∈kept (pc p) := by cases p <;> simp only [pc] <;> decide
  have frozen := preserved _ _ (registered _ live) s t coins known.atPc ext.frozen (needingWide limitOk ok live known ext) path
  have moved := cursorAfter known ext live path
  have paid := spent v w' ok edge
  exact ⟨(regFrame known live path _ (stackMem _)).trans ext.stack,frozen,
    by have := ext.cursor; omega,fun _ => ptrAfter known ext live path,auxAfter ok known ext live path edge matched⟩

theorem maintained (v w' : Node) (s t : MachineState) {coins : Bool} (ok : legal v)
    (live : v.phase≠.returned) (known : Matches v s) (ext : Extra v s) (path : Path coins s t)
    (edge : w'∈next v.depth v.phase) (matched : Matches w' t) : Extra w' t :=
  maintainedWide (by decide : 600000≤70000000000) _ _ _ _ ok live known ext path edge matched

end CommitGolfCandidate.Reconstruction.HonestCapInvariant
