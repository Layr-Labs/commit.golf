import CommitGolfCandidate.ReconstructedHonestCapMetadata
import CommitGolfCandidate.ReconstructedHonestSizeSchedule

namespace CommitGolfCandidate.Reconstruction.HonestCapOperands
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 HonestCapPlan HonestCapStages HonestCapTables
open HonestCapState (Path Matches applyTable)
open HonestCapRam (activeBase Frozen widthInput)
open HonestRanges HonestRegionStep HonestProtected
open HonestRecordMemory (context constant)
open CommitBlocks (addr)

set_option maxRecDepth 32768
set_option maxHeartbeats 50000000
attribute [local irreducible] ArtifactEncoding.decode

def left (k : Nat) := w (activeBase+2*k)
def right (k : Nat) := w (activeBase+2*k+1)
def children (k : Nat) : Facts := [(.x23,left k),(.x16,right k)]

theorem children_start (d : Fin 9) : checked 1451
    [(.x0,0),(.x10,w (d.val+1)),(.x11,1),(.x13,w activeBase),(.x26,2)]
    [.x0,.x10,.x11,.x13,.x14,.x16,.x21,.x22,.x23,.x24,.x26] [(1470,children (pairs (d.val+1)))] 14=true := by
  exact (by decide +kernel : ∀ k : Fin 9, checked 1451
    [(.x0,0),(.x10,w (k.val+1)),(.x11,1),(.x13,w activeBase),(.x26,2)]
    [.x0,.x10,.x11,.x13,.x14,.x16,.x21,.x22,.x23,.x24,.x26] [(1470,children (pairs (k.val+1)))] 14=true) d

theorem children_next (k : Fin 512) : checked 1470 (children k.val) [.x16,.x23]
    [(1469,children (k.val+1))] 17=true := by
  exact (by decide +kernel : ∀ j : Fin 512, checked 1470 (children j.val) [.x16,.x23]
    [(1469,children (j.val+1))] 17=true) k

theorem guard_children (k : Nat) (s t : MachineState) (coins : Bool) (pc0 : s.pc=addr 1469)
    (start : holds s (children k)) (path : Path coins s t) : holds t (children k) := by
  have held := HonestFrame.sound Artifact.openingCode (Artifact.submission.image .opening)
    (Eq.refl (ArtifactEncoding.decode 32 _)) (by decide) stops [.x23,.x16] 1 (addr 1469) (by decide +kernel)
    coins s t pc0 path
  simp only [children,holds_cons,holds_nil,and_true] at start ⊢
  exact ⟨(held _ (by simp)).trans start.1,(held _ (by simp)).trans start.2⟩

def widthOutput (d : Nat) (pc : Word) : Option Shape :=
  if pc=addr 1512 then some ⟨[(.x23,constant (if d<8 then 48 else 32))],[]⟩ else some ⟨[],[]⟩

private theorem width_table (d : Fin 9) : HonestRegionBlocks.check context Artifact.openingCode
    HonestCapStages.stops (widthOutput (d.val+1)) 26 (addr 1483) ((widthInput (d.val+1)).model context) = true := by
  exact (by decide +kernel : ∀ i : Fin 9, HonestRegionBlocks.check context Artifact.openingCode
    HonestCapStages.stops (widthOutput (i.val+1)) 26 (addr 1483) ((widthInput (i.val+1)).model context) = true) d

theorem emit_width (d : Fin 9) (s t : MachineState) (coins : Bool) (start : s.pc=addr 1483)
    (stack : s.getReg .x8=HonestCapTables.sp) (depth : s.getReg .x10=HonestCapTables.w (d.val+1))
    (old : Frozen s) (walk : Path coins s t) (ending : t.pc=addr 1512) :
    t.getReg .x23=HonestCapTables.w (if d.val+1<8 then 48 else 32) := by
  have inputs : Holds context (widthInput (d.val+1)) s := by
    refine ⟨?_,⟨(by intro q v h; cases h),old⟩⟩
    intro r v h
    simp only [widthInput,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with h|h <;> cases h
    · rw [depth]; exact precise _
    · rw [stack]; exact precise _
  obtain ⟨b,shape,held⟩ := HonestRegionBlocks.from_shape context Artifact.openingCode
    (Artifact.submission.image .opening) (Eq.refl (ArtifactEncoding.decode 32 _)) (by decide)
    HonestCapStages.stops (widthOutput (d.val+1)) _ _ _ (width_table d) s t coins start inputs walk
  simp only [widthOutput,ending,ite_true,Option.some.injEq] at shape
  subst b
  exact singleton_ok (held.1 _ _ List.mem_cons_self) (by split <;> rfl)


end CommitGolfCandidate.Reconstruction.HonestCapOperands
