import CommitGolfCandidate.ReconstructedHonestCapRam

namespace CommitGolfCandidate.Reconstruction.HonestCapMetadata
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 HonestCapPlan HonestCapStages HonestCapTables
open HonestCapState (Path Matches applyTable)
open CommitBlocks (addr)

set_option maxRecDepth 32768
attribute [local irreducible] ArtifactEncoding.decode

def kept (idx : Nat) : List Reg :=
  [.x2] ++ (if idx=1429 then [] else [.x9,.x13,.x17]) ++
    (if idx=1512 ∨ idx=1626 then [] else [.x7]) ++
    (if idx=1512 ∨ idx=1511 then [.x23] else [])

theorem frame (idx fee : Nat) (hit : (idx,fee)∈HonestCapFrame.prices) (s t : MachineState) (coins : Bool)
    (pc : s.pc=addr idx) (walk : Path coins s t) : ∀ r∈kept idx, t.getReg r=s.getReg r := by
  have table : ∀ p∈HonestCapFrame.prices, HonestFrame.check Artifact.openingCode stops (kept p.1) p.2 (addr p.1)=true := by
    intro p hit
    simp only [HonestCapFrame.prices,List.mem_cons,List.not_mem_nil,or_false] at hit
    rcases hit with h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> cases h <;> decide +kernel
  exact HonestFrame.sound Artifact.openingCode _ (Eq.refl (ArtifactEncoding.decode 32 _)) (by decide) stops _
    _ _ (table _ hit) coins s t pc walk

def Pointers (s : MachineState) := s.getReg .x9=w scratch ∧ s.getReg .x13=w HonestCapRam.activeBase ∧
  s.getReg .x17=w HonestRecordMemory.proofBase

theorem init_pointers (s t : MachineState) (coins : Bool) (pc0 : s.pc=addr 1429)
    (framePtr : s.getReg .x8=sp) (walk : Path coins s t) : Pointers t := by
  have c : checked 1429 [(.x0,0),(.x8,sp)] [.x0,.x8,.x9,.x13,.x14,.x17]
      [(1451,[(.x9,w scratch),(.x13,w HonestCapRam.activeBase),(.x17,w HonestRecordMemory.proofBase)])] 19=true :=
    by decide +kernel
  have out := applyTable c pc0 (by simp only [holds_cons,holds_nil,and_true]; exact ⟨rfl,framePtr⟩) walk
  simpa only [holds_cons,holds_nil,and_true,Pointers] using out.2

def scanPtr (d j : Nat) := w (HonestCapRam.activeBase+pairs d+j)

theorem pair_start (d : Fin 9) : checked 1451
    [(.x0,0),(.x10,w (d.val+1)),(.x11,1),(.x13,w HonestCapRam.activeBase),(.x26,2)]
    [.x0,.x10,.x11,.x13,.x21,.x22,.x24,.x26] [(1470,[(.x24,scanPtr (d.val+1) 0)])] 14=true := by
  exact (by decide +kernel : ∀ k : Fin 9, checked 1451
    [(.x0,0),(.x10,w (k.val+1)),(.x11,1),(.x13,w HonestCapRam.activeBase),(.x26,2)]
    [.x0,.x10,.x11,.x13,.x21,.x22,.x24,.x26] [(1470,[(.x24,scanPtr (k.val+1) 0)])] 14=true) d

theorem pair_next (k : Fin 512) : checked 1470 [(.x24,w (HonestCapRam.activeBase+k.val))]
    [.x24] [(1469,[(.x24,w (HonestCapRam.activeBase+(k.val+1)))])] 17=true := by
  exact (by decide +kernel : ∀ j : Fin 512, checked 1470 [(.x24,w (HonestCapRam.activeBase+j.val))]
    [.x24] [(1469,[(.x24,w (HonestCapRam.activeBase+(j.val+1)))])] 17=true) k

end CommitGolfCandidate.Reconstruction.HonestCapMetadata
