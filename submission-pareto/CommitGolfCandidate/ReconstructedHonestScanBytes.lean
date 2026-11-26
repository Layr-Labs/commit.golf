import CommitGolfCandidate.ReconstructedHonestScanCounter
import CommitGolfCandidate.ReconstructedHonestScanPrefix

namespace CommitGolfCandidate.Reconstruction.HonestScanBytes
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp HonestCapStages HonestCapState
open HonestCapTables (scratch w)
open CommitBlocks (addr)

set_option maxRecDepth 32768
set_option maxHeartbeats 40000000
attribute [local irreducible] ArtifactEncoding.decode

/-- The actual pair scan increments the sibling count on precisely XOR, sets
the shared parent byte on OR, and leaves all other cap bytes unchanged. -/
theorem execute (s t : MachineState) (coins : Bool) (pc0 : s.pc=addr 1470) (path : Path coins s t)
    (p : Fin 257) (l r : Bool) (lo : s.getByte (s.getReg .x23)=HonestFlagState.code l)
    (hi : s.getByte (s.getReg .x16)=HonestFlagState.code r) (unit : s.getReg .x11=1)
    (count : s.getReg .x20=w p.val) (scratchPtr : s.getReg .x9=w scratch) :
    t.getReg .x20=w (p.val+(l != r).toNat) ∧ ∀ q, HonestRanges.Contains HonestCapSpan.flags q →
      t.getByte q=if (l||r) && q==s.getReg .x24 then 1 else s.getByte q := by
  let u := after s (l||r)
  obtain ⟨rest,loc⟩ := afterPath s t coins pc0 path l r lo hi
  have rg (x : Reg) : u.getReg x=(combine s).getReg x := after_reg .. 
  obtain ⟨_,ll,rr⟩ := getCombine s l r lo hi
  have ct : u.getReg .x20=w p.val := (rg _).trans count
  have ptr : u.getReg .x9=w scratch := (rg _).trans scratchPtr
  have inputs : holds u (countInput p.val l r) := by
    simp only [countInput,holds_cons,holds_nil,and_true]; exact ⟨rfl,(rg _).trans ll,(rg _).trans rr,ct⟩
  have out := applyTable (count_table p l r) loc inputs rest
  have n : (u.getReg .x20).toNat≤256 := by rw [ct,BitVec.toNat_ofNat]; have := p.isLt; omega
  have bytes := HonestCapSpan.afterStore u t coins loc n ptr rest
  exact ⟨((holds_cons ..).mp out.2).1,fun q inside => (bytes q inside).trans (after_byte s _ unit q)⟩

end CommitGolfCandidate.Reconstruction.HonestScanBytes
