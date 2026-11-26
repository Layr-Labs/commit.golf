import CommitGolfCandidate.ReconstructedHonestCapState

namespace CommitGolfCandidate.Reconstruction.HonestScanBytes
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp HonestCapStages HonestCapState
open HonestCapTables (scratch w)
open CommitBlocks (addr)

set_option maxRecDepth 32768
set_option maxHeartbeats 40000000
attribute [local irreducible] ArtifactEncoding.decode

def countInput (p : Nat) (l r : Bool) : Facts := [(.x0,0),(.x14,w l.toNat),(.x15,w r.toNat),(.x20,w p)]
def countNext (p : Nat) (l r : Bool) : Facts := [(.x20,w (p+(l != r).toNat))]

theorem count_table (p : Fin 257) (l r : Bool) : checked 1475 (countInput p.val l r)
    [.x0,.x14,.x15,.x20] [(1469,countNext p.val l r)] 15=true := by
  exact (by decide +kernel : ∀ j : Fin 257, ∀ u v : Bool, checked 1475 (countInput j.val u v)
    [.x0,.x14,.x15,.x20] [(1469,countNext j.val u v)] 15=true) p l r

end CommitGolfCandidate.Reconstruction.HonestScanBytes
