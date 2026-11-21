import CommitGolfCandidate.QuadNodeBlock
import CommitGolfCandidate.TwoPermutationQuadSpec
import CommitGolfCandidate.TwoPermutationBindingLeaf
import CommitGolfCandidate.TwoPermutationHeapInvariant

/-! The actual aligned 200-byte workspace represents precisely QuadSpec.quadInput. -/
namespace TwoPermutationPrototype.Quad.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

/-- Four children as present in the actual workspace, in slot order. -/
def workspaceChildren (s : MachineState) : Fin 4 → BitVec 256 :=
  fun k => readBuffer s (12872+32*k.val) 32

/-- Word representation of the shared quad input, low word first. -/
def quadInputWords (c : Fin 4 → BitVec 256) (i : Fin 25) : Word :=
  if h : i.val<9 then 0 else
    (c ⟨(i.val-9)/4,by have := i.isLt; omega⟩).extractLsb' (64*((i.val-9)%4)) 64

theorem quad_input_word (c : Fin 4 → BitVec 256) (i : Fin 25) :
    (quadInput c).extractLsb' (64*i.val) 64=quadInputWords c i := by
  fin_cases i
  · exact (BitVec.extractLsb'_append_eq_of_add_le (xhi := (((c 3 ++ c 2) ++ c 1) ++ c 0)) (xlo := (0#576))
        (start := 0) (len := 64) (by decide)).trans BitVec.extractLsb'_zero
  · exact (BitVec.extractLsb'_append_eq_of_add_le (xhi := (((c 3 ++ c 2) ++ c 1) ++ c 0)) (xlo := (0#576))
        (start := 64) (len := 64) (by decide)).trans BitVec.extractLsb'_zero
  · exact (BitVec.extractLsb'_append_eq_of_add_le (xhi := (((c 3 ++ c 2) ++ c 1) ++ c 0)) (xlo := (0#576))
        (start := 128) (len := 64) (by decide)).trans BitVec.extractLsb'_zero
  · exact (BitVec.extractLsb'_append_eq_of_add_le (xhi := (((c 3 ++ c 2) ++ c 1) ++ c 0)) (xlo := (0#576))
        (start := 192) (len := 64) (by decide)).trans BitVec.extractLsb'_zero
  · exact (BitVec.extractLsb'_append_eq_of_add_le (xhi := (((c 3 ++ c 2) ++ c 1) ++ c 0)) (xlo := (0#576))
        (start := 256) (len := 64) (by decide)).trans BitVec.extractLsb'_zero
  · exact (BitVec.extractLsb'_append_eq_of_add_le (xhi := (((c 3 ++ c 2) ++ c 1) ++ c 0)) (xlo := (0#576))
        (start := 320) (len := 64) (by decide)).trans BitVec.extractLsb'_zero
  · exact (BitVec.extractLsb'_append_eq_of_add_le (xhi := (((c 3 ++ c 2) ++ c 1) ++ c 0)) (xlo := (0#576))
        (start := 384) (len := 64) (by decide)).trans BitVec.extractLsb'_zero
  · exact (BitVec.extractLsb'_append_eq_of_add_le (xhi := (((c 3 ++ c 2) ++ c 1) ++ c 0)) (xlo := (0#576))
        (start := 448) (len := 64) (by decide)).trans BitVec.extractLsb'_zero
  · exact (BitVec.extractLsb'_append_eq_of_add_le (xhi := (((c 3 ++ c 2) ++ c 1) ++ c 0)) (xlo := (0#576))
        (start := 512) (len := 64) (by decide)).trans BitVec.extractLsb'_zero
  · exact (BitVec.extractLsb'_append_eq_of_le (xhi := (((c 3 ++ c 2) ++ c 1) ++ c 0)) (xlo := (0#576))
        (start := 576) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_add_le (xhi := ((c 3 ++ c 2) ++ c 1)) (xlo := c 0)
        (start := 0) (len := 64) (by decide)))
  · exact (BitVec.extractLsb'_append_eq_of_le (xhi := (((c 3 ++ c 2) ++ c 1) ++ c 0)) (xlo := (0#576))
        (start := 640) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_add_le (xhi := ((c 3 ++ c 2) ++ c 1)) (xlo := c 0)
        (start := 64) (len := 64) (by decide)))
  · exact (BitVec.extractLsb'_append_eq_of_le (xhi := (((c 3 ++ c 2) ++ c 1) ++ c 0)) (xlo := (0#576))
        (start := 704) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_add_le (xhi := ((c 3 ++ c 2) ++ c 1)) (xlo := c 0)
        (start := 128) (len := 64) (by decide)))
  · exact (BitVec.extractLsb'_append_eq_of_le (xhi := (((c 3 ++ c 2) ++ c 1) ++ c 0)) (xlo := (0#576))
        (start := 768) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_add_le (xhi := ((c 3 ++ c 2) ++ c 1)) (xlo := c 0)
        (start := 192) (len := 64) (by decide)))
  · exact (BitVec.extractLsb'_append_eq_of_le (xhi := (((c 3 ++ c 2) ++ c 1) ++ c 0)) (xlo := (0#576))
        (start := 832) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := ((c 3 ++ c 2) ++ c 1)) (xlo := c 0)
        (start := 256) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_add_le (xhi := (c 3 ++ c 2)) (xlo := c 1)
        (start := 0) (len := 64) (by decide))))
  · exact (BitVec.extractLsb'_append_eq_of_le (xhi := (((c 3 ++ c 2) ++ c 1) ++ c 0)) (xlo := (0#576))
        (start := 896) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := ((c 3 ++ c 2) ++ c 1)) (xlo := c 0)
        (start := 320) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_add_le (xhi := (c 3 ++ c 2)) (xlo := c 1)
        (start := 64) (len := 64) (by decide))))
  · exact (BitVec.extractLsb'_append_eq_of_le (xhi := (((c 3 ++ c 2) ++ c 1) ++ c 0)) (xlo := (0#576))
        (start := 960) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := ((c 3 ++ c 2) ++ c 1)) (xlo := c 0)
        (start := 384) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_add_le (xhi := (c 3 ++ c 2)) (xlo := c 1)
        (start := 128) (len := 64) (by decide))))
  · exact (BitVec.extractLsb'_append_eq_of_le (xhi := (((c 3 ++ c 2) ++ c 1) ++ c 0)) (xlo := (0#576))
        (start := 1024) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := ((c 3 ++ c 2) ++ c 1)) (xlo := c 0)
        (start := 448) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_add_le (xhi := (c 3 ++ c 2)) (xlo := c 1)
        (start := 192) (len := 64) (by decide))))
  · exact (BitVec.extractLsb'_append_eq_of_le (xhi := (((c 3 ++ c 2) ++ c 1) ++ c 0)) (xlo := (0#576))
        (start := 1088) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := ((c 3 ++ c 2) ++ c 1)) (xlo := c 0)
        (start := 512) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := (c 3 ++ c 2)) (xlo := c 1)
        (start := 256) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_add_le (xhi := c 3) (xlo := c 2)
        (start := 0) (len := 64) (by decide)))))
  · exact (BitVec.extractLsb'_append_eq_of_le (xhi := (((c 3 ++ c 2) ++ c 1) ++ c 0)) (xlo := (0#576))
        (start := 1152) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := ((c 3 ++ c 2) ++ c 1)) (xlo := c 0)
        (start := 576) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := (c 3 ++ c 2)) (xlo := c 1)
        (start := 320) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_add_le (xhi := c 3) (xlo := c 2)
        (start := 64) (len := 64) (by decide)))))
  · exact (BitVec.extractLsb'_append_eq_of_le (xhi := (((c 3 ++ c 2) ++ c 1) ++ c 0)) (xlo := (0#576))
        (start := 1216) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := ((c 3 ++ c 2) ++ c 1)) (xlo := c 0)
        (start := 640) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := (c 3 ++ c 2)) (xlo := c 1)
        (start := 384) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_add_le (xhi := c 3) (xlo := c 2)
        (start := 128) (len := 64) (by decide)))))
  · exact (BitVec.extractLsb'_append_eq_of_le (xhi := (((c 3 ++ c 2) ++ c 1) ++ c 0)) (xlo := (0#576))
        (start := 1280) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := ((c 3 ++ c 2) ++ c 1)) (xlo := c 0)
        (start := 704) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := (c 3 ++ c 2)) (xlo := c 1)
        (start := 448) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_add_le (xhi := c 3) (xlo := c 2)
        (start := 192) (len := 64) (by decide)))))
  · exact (BitVec.extractLsb'_append_eq_of_le (xhi := (((c 3 ++ c 2) ++ c 1) ++ c 0)) (xlo := (0#576))
        (start := 1344) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := ((c 3 ++ c 2) ++ c 1)) (xlo := c 0)
        (start := 768) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := (c 3 ++ c 2)) (xlo := c 1)
        (start := 512) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := c 3) (xlo := c 2)
        (start := 256) (len := 64) (by decide)))))
  · exact (BitVec.extractLsb'_append_eq_of_le (xhi := (((c 3 ++ c 2) ++ c 1) ++ c 0)) (xlo := (0#576))
        (start := 1408) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := ((c 3 ++ c 2) ++ c 1)) (xlo := c 0)
        (start := 832) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := (c 3 ++ c 2)) (xlo := c 1)
        (start := 576) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := c 3) (xlo := c 2)
        (start := 320) (len := 64) (by decide)))))
  · exact (BitVec.extractLsb'_append_eq_of_le (xhi := (((c 3 ++ c 2) ++ c 1) ++ c 0)) (xlo := (0#576))
        (start := 1472) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := ((c 3 ++ c 2) ++ c 1)) (xlo := c 0)
        (start := 896) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := (c 3 ++ c 2)) (xlo := c 1)
        (start := 640) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := c 3) (xlo := c 2)
        (start := 384) (len := 64) (by decide)))))
  · exact (BitVec.extractLsb'_append_eq_of_le (xhi := (((c 3 ++ c 2) ++ c 1) ++ c 0)) (xlo := (0#576))
        (start := 1536) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := ((c 3 ++ c 2) ++ c 1)) (xlo := c 0)
        (start := 960) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := (c 3 ++ c 2)) (xlo := c 1)
        (start := 704) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := c 3) (xlo := c 2)
        (start := 448) (len := 64) (by decide)))))

/-- Nine cleared words suffice; the remaining sixteen words are exactly the
four 32-byte child reads of this same machine state. -/
theorem workspace_quad_input (s : MachineState)
    (zeros : ∀ i<9, memoryView s (1600+i)=0) :
    packBuffer (window (memoryView s) 1600)=quadInput (workspaceChildren s) := by
  rw [←read_permutation_window]
  apply aligned_buffer_eq s 1600 200 (by decide)
  intro k bound
  let i : Fin 25 := ⟨k,bound⟩
  refine Eq.trans ?_ (quad_input_word (workspaceChildren s) i).symm
  change memoryView s (1600+i.val)=quadInputWords (workspaceChildren s) i
  unfold quadInputWords
  split
  · exact zeros _ (by assumption)
  · rename_i h
    rw [workspaceChildren,read_digest_word _ _ _ (by omega) (by omega)]
    dsimp only [Fin.val_mk]
    change s.getMem (wordAddress (1600+i.val))=s.getMem (BitVec.ofNat 64 _)
    congr 2
    unfold wordAddress
    congr 1
    omega

end TwoPermutationPrototype.Quad.Checker
