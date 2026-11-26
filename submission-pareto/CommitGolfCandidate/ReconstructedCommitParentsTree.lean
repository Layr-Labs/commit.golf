import CommitGolfCandidate.ReconstructedCommitParentsLevel

namespace CommitGolfCandidate.Reconstruction.CommitParents
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding CommitExact
attribute [local irreducible] readBuffer

def treeSteps : Nat → Nat
  | 0 => (Setup.ops 0).length+depthSteps 0
  | n+1 => ((Setup.ops (n+1)).length+depthSteps (n+1))+treeSteps n

theorem accumulated (o : Oracle) (leaves : Nat→Binding.Digest) (can : ∀ k, Canonical 24 (leaves k))
    (d : Nat) (hd : d<24) (s : MachineState) (pc : s.pc=CommitBlocks.addr (Setup.begin d))
    (kind : s.getReg .x5=0) (regular : d<23 → s.getReg .x11=64 ∧ s.getReg .x13=0)
    (initial : Snapshot (cell s) (node (rawC o) leaves) d (2^d)) :
    ∃ t, Segment o CommitSetup.im (treeSteps d) s t ∧ Done o leaves (0 : Fin 24) s t := by
  induction d generalizing s with
  | zero => exact depth o (0 : Fin 24) leaves can s pc kind regular initial
  | succ d ih =>
    obtain ⟨v,sg,built⟩ := depth o ⟨d+1,hd⟩ leaves can s pc kind regular initial
    have adjacency : ∀ j : Fin 23, depthEnd (j.val+1)=Setup.begin j := by decide
    have next : v.pc=CommitBlocks.addr (Setup.begin d) :=
      built.pc.trans (congrArg CommitBlocks.addr (adjacency ⟨d,by omega⟩))
    obtain ⟨t,rem,done⟩ := ih (by omega) v next built.tags.1 (fun _=>built.tags.2) (next_level built.heap)
    exact ⟨t,compose sg rem,{done with outside:=built.outside.trans done.outside}⟩

/-- The leaf stage hands control to word 53016 with its hash selector already
zero. All 24 executed level loops finish before the root copy at word 150118. -/
theorem built_tree (o : Oracle) (leaves : Nat→Binding.Digest) (can : ∀ k, Canonical 24 (leaves k))
    (s : MachineState) (pc : s.pc=CommitBlocks.addr 53016) (kind : s.getReg .x5=0)
    (initial : Snapshot (cell s) (node (rawC o) leaves) 23 (2^23)) :
    ∃ t, Segment o CommitSetup.im (treeSteps 23) s t ∧ t.pc=CommitBlocks.addr 150118 ∧
      cell t (addr 0 1)=node (rawC o) leaves 0 1 ∧
      (∀ e k, Cell e k → 0<e → cell t (addr e k)=consumed e k (node (rawC o) leaves e k)) ∧
      Outside s t ∧ t.getReg .x12=BitVec.ofNat 64 (addr 0 1) := by
  obtain ⟨t,seg,built⟩ := accumulated o leaves can 23 (by decide) s pc kind (by omega) initial
  have root := built.heap.1 0 1 (by unfold Cell;decide)
  have top : cell t (addr 0 1)=node (rawC o) leaves 0 1 := root
  refine ⟨t,seg,built.pc,top,?_,built.outside,built.output⟩
  intro e k h pos
  have bound := h.2.2
  have mem := built.heap.1 e k h
  by_cases first : e=1
  · subst e;simpa [stage,show k<4 by omega] using mem
  · simpa [stage,show 1<e by omega] using mem

end CommitGolfCandidate.Reconstruction.CommitParents
