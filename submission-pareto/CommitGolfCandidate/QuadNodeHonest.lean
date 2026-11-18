import CommitGolfCandidate.QuadNodeSemantic
import CommitGolfCandidate.QuadCheckRecordData

namespace TwoPermutationPrototype.Quad.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

private theorem quad_child_cases (slot k : Fin 4) :
    k=slot ∨ k=⟨(slot.val+0+1)%4,Nat.mod_lt _ (by decide)⟩ ∨
    k=⟨(slot.val+1+1)%4,Nat.mod_lt _ (by decide)⟩ ∨
    k=⟨(slot.val+2+1)%4,Nat.mod_lt _ (by decide)⟩ := by
  fin_cases slot <;> fin_cases k <;> decide

theorem quad_opened_leaf (leaves : DigestTape) (index : Index) :
    quadLeaf leaves index ⟨index.val%4,Nat.mod_lt _ (by decide)⟩=leaves index := by
  unfold quadLeaf
  congr 1
  apply Fin.ext
  dsimp only [Fin.val_mk]
  omega

/-- Actual prepared children agree with the honest shared leaves when the four
loaded digest values do; no abstract checker is substituted for the machine. -/
theorem quad_workspace_honest (s : MachineState) (index : Index) (proof : Nat)
    (ready : QuadNodeReady s ⟨index.val%4,Nat.mod_lt _ (by decide)⟩ proof)
    (leaves : DigestTape) (opened : readBuffer s 12288 32=leaves index)
    (siblings : ∀ j<3, readBuffer s (proof+32*j) 32=quadLeaf leaves index (quadRotSlot index j)) :
    workspaceChildren (quadWorkspace s)=quadLeaf leaves index := by
  let slot : Fin 4 := ⟨index.val%4,Nat.mod_lt _ (by decide)⟩
  have atOpened : workspaceChildren (quadWorkspace s) slot=quadLeaf leaves index slot :=
    (quad_workspace_input s slot proof ready.pair ready.digest ready.opened ready.source ready.room ready.even ready.above).2.trans
      (opened.trans (quad_opened_leaf leaves index).symm)
  have atOther (j : Nat) (small : j<3) :
      workspaceChildren (quadWorkspace s) (quadRotSlot index j)=quadLeaf leaves index (quadRotSlot index j) :=
    (quad_workspace_siblings s slot proof ready.pair ready.digest ready.opened ready.source ready.room ready.even ready.above j small).trans
      (siblings j small)
  funext k
  rcases quad_child_cases slot k with h | h | h | h
  · exact h.symm ▸ atOpened
  · exact h.symm ▸ atOther 0 (by decide)
  · exact h.symm ▸ atOther 1 (by decide)
  · exact h.symm ▸ atOther 2 (by decide)

theorem quad_group_children (leaves : DigestTape) (index : Index) :
    quadGroupLeaves leaves (index.val/4)=quadLeaf leaves index := by
  funext k
  have bounded : 4*(index.val/4)+k.val<LENGTH := by
    have indexBound := index.isLt
    have slotBound := k.isLt
    change index.val<16777216 at indexBound
    change 4*(index.val/4)+k.val<16777216
    omega
  rw [quadGroupLeaves,dif_pos bounded]
  rfl

/-- The honest low-256-bit quad result is exactly the first node of the
fourteen-level shared heap path. -/
theorem quad_honest_start (oracle : Oracle) (leaves : DigestTape) (index : Index) :
    (oracle.permutation (quadInput (quadLeaf leaves index))).extractLsb' 0 256=
      quadHeap oracle.compression (quadFunction oracle.permutation) leaves ((LENGTH+index.val)/4) := by
  have node : (LENGTH+index.val)/4=LENGTH/4+index.val/4 := by
    change (16777216+index.val)/4=4194304+index.val/4
    omega
  have inside : index.val/4<LENGTH/4 := by
    have := index.isLt
    change index.val<16777216 at this
    change index.val/4<4194304
    omega
  rw [node,quad_heap_node _ _ _ _ inside,quad_group_children]
  rfl

end TwoPermutationPrototype.Quad.Checker
