import CommitGolfCandidate.QuadNodeSemantic
import CommitGolfCandidate.QuadCheckRecordData
import CommitGolfCandidate.TwoPermutationQuad3Spec

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

/-- Actual prepared children agree with any four claimed children when the
opened digest and the three rotated proof digests do. -/
theorem quad_workspace_children (s : MachineState) (slot : Fin 4) (proof : Nat)
    (ready : QuadNodeReady s slot proof) (c : Fin 4 → BitVec 256)
    (opened : readBuffer s 12288 32=c slot)
    (siblings : ∀ j<3, readBuffer s (proof+32*j) 32=c ⟨(slot.val+j+1)%4,Nat.mod_lt _ (by decide)⟩) :
    workspaceChildren (quadWorkspace s)=c := by
  have atOpened : workspaceChildren (quadWorkspace s) slot=c slot :=
    (quad_workspace_input s slot proof ready.pair ready.digest ready.opened ready.source ready.room ready.even ready.above).2.trans
      opened
  have atOther (j : Nat) (small : j<3) :
      workspaceChildren (quadWorkspace s) ⟨(slot.val+j+1)%4,Nat.mod_lt _ (by decide)⟩=
        c ⟨(slot.val+j+1)%4,Nat.mod_lt _ (by decide)⟩ :=
    (quad_workspace_siblings s slot proof ready.pair ready.digest ready.opened ready.source ready.room ready.even ready.above j small).trans
      (siblings j small)
  funext k
  rcases quad_child_cases slot k with h | h | h | h
  · exact h.symm ▸ atOpened
  · exact h.symm ▸ atOther 0 (by decide)
  · exact h.symm ▸ atOther 1 (by decide)
  · exact h.symm ▸ atOther 2 (by decide)

/-- Actual prepared children agree with the honest shared leaves when the four
loaded digest values do; no abstract checker is substituted for the machine. -/
theorem quad_workspace_honest (s : MachineState) (index : Index) (proof : Nat)
    (ready : QuadNodeReady s ⟨index.val%4,Nat.mod_lt _ (by decide)⟩ proof)
    (leaves : DigestTape) (opened : readBuffer s 12288 32=leaves index)
    (siblings : ∀ j<3, readBuffer s (proof+32*j) 32=quadLeaf leaves index (quadRotSlot index j)) :
    workspaceChildren (quadWorkspace s)=quadLeaf leaves index :=
  quad_workspace_children s _ proof ready _ (opened.trans (quad_opened_leaf leaves index).symm) siblings

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

/-- The opened quad node is slot `(index/4)%4` of its quad2 group. -/
theorem quad2_opened_child (quad : QuadFunction) (leaves : DigestTape) (index : Index) :
    quad2Group quad leaves (index.val/16) ⟨(index.val/4)%4,Nat.mod_lt _ (by decide)⟩=
      quad (quadLeaf leaves index) := by
  unfold quad2Group quadValue
  rw [show 4*(index.val/16)+(index.val/4)%4=index.val/4 by omega,quad_group_children]

/-- The three rotated quad neighbours in the record are the other quad2 children. -/
theorem quad2_neighbour_child (quad : QuadFunction) (leaves : DigestTape) (index : Index) (j : Nat) :
    quadValue quad leaves (quad2Neighbour index j)=
      quad2Group quad leaves (index.val/16) ⟨((index.val/4)%4+j+1)%4,Nat.mod_lt _ (by decide)⟩ := rfl

/-- The opened level-2 node is slot `(index/16)%4` of its level-3 group. -/
theorem quad3_opened_child (quad : QuadFunction) (leaves : DigestTape) (index : Index) :
    quad3Group quad leaves (index.val/64) ⟨(index.val/16)%4,Nat.mod_lt _ (by decide)⟩=
      quad (quad2Group quad leaves (index.val/16)) := by
  unfold quad3Group quad2Value
  rw [show 4*(index.val/64)+(index.val/16)%4=index.val/16 by omega]

/-- The three rotated level-2 neighbours in the record are the other level-3 children. -/
theorem quad3_neighbour_child (quad : QuadFunction) (leaves : DigestTape) (index : Index) (j : Nat) :
    quad2Value quad leaves (quad3Neighbour index j)=
      quad3Group quad leaves (index.val/64) ⟨((index.val/16)%4+j+1)%4,Nat.mod_lt _ (by decide)⟩ := rfl

/-- The honest low-256-bit level-3 result is the first node of the ten-level
binary path in the shared quad3 heap. -/
theorem quad3_honest_start (oracle : Oracle) (leaves : DigestTape) (index : Index) :
    (oracle.permutation (quadInput (quad3Group (quadFunction oracle.permutation) leaves (index.val/64)))).extractLsb' 0 256=
      quad3Heap oracle.compression (quadFunction oracle.permutation) leaves ((LENGTH+index.val)/64) := by
  have node : (LENGTH+index.val)/64=LENGTH/64+index.val/64 := by
    change (16777216+index.val)/64=262144+index.val/64
    omega
  have inside : index.val/64<LENGTH/64 := by
    have := index.isLt
    change index.val<16777216 at this
    change index.val/64<262144
    omega
  rw [node,quad3_heap_node _ _ _ _ inside]
  rfl

end TwoPermutationPrototype.Quad.Checker
