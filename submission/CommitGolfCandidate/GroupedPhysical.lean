import CommitGolfCandidate.GroupedSeededLeaves
import CommitGolfCandidate.GroupedSerial
import CommitGolfCandidate.GroupedQMeaning
import CommitGolfCandidate.QuartetPhysical
import CommitGolfCandidate.MaterializedManifest

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.QuartetCommit (qSource qSalt qLeaf qUpper digestWords pairLeaf pairHeap upper_sequence_semantics upper_groups_semantics UpperContent PaddedLeaves pair_heap_parent pair_heap_leaf packed_sequence_keeps_output wide_parent_full_register)
open CommitGolfCandidate.Permutation.CounterSalt (salts)
set_option maxRecDepth 18000
set_option maxHeartbeats 1000000
attribute [local irreducible] readBuffer checkEvaluation qGroups qUnits scan fixedScan packedParentsTrace packedParentGroups rootPrefix pairHeap pairLeaf readyState
attribute [local irreducible] seededLeaves packedOutput tailBody

theorem physical_results (oracle : Oracle) (msg : Message) (key : Key) :
    let leaves:=seededLeaves oracle msg key
    let r:=salts oracle.permutation key
    let output:=actual.readCommit (packedOutput oracle leaves)
    let heap:=pairHeap oracle msg r
    output.1=heap 1 ∧ (∀ n, 0<n → n<8388608 → Opening.trapdoorHeap (s:=actual) output.2 n=heap n) ∧
      (∀ i : Index, QuartetRV.trapdoorLeaf (s:=actual) output.2 i.val=pairLeaf oracle msg r i.val) ∧
      (∀ j : Fin 3, savedKey output.2 j=key.extractLsb' (64*j.val) 64) := by
  let leaves:=seededLeaves oracle msg key
  let salts:=salts oracle.permutation key
  let heap:=pairHeap oracle msg salts
  obtain ⟨ready,good⟩:=seeded_content oracle msg key
  obtain ⟨_,qpc,qregs,carry⟩:=quartet_entry leaves ready
  let qs:=qStartPrefix leaves 3
  let quad:=(checkEvaluation oracle (qGroups 512 0 qs)).1
  obtain ⟨_,upc,uregs,out⟩ := start_upper qs qregs qpc carry (check_evaluation_support oracle (qGroups 512 0 qs))
  let us:=upStartPrefix quad 6
  let pre:=(checkEvaluation oracle (packedParentsTrace 4194176 127 us)).1
  let parents:=(checkEvaluation oracle (packedParentGroups GroupedUpper.loopBase 32767 128 pre)).1
  have leafContent : PaddedLeaves (memoryView leaves) (fun i => digestWords (pairLeaf oracle msg salts i)) := by
    refine ⟨good.padding,?_⟩;intro i hi
    simpa only [pairLeaf,Quartet.leafAt,dif_pos (show i<LENGTH from hi),value] using good.children ⟨i,hi⟩ (by show i<2*8388608; omega)
  have uContent:=ready_upper_content oracle msg salts leaves leafContent
  have preContent:=upper_sequence_semantics oracle us heap (memoryView leaves) 4194176 127 (by decide)
    (pair_heap_parent oracle msg salts) uContent uregs
  have parentContent:=upper_groups_semantics oracle GroupedUpper.loopBase 32767 128 pre heap (memoryView leaves) (by decide)
    (pair_heap_parent oracle msg salts) preContent.1 preContent.2
  have hit1:=check_evaluation_support oracle (packedParentsTrace 4194176 127 us)
  have hit2:=check_evaluation_support oracle (packedParentGroups GroupedUpper.loopBase 32767 128 pre)
  have pc1:= (packed_parent_segment_post 284808 4194176 127 0 us uregs (by simpa [packedParentPC] using upc) hit1).2
  have pc2 : pre.pc=GroupedUpper.loopBase := pc1
  have preg := (packed_groups_post GroupedUpper.loopBase 32767 128 pre (by decide) (fun _ => pc2) preContent.2 hit2).1
  have x8:= (wide_parent_full_register _ _ _ _ hit2).trans ((packed_sequence_keeps_output _ _ _ hit1).trans out)
  exact serialize parents heap (pairLeaf oracle msg salts) key _ (eval_tail oracle leaves) preg.heap x8
    (finish_stores parents leaves heap _ key parentContent leafContent good.key)


theorem tail_counted (o : Oracle) (s : MachineState) : RunPublic o (tailBody s) 8388607 := by
  unfold tailBody
  apply run_bind_public _ _ _ 4194304 4194303 (q_groups_counted ..);intro quad
  apply run_bind_public _ _ _ 127 4194176 (counted_packed_parents ..);intro pre
  exact run_bind_public _ _ _ 4194176 0 (counted_packed_groups ..) (fun _ => run_pure_public ..)

theorem counted_commit (o : Oracle) (msg : Message) :
    o.run (actual.run .commit msg)=(do let k ← $ᵗ Key;return (packedOutput o (seededLeaves o msg k),43470847)) := by
  rw [commit_of_image actual exact_image.symm (by decide) msg ⟨rfl,rfl,rfl,rfl⟩]
  unfold commitTrace;rw [oracle_run_coins_bind];apply bind_congr;intro k
  rw [oracle_run_bind,fixed_scan_run _ _ _ _ (by decide),pure_bind];dsimp only
  rw [oracle_run_bind,show o.run (tailBody _)=_ from tail_counted o _,pure_bind]
  simp only [oracle_run_pure,pure_bind]
  simp only [packedOutput,seededLeaves];rfl

end TwoPermutationPrototype.Grouped
