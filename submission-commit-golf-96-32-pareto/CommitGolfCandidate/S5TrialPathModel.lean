import CommitGolfCandidate.S5CapUpperMemory

namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W)

def trialIndex (d : Nat) := 170 / 2^d

def trialValues (H : Compression) (x : CheckInput) (q0 q : Fin 4) (d : Nat) : Values :=
  fun h j => if h ≤ d then capVal H x q h j else capVal H x q0 h j

private theorem trial_away (H : Compression) (x : CheckInput) (q0 q : Fin 4)
    (h j : Nat) (away : j ≠ trialIndex h) : capVal H x q0 h j = capVal H x q h j := by
  apply S5.upper_local _ _ _ _ _ _ away
  intro i small distinct
  exact (S5.trial_pairs H x q0 i (by omega)).trans (S5.trial_pairs H x q i (by omega)).symm

theorem trial_start_values (H : Compression) (x : CheckInput) (q0 q : Fin 4) :
    replaceNode (capVal H x q0) 0 170 (capVal H x q 0 170) = trialValues H x q0 q 0 := by
  funext h j
  by_cases hz : h = 0
  · subst h
    by_cases jlast : j = 170
    · subst j; simp [replaceNode, trialValues]
    · simp only [replaceNode,jlast,and_false,ite_false,trialValues,Nat.le_refl,ite_true]
      exact trial_away H x q0 q 0 j jlast
  · simp [replaceNode,trialValues,hz]

theorem trial_next_values (H : Compression) (x : CheckInput) (q0 q : Fin 4) (d : Nat) :
    replaceNode (trialValues H x q0 q d) (d+1) (trialIndex (d+1))
      (capVal H x q (d+1) (trialIndex (d+1))) = trialValues H x q0 q (d+1) := by
  funext h j
  by_cases hs : h = d+1
  · subst h
    by_cases js : j = trialIndex (d+1)
    · subst j; simp [replaceNode,trialValues]
    · simp only [replaceNode,js,and_false,ite_false,trialValues,Nat.not_succ_le_self,Nat.le_refl,ite_true]
      exact trial_away H x q0 q (d+1) j js
  · have same : h ≤ d ↔ h ≤ d+1 := by omega
    simp [replaceNode,trialValues,hs,same]

theorem trial_done_cache {H x q0 q s} (cache : Cache s (trialValues H x q0 q 8)) :
    Cache s (capVal H x q) := by
  refine ⟨?_,cache.gap⟩
  intro h bound j inside
  simpa only [trialValues,if_pos (by omega : h ≤ 8)] using cache.node h bound j inside

def trialPathPC (d : Nat) :=
  ([1197,1205,1212,1220,1228,1236,1244,1252,1260] : List Nat)[d]?.getD 0

def trialPathOps (d : Nat) : List Sym.Calc :=
  let p := trialIndex (d+1)
  liOps .x10 (rowAt d p) ++ liOps .x12 (nodeAt (d+1) p)

def trialHashPC (d : Nat) := trialPathPC d + (trialPathOps d).length

theorem trial_path_sites : ∀ i : Fin 8,
    let d := i.val
    let p := trialIndex (d+1)
    let ops := trialPathOps d
    let f := ops.foldl Sym.bump Sym.original
    p < layerCount (d+1) ∧ Sym.Listed ops (trialPathPC d) ∧ Sym.requirements Sym.original ops = [] ∧
      f .x10 = .lit (W (rowAt d p)) ∧ f .x12 = .lit (W (nodeAt (d+1) p)) ∧
      (ops.all fun c => ([.x10,.x12] : List Reg).contains c.dst) ∧ ops.length ≤ 4 ∧
      parentSites (trialHashPC d) (16+d) ∧ trialHashPC d+4 < 2336 ∧
      trialHashPC d+4 = trialPathPC (d+1) := by decide +kernel

end CommitGolfCandidate.S5Machine.Check
