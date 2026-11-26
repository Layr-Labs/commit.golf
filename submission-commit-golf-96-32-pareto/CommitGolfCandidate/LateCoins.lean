import CommitGolfCandidate.LateModel
import CommitGolfCandidate.CountingCoins
import VCVio.OracleComp.Constructions.SampleableType.Measure

namespace CommitGolfCandidate.Late
open CommitGolf OracleComp

local instance {α : Type} : MeasurableSpace α := ⊤

private theorem iid_words {α : Type} (xs : List Nat) (k : List PairCoins → ProbComp α) :
    𝒟[xs.mapM (fun _ => ($ᵗ PairCoins : ProbComp PairCoins)) >>= k] =
      𝒟[($ᵗ (Fin xs.length → PairCoins)) >>= fun f => k (List.ofFn f)] := by
  induction xs generalizing k with
  | nil =>
    simp only [List.mapM_nil, pure_bind, List.length_nil, List.ofFn_zero]
    exact (OracleComp.evalDist_bind_const _ _).symm
  | cons i xs ih =>
    let e := Fin.consEquiv (fun _ : Fin (xs.length+1) => PairCoins)
    have uniform := ((SampleableType.map_uniformSample_evalDistEq_of_bijective e.bijective).bind_left
      (fun f => k (List.ofFn f))).evalDist_eq
    rw [List.length_cons, ← uniform, bind_map_left, SampleableType.uniformSample_prod_eq_bind]
    simp only [List.mapM_cons, bind_assoc, pure_bind]
    apply _root_.evalDist_bind_congr
    intro w
    rw [ih (fun ws => k (w::ws))]
    congr 1
    apply bind_congr
    intro f
    change k (w::List.ofFn f) = k (List.ofFn (Fin.cons w f))
    simp [List.ofFn_succ]

abbrev PairIndex := Fin (LENGTH/2)

def unpack (ws : PairIndex → PairCoins) (i : Index) : Salt :=
  pairSalts (ws ⟨i.val/2, by have := i.isLt; change i.val < 16777216 at this
                             change i.val / 2 < 8388608; omega⟩) (i.val.testBit 0)

def pack (s : SaltTape) (p : PairIndex) : PairCoins :=
  let bound := p.isLt
  s ⟨2*p.val+1, by change p.val < 8388608 at bound; change _ < 16777216; omega⟩ ++
  s ⟨2*p.val, by change p.val < 8388608 at bound; change _ < 16777216; omega⟩

theorem unpack_pack (s : SaltTape) : unpack (pack s) = s := by
  funext i
  unfold unpack pack pairSalts
  simp only [Nat.testBit_eq_decide_div_mod_eq, Nat.pow_zero, Nat.div_one]
  split
  · rw [BitVec.extractLsb'_append_eq_left]
    congr 1
    apply Fin.ext
    simp_all
    omega
  · rw [BitVec.extractLsb'_append_eq_right]
    congr 1
    apply Fin.ext
    simp_all
    omega

theorem pack_unpack (ws : PairIndex → PairCoins) : pack (unpack ws) = ws := by
  funext p
  unfold pack unpack pairSalts
  have odd : (2*p.val+1).testBit 0 = true := by
    simp only [Nat.testBit_eq_decide_div_mod_eq, Nat.pow_zero, Nat.div_one]; simp
  have even : (2*p.val).testBit 0 = false := by
    simp [Nat.testBit_eq_decide_div_mod_eq]
  simp only [odd, even, Bool.false_eq_true, if_false, if_true]
  have a : (2*p.val+1)/2 = p.val := by omega
  have b : 2*p.val/2 = p.val := by omega
  simp only [a, b, Fin.eta]
  exact BitVec.extractLsb'_append_extractLsb'

theorem unpack_uniform {α : Type} (k : SaltTape → ProbComp α) :
    𝒟[($ᵗ (PairIndex → PairCoins)) >>= fun ws => k (unpack ws)] =
      𝒟[($ᵗ SaltTape) >>= k] := by
  rw [← bind_map_left]
  exact ((SampleableType.map_uniformSample_evalDistEq_of_bijective
    (f := unpack) ⟨Function.LeftInverse.injective pack_unpack,
      Function.RightInverse.surjective unpack_pack⟩).bind_left k).evalDist_eq

theorem lift_draws (xs : List Nat) :
    xs.mapM (fun _ => drawPair) =
      (liftM (xs.mapM (fun _ => ($ᵗ PairCoins : ProbComp PairCoins))) : OracleComp World _) := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
    simp only [List.mapM_cons, liftM_bind, liftM_pure]
    rw [ih]
    rfl

private theorem range_uniform {α : Type} (n : Nat) (xs : List Nat) (len : xs.length = n)
    (k : List PairCoins → ProbComp α) :
    𝒟[xs.mapM (fun _ => ($ᵗ PairCoins : ProbComp PairCoins)) >>= k] =
      𝒟[($ᵗ (Fin n → PairCoins)) >>= fun ws => k (List.ofFn ws)] := by
  subst n
  exact iid_words xs k

attribute [local irreducible] List.range

/-- Retain an arbitrary continuation and its public-call count. Drawing the
machine's ordered words is exactly uniform on the complete per-leaf salt tape. -/
theorem sample_salts_uniform {α : Type} (oracle : Oracle) (k : SaltTape → OracleComp World α) :
    letI : MeasurableSpace (α × Nat) := ⊤
    𝒟[oracle.run (sampleSalts >>= k)] =
      𝒟[($ᵗ SaltTape) >>= fun s => oracle.run (k s)] := by
  letI : MeasurableSpace (α × Nat) := ⊤
  unfold sampleSalts
  simp only [bind_assoc, pure_bind, lift_draws, oracle_run_coins_bind]
  let readWords (ws : List PairCoins) : SaltTape := fun i =>
    pairSalts (ws[i.val/2]?.getD 0) (i.val.testBit 0)
  have law := range_uniform (α := α × Nat) (LENGTH/2) (List.range (LENGTH/2))
    (List.length_range (n := LENGTH/2)) (fun ws => oracle.run (k (readWords ws)))
  have slice (ws : PairIndex → PairCoins) :
      (fun i : Index => pairSalts ((List.ofFn ws)[i.val/2]?.getD 0) (i.val.testBit 0)) =
        unpack ws := by
    funext i
    have bound : i.val/2 < LENGTH/2 := by
      have h := i.isLt
      change i.val < 16777216 at h
      change i.val/2 < 8388608
      omega
    simp only [unpack, List.getElem?_ofFn, dif_pos bound, Option.getD_some]
  have conversion (ws : PairIndex → PairCoins) : readWords (List.ofFn ws) = unpack ws := slice ws
  simp only [conversion] at law
  exact law.trans (unpack_uniform (fun s => oracle.run (k s)))

end CommitGolfCandidate.Late
