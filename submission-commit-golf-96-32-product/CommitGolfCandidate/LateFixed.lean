import CommitGolfCandidate.LateModel
import CommitGolfCandidate.Counting

namespace CommitGolfCandidate.Late
open CommitGolf OracleComp

def view {α : Type} (o : Oracle) (c : OracleComp World α) : ProbComp α := Prod.fst <$> o.run c

theorem view_bind {α β : Type} (o : Oracle) (c : OracleComp World α) (k : α → OracleComp World β) :
    view o (c >>= k) = (view o c >>= fun x => view o (k x)) := by
  simp only [view, oracle_run_bind, map_bind, map_pure, bind_map_left]
  apply bind_congr
  rintro ⟨x,n⟩
  simp [map_eq_bind_pure_comp]

theorem view_pure {α : Type} (o : Oracle) (v : α) :
    view o (pure v) = pure v := by rw [view, oracle_run_pure, map_pure]

theorem view_hash (o : Oracle) (x : Block) : view o (hash x) = pure (o.compression x) := by
  unfold view hash
  erw [oracle_run_public o (.inl x), map_pure]
  rfl

theorem view_leaf (o : Oracle) (odd : Bool) (s : Salt) (v : Entry) :
    view o (leafM hash odd s v) = pure (leaf o.compression odd s v) := by
  simp only [leafM, view_bind, view_hash, pure_bind]
  rfl

private theorem view_mapM {α β : Type} (o : Oracle) (xs : List α) (f : α → OracleComp World β)
    (g : α → β) (agree : ∀ x, view o (f x) = pure (g x)) :
    view o (xs.mapM f) = pure (xs.map g) := by
  induction xs with
  | nil => exact view_pure _ _
  | cons x xs ih => simp only [List.mapM_cons, view_bind, agree, ih, pure_bind, view_pure, List.map_cons]

theorem view_parents (o : Oracle) (height : Nat) (xs : List Digest) :
    view o (parentsM hash height xs) = pure (parentsM (M := Id) o.compression height xs) := by
  match xs with
  | [] | [_] => exact view_pure _ _
  | a::b::xs =>
    simp only [parentsM, view_bind, view_hash, pure_bind, view_parents o height xs, view_pure]
    rfl

theorem view_levels (o : Oracle) (d : Nat) (xs : List Digest) :
    view o (levelsM hash d xs) = pure (levelsM (M := Id) o.compression d xs) := by
  induction d generalizing xs with
  | zero => exact view_pure _ _
  | succ d ih =>
    simp only [levelsM, view_bind, view_parents, ih, pure_bind, view_pure]
    rfl

attribute [local irreducible] List.finRange

theorem view_tree (o : Oracle) (m : Message) (s : SaltTape) :
    view o (treeM hash m s) = pure (treeM (M := Id) o.compression m s) := by
  unfold treeM
  rw [view_bind, view_mapM _ _ _ _ (fun i => view_leaf o _ _ _), pure_bind, view_levels]
  have mapId {α β : Type} (xs : List α) (f : α → β) :
      (xs.mapM (m := Id) f) = xs.map f := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [List.mapM_cons, ih]; rfl
  change pure (levelsM (M := Id) o.compression LOG_LENGTH _) =
    pure (levelsM (M := Id) o.compression LOG_LENGTH ((List.finRange LENGTH).mapM (m := Id) _))
  rw [mapId]
  rfl
end CommitGolfCandidate.Late
