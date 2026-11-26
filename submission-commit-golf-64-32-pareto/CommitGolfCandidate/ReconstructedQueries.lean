import CommitGolfCandidate.ReconstructedRoutes

namespace CommitGolfCandidate.Reconstruction

universe u
variable {α : Type u} {h : Nat}

/-- Query cost of the checker's shared cap. A bottom block has one ordinary parent
and two eight-query parents. A fork above the blocks uses one compression when active. -/
def Cap.checkQueries {h : Nat} : Cap h → Nat
  | .block b => b.active.toNat + 8*((b.a || b.b).toNat + (b.c || b.d).toNat)
  | .fork l r => (l.count.active || r.count.active).toNat + l.checkQueries + r.checkQueries

private theorem active_le_endpoints (c : Cap h) : c.count.active.toNat ≤ c.count.endpoints := by
  induction c with
  | block b =>
    rcases b with ⟨a, b, c, d⟩
    cases a <;> cases b <;> cases c <;> cases d <;> decide
  | fork l r hl hr =>
    simp only [Cap.count]
    cases el : l.count.active <;> cases er : r.count.active <;> simp_all <;> omega

theorem cap_query_bound (c : Cap h) : c.checkQueries ≤ (h + 9)*c.count.endpoints := by
  induction c with
  | block b =>
    rcases b with ⟨a, b, c, d⟩
    cases a <;> cases b <;> cases c <;> cases d <;> decide
  | @fork h l r hl hr =>
    have active := active_le_endpoints (Cap.fork l r)
    simp only [Cap.count] at active
    simp only [Cap.checkQueries, Cap.count]
    rw [show h+1+9=(h+9)+1 by omega, Nat.succ_mul, Nat.mul_add]
    omega

/-- Two leaf permutations and the fifteen lower parent traversals per record. -/
def lowerQueries := 2 + (((sameSize.calls.drop 9).take 15).map (max 1)).sum

theorem lower_query_cost : lowerQueries = 84 := by decide

def checkedQueries (n : Nat) (cap : Cap 7) := n*lowerQueries + cap.checkQueries

theorem batch_query_bound (route : α → Route 7) (positions : List α) :
    checkedQueries positions.length (collect route positions) ≤ 100 * positions.length := by
  have cap := cap_query_bound (collect route positions)
  have ep := collect_bound route positions
  unfold checkedQueries
  rw [lower_query_cost]
  omega

theorem spread_query_cost : checkedQueries 128 (spread 7) = 12031 := by decide

end CommitGolfCandidate.Reconstruction
