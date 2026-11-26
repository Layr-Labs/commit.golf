import CommitGolfCandidate.ReconstructedLeafMacros

namespace CommitGolfCandidate.Reconstruction.LeafSpill
open CommitGolf RiscvZkvm.Rv64 TwoPermutationPrototype.RV64
open LeafCode LeafModel LeafMacros

def intermediate (m : Model) (base : Nat) (j : Nat) :=
  (List.range j).foldl (fun x i => x.set (saved i) (m.mem (base+14+i))) m

private theorem advance (m : Model) (base j : Nat) :
    intermediate m base (j+1) = (intermediate m base j).set (saved j) (m.mem (base+14+j)) := by
  simp [intermediate,List.range_succ,List.foldl_append]

theorem memory (m : Model) (base j : Nat) : (intermediate m base j).mem = m.mem := by
  induction j with
  | zero => rfl
  | succ j ih => rw [advance]; exact ih

theorem other (m : Model) (base j : Nat) (r : Reg) (notUsed : ∀ k < j, saved k ≠ r) :
    (intermediate m base j).reg r = m.reg r := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [advance]
    simp only [Model.set,notUsed j (by omega),false_and,ite_false]
    exact ih (fun k hk => notUsed k (by omega))

theorem captured (m : Model) (base : Nat) (j : Fin 8) :
    (intermediate m base 8).reg (saved j.val) = m.mem (base+14+j.val) := by
  fin_cases j <;> rfl

private theorem keepsDestination (m : Model) (base j : Nat) (limit : j ≤ 8) :
    (intermediate m base j).reg .x12 = m.reg .x12 := by
  apply other
  intro k hk
  have tbl : ∀ k : Fin 8, saved k.val ≠ .x12 := by decide
  exact tbl ⟨k,by omega⟩

/-- The last four two-word salts are copied to eight registers before any lane's
second permutation. The other words remain directly addressable in memory. -/
theorem capture (o : Oracle) (m : Model) (base : Nat) (room : base+25 ≤ 2^33)
    (dst : m.reg .x12 = wordAddress base) : Contract o spill m (intermediate m base 8) := by
  have run (n : Nat) (limit : n ≤ 8) : Contract o ((List.range n).map fun j =>
      .LD (saved j) .x12 (BitVec.ofNat 12 (112+8*j))) m (intermediate m base n) := by
    induction n with
    | zero => exact LeafModel.empty _ _
    | succ j ih =>
      rw [List.range_succ,List.map_append,advance]
      apply LeafModel.combine (ih (by omega))
      have addr : (intermediate m base j).reg .x12 + signExtend12 (BitVec.ofNat 12 (112+8*j)) =
          wordAddress (base+14+j) := by
        have tbl : ∀ k : Fin 8, signExtend12 (BitVec.ofNat 12 (112+8*k.val)) = wordAddress (14+k.val) :=
          by decide
        rw [keepsDestination _ _ _ (by omega),dst,plus base (14+j) _ (tbl ⟨j,by omega⟩),Nat.add_assoc]
      have step := LeafModel.load o (intermediate m base j) (saved j) .x12 _ (base+14+j) (by omega) addr
      simpa only [List.map_cons,List.map_nil,memory] using step
  exact run 8 (by decide)

/-- Ordinary lanes stage the two full 64-bit registers. SB subsequently erases eight bits. -/
def stamp (m : Model) (p : Nat) (lo hi : Word) := (m.store (p+1) lo).store (p+2) hi

private theorem writePair (o : Oracle) (m : Model) (p : Nat) (lr hr : Reg)
    (lo hi : Word) (room : p+3 ≤ 2^33) (ptr : m.reg .x10 = wordAddress p)
    (l : m.reg lr = lo) (h : m.reg hr = hi) :
    Contract o [.SD .x10 lr 8,.SD .x10 hr 16] m (stamp m p lo hi) := by
  let a := m.store (p+1) lo
  have s1 := LeafModel.store o m .x10 lr 8 (p+1) (by omega) (by rw [ptr,plus p 1 8 rfl])
  rw [l] at s1
  have s2 := LeafModel.store o a .x10 hr 16 (p+2) (by omega) (by
    change m.reg .x10+_ = _; rw [ptr,plus p 2 16 rfl])
  change Contract _ _ a (a.store (p+2) (m.reg hr)) at s2
  rw [h] at s2
  exact LeafModel.combine s1 s2

def nearState (m : Model) (p base lane : Nat) :=
  let w := base+2*(lane-1)
  let a := (m.set .x6 (m.mem w)).set .x7 (m.mem (w+1))
  stamp a p (m.mem w) (m.mem (w+1))

theorem near (o : Oracle) (m : Model) (base : Nat) (l : Fin 8) (positive : 0 < l.val)
    (p : Nat) (geom : p = base+22+32*l.val) (room : p+3 ≤ 2^33)
    (ptr : m.reg .x10 = wordAddress p) :
    Contract o (saltLoad l.val) m (nearState m p base l.val) := by
  let lane := l.val
  let w := base+2*(lane-1)
  let dist := 22+32*lane-2*(lane-1)
  let disp := 4096+16*(lane-1)-176-256*lane
  let a := m.set .x6 (m.mem w)
  let b := a.set .x7 (m.mem (w+1))
  have lim : lane < 8 := l.isLt
  have coord : p-dist = w ∧ p-(dist-1)=w+1 ∧ dist ≤ p := by dsimp [dist,w,lane]; omega
  have table : ∀ k : Fin 8, 0 < k.val →
      let v := k.val
      let n := 22+32*v-2*(v-1)
      let d := 4096+16*(v-1)-176-256*v
      wordAddress n + signExtend12 (BitVec.ofNat 12 d) = 0 ∧
        wordAddress (n-1) + signExtend12 (BitVec.ofNat 12 (d+8)) = 0 := by decide
  obtain ⟨neg,neg'⟩ := table l positive
  have s1 := LeafModel.load o m .x6 .x10 (BitVec.ofNat 12 disp) w (by omega) (by
    rw [ptr,minus p dist _ coord.2.2 neg,coord.1])
  have s2 := LeafModel.load o a .x7 .x10 (BitVec.ofNat 12 (disp+8)) (w+1) (by omega) (by
    change m.reg .x10+_ = _; rw [ptr,minus p (dist-1) _ (by omega) neg',coord.2.1])
  have s3 := writePair o b p .x6 .x7 (m.mem w) (m.mem (w+1)) room ptr rfl rfl
  have run := LeafModel.combine s1 (LeafModel.combine s2 s3)
  simpa only [saltLoad,show l.val≠0 by omega,ite_false,l.isLt,ite_true,disp,lane,nearState,w,b,a,Model.set, List.cons_append,List.nil_append] using run

theorem far (o : Oracle) (m : Model) (p lane : Nat) (large : 8 ≤ lane) (room : p+3 ≤ 2^33)
    (ptr : m.reg .x10 = wordAddress p) :
    Contract o (saltLoad lane) m (stamp m p (m.reg (saved (2*(lane-8)))) (m.reg (saved (2*(lane-8)+1)))) := by
  simp only [saltLoad,show lane≠0 by omega,show ¬lane<8 by omega,ite_false]
  exact writePair _ _ _ _ _ _ _ room ptr rfl rfl

end CommitGolfCandidate.Reconstruction.LeafSpill
