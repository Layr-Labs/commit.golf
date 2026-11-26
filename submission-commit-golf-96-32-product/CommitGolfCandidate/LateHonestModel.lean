import CommitGolfCandidate.LateHonestFields
import CommitGolfCandidate.LateHonestTree
import CommitGolfCandidate.LateResources2

namespace CommitGolfCandidate.Late.Check
open CommitGolf
set_option maxRecDepth 5000
attribute [local irreducible] leaf treeM node lower recordValue capSlot opening

private theorem found (input : CheckInput) (u r : Nat) (e : first input u=some r) :
    r<128 ∧ (recordIndex input.positions r).val/65536=u := by
  unfold first at e
  exact ⟨List.mem_range.mp (List.mem_of_find?_eq_some e),beq_iff_eq.mp (List.find?_some (p:=fun j => (recordIndex input.positions j).val/65536==u) e)⟩

private theorem absent (input : CheckInput) (u : Nat) (e : first input u=none) :
    ∀ r<128, (recordIndex input.positions r).val/65536≠u := by
  intro r hr eqn
  exact (List.find?_eq_none.mp e r (List.mem_range.mpr hr)) (beq_iff_eq.mpr eqn)

theorem honest_lower (h : Compression) (m : Message) (s : SaltTape) (t : Levels)
    (tree : HonestTree h m s t) (p : Positions) (r d : Nat) (hr : r<p.card)
    (hd : d≤depth (canonicalInput m p t s)) (height : d≤LOG_LENGTH) :
    lower h (canonicalInput m p t s) r d = node t d (Open.indexAbove (recordIndex p r) d) := by
  let x:=canonicalInput m p t s
  let i:=recordIndex p r
  have fields : path i d (sibling x r) = path i d (fun l=>node t l (Open.mate i l)) := by
    apply List.map_congr_left
    intro l hl
    exact congrArg (fun a => (i.val.testBit l,a)) (honest_sibling m p t s r l hr (by have := List.mem_range.mp hl;omega)
      (fun d j c hj => tree.stored h m s t d j c hj))
  unfold lower
  change climbAt _ 0 (leaf _ (i.val.testBit 0) (salt x r) (recordValue x r)) (path i d _) = _
  rw [honest_salt m p t s r hr,honestValue m p t s r hr,fields]
  exact tree.climb h m s t i d height

private theorem slot_eq (t : Levels) (ps : Positions) (p : Nat) (d : Digest)
    (fallback : (∀ r<ps.card,(recordIndex ps r).val/131072≠p) → node t 17 p=d)
    (hit : ∀ r<ps.card,(recordIndex ps r).val/131072=p →
      node t 16 (((recordIndex ps r).val/65536) ^^^ 1)=d) : capSlot t (ps.sort (·≤·)) p=d := by
  let xs:=ps.sort (·≤·)
  have len : xs.length=ps.card := Finset.length_sort ..
  have idx (r : Nat) (hr : r<xs.length) : recordIndex ps r=xs[r] := by
    change xs[r]?.getD _=xs[r];rw [List.getElem?_eq_getElem hr];rfl
  unfold capSlot
  cases e : xs.find? (fun i => i.val/2^17==p) with
  | none =>
    apply fallback
    intro r hr equal
    have hr' : r<xs.length := by omega
    exact (List.find?_eq_none.mp e xs[r] (List.getElem_mem hr')) (beq_iff_eq.mpr ((idx r hr') ▸ equal))
  | some i =>
    have mem := List.mem_of_find?_eq_some e
    obtain ⟨r,hr,atR⟩ := List.getElem_of_mem mem
    have equal : recordIndex ps r=i := (idx r hr).trans atR
    have good : i.val/131072=p := beq_iff_eq.mp (List.find?_some (p:=fun j : Index=>j.val/2^17==p) e)
    exact equal ▸ hit r (by omega) (equal ▸ good)

private theorem batch_honest (h : Compression) (m : Message) (s : SaltTape) (t : Levels)
    (tree : HonestTree h m s t) (ps : Positions) (b : ps.card=BATCH) :
    BatchValid h (canonicalInput m ps t s) := by
  let input := canonicalInput m ps t s
  let ix := fun r => (recordIndex ps r).val
  have k : ps.card=128 := b
  have lo (r : Nat) (hr : r<128) : lower h input r 16=node t 16 (ix r/65536) :=
    honest_lower h m s t tree ps r 16 (by omega) (by change 16≤(if ps.card=BATCH then 16 else 24);simp [b]) (by decide)
  have hit (u r : Nat) (e : first input u=some r) : ix r/65536=u := (found input u r e).2
  have digest (u r : Nat) (e : first input u=some r) : lower h input r 16=node t 16 u := by
    rw [lo _ (found input u r e).1,hit _ _ e]
  have cap (p : Nat) (hp : p<128) : parent h input p = node t 17 p := by
    have slots := honest_slot m ps t s p b hp (fun d j c hj => tree.stored h m s t d j c hj)
    change supplied input p=_ at slots
    have par := tree.pair 16 p (by decide) hp
    unfold parent PairCap.Children.parent children
    cases l : first input (2*p) with
    | none =>
      have noL := absent input (2*p) l
      cases rr : first input (2*p+1) with
      | none =>
        have noR := absent input (2*p+1) rr
        have slot : capSlot t (ps.sort (·≤·)) p = node t 17 p := by
          apply slot_eq _ _ _ _ (fun _=>rfl)
          intro r hr e
          have nl:=noL r (by omega);have nr:=noR r (by omega)
          change ix r/65536≠_ at nl nr
          change ix r/131072=p at e
          omega
        show cut 17 (supplied input p) = _
        rw [slots,slot,cut_of_cut ⟨by decide,by decide⟩]
        exact (tree.stored h m s t 17 p ⟨by decide,by decide⟩ hp).symm
      | some r =>
        have eq := hit _ _ rr
        have slot := slot_eq t ps p (node t 16 (2*p))
          (by intro miss; have wrong:=miss r (by have z:=(found input _ _ rr).1;omega);change ix r/131072≠p at wrong;omega)
          (by intro z hz pair;have no:=noL z (by omega);change ix z/65536≠_ at no
              change ix z/131072=p at pair;change node t 16 ((ix z/65536) ^^^ 1)=_
              rw [show ix z/65536=2*p+1 by omega,Nat.xor_one_of_odd (Nat.odd_iff.mpr (by omega))]
              congr 1 <;> omega)
        show cut 17 (combine h (supplied input p) (lower h input r 16)) = _
        rw [slots,slot,digest _ _ rr]; exact par.symm
    | some a =>
      cases rr : first input (2*p+1) with
      | some z =>
        show cut 17 (combine h (lower h input a 16) (lower h input z 16)) = _
        rw [digest _ _ l,digest _ _ rr]; exact par.symm
      | none =>
        have noR := absent input (2*p+1) rr
        have eq := hit _ _ l
        have slot := slot_eq t ps p (node t 16 (2*p+1))
          (by intro miss;have no:=miss a (by have z:=(found input _ _ l).1;omega);change ix a/131072≠p at no;omega)
          (by intro z hz pair;have no:=noR z (by omega);change ix z/65536≠_ at no
              change ix z/131072=p at pair;change node t 16 ((ix z/65536) ^^^ 1)=_
              rw [show ix z/65536=2*p by omega,Nat.xor_one_of_even (Nat.even_iff.mpr (by omega))])
        show cut 17 (combine h (lower h input a 16) (supplied input p)) = _
        rw [digest _ _ l,slots,slot]; exact par.symm
  constructor
  · change (opening t s ps).length=69120;rw [opening_size,if_pos b]
  · intro r hr
    let u := ix r/65536
    let p := ix r/131072
    have lookup : (first input u).map (fun z=>lower h input z 16) = some (lower h input r 16) := by
      cases eqn : first input u with
      | none => exact False.elim (absent input u eqn r hr rfl)
      | some z => simp [digest _ _ eqn,lo r hr,u]
    change (children h input p).child ((ix r).testBit 16) = _
    unfold PairCap.Children.child children
    rw [Nat.testBit_eq_decide_div_mod_eq]
    by_cases right : u%2=1
    · rw [if_pos (by change decide (u%2=1)=true;simp [right])]
      simpa only [show 2*p+1=u by dsimp [p,u] at *;omega] using lookup
    · rw [if_neg (by change ¬decide (u%2=1)=true;simp [right])]
      simpa only [show 2*p=u by dsimp [p,u] at *;omega] using lookup
  · apply tree.upper h m s t (capTable h input)
    intro j hj;rw [capTable,if_pos hj];exact cap j hj

theorem honest_valid (o : Oracle) (m : Message) (ws : List PairCoins) (ps : Positions) :
    Valid o.compression (honestInput o m ws ps) := by
  let t := cachedLevels o m ws;let s:=wordTape ws
  have tree : HonestTree o.compression m s t := honestTree o.compression m s
  change (if ps.card=BATCH then BatchValid _ (canonicalInput m ps t s) else
    (opening t s ps).length=ps.card*792 ∧ ∀ r<ps.card, lower _ (canonicalInput m ps t s) r 24 = node t LOG_LENGTH 0)
  by_cases b : ps.card=BATCH
  · rw [if_pos b];exact batch_honest _ _ _ _ tree ps b
  · rw [if_neg b]
    refine ⟨by rw [opening_size,if_neg b,Nat.mul_comm],?_⟩
    intro r hr
    let i:=recordIndex ps r
    have endIx : Open.indexAbove i 24=0 := Nat.div_eq_of_lt i.isLt
    have endNode := honest_lower _ _ _ _ tree ps r 24 hr (by change 24≤(if ps.card=BATCH then 16 else 24);simp [b]) (by decide)
    exact endNode.trans (congrArg (node t LOG_LENGTH) endIx)

end CommitGolfCandidate.Late.Check
