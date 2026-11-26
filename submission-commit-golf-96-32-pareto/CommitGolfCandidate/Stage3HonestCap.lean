import CommitGolfCandidate.Stage3HonestPath
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv
open CommitGolfCandidate.Late (Levels SaltTape node capSlot wideOpening)
open CommitGolfCandidate.Late.Check (canonicalInput)
set_option maxRecDepth 12000
set_option maxHeartbeats 500000
attribute [local irreducible] Late.treeM node lowerHash capSlot wideOpening recordValue

private theorem found (input : CheckInput) (u r : Nat) (e : firstAt input u=some r) :
    r<128 ∧ openingIndex input.positions r/65536=u := by
  unfold firstAt at e
  exact ⟨List.mem_range.mp (List.mem_of_find?_eq_some e),beq_iff_eq.mp (List.find?_some (p:=fun j => openingIndex input.positions j/65536==u) e)⟩

private theorem absent (input : CheckInput) (u : Nat) (e : firstAt input u=none) :
    ∀ r<128, openingIndex input.positions r/65536≠u := by
  intro r hr eqn
  exact (List.find?_eq_none.mp e r (List.mem_range.mpr hr)) (beq_iff_eq.mpr eqn)

private theorem slot_eq (t : Levels) (ps : Positions) (p : Nat) (d : Digest)
    (fallback : (∀ r<ps.card,openingIndex ps r/131072≠p) → node t 17 p=d)
    (hit : ∀ r<ps.card,openingIndex ps r/131072=p →
      node t 16 ((openingIndex ps r/65536) ^^^ 1)=d) : capSlot t (ps.sort (·≤·)) p=d := by
  let xs:=ps.sort (·≤·)
  have len : xs.length=ps.card := Finset.length_sort ..
  have idx (r : Nat) (hr : r<xs.length) : openingIndex ps r=xs[r].val := by
    unfold openingIndex;rw [dif_pos (by omega)]
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
    have equal : openingIndex ps r=i.val := (idx r hr).trans (congrArg Fin.val atR)
    have good : i.val/131072=p := beq_iff_eq.mp (List.find?_some (p:=fun j : Index=>j.val/2^17==p) e)
    change node t 16 (i.val/65536 ^^^ 1)=d
    rw [←equal]; apply hit r (by omega); rw [equal];exact good

theorem batchHonest (h : Compression) (m : Message) (s : SaltTape) (ps : Positions) (b : ps.card=BATCH) :
    let t:=Late.treeM (M:=Id) h m s
    BatchValid h (canonicalInput m ps t s) := by
  let t:=Late.treeM (M:=Id) h m s
  let input:=canonicalInput m ps t s
  let ix:=fun r=>openingIndex ps r
  have k : ps.card=128:=b
  have dep : Late.Check.depth input=16 := by change (if ps.card=BATCH then 16 else 24)=_;rw [if_pos b]
  have stride (r : Nat) : Late.Check.start input r=536*r := by unfold Late.Check.start;rw [dep];omega
  have lo (r : Nat) (hr : r<128) : lowerHash h input r=node t 16 (ix r/65536) := by
    have ref:=widePath h m s ps r 16 (by omega) (by decide) dep.ge
    have ss : batchSalt input r=Late.Check.salt input r := by unfold Late.Check.salt;rw [stride];rfl
    have pp : lowerSibling input r=Late.Check.sibling input r := by
      funext j;unfold lowerSibling Late.Check.sibling Late.Check.proofAt;rw [stride]
      change readBuffer _ (12079599648+536*r+24+32*j) 32=readBuffer _ (12079599648+(536*r+24+32*j)) 32
      rw [show 12079599648+536*r+24+32*j=12079599648+(536*r+24+32*j) by omega] <;> rfl
    unfold lowerHash;rw [ss,pp];exact ref
  have hit (u r : Nat) (e : firstAt input u=some r) : ix r/65536=u := (found input u r e).2
  have digest (u r : Nat) (e : firstAt input u=some r) : lowerHash h input r=node t 16 u := by
    rw [lo _ (found input u r e).1,hit _ _ e]
  have cap (p : Nat) (hp : p<128) : parentAt h input p = node t 17 p := by
    have slots := Late.Check.honest_slot m ps t s p b hp
    have ss : supplied input p=Late.Check.supplied input p := by
      unfold supplied Late.Check.supplied Late.Check.proofAt
      change readBuffer _ (12079668256+32*p) 32=readBuffer _ (12079599648+(68608+32*p)) 32
      rw [show 12079668256+32*p=12079599648+(68608+32*p) by omega] <;> rfl
    have slots:=ss.trans slots
    let hpTree:=Late.heap h m s
    have par : node t 17 p=storeNode (128+p) (combine h (node t 16 (2*p)) (node t 16 (2*p+1))) := by
      rw [Late.heapLevel h m s 17 p (by decide) hp,Late.heapLevel h m s 16 (2*p) (by decide) (by change 2*p<256;omega),
        Late.heapLevel h m s 16 (2*p+1) (by decide) (by change 2*p+1<256;omega)]
      change hpTree (128+p)=storeNode _ (combine h (hpTree (256+2*p)) (hpTree (256+(2*p+1))))
      have step:=reference_heap_parent h LENGTH (fun j=>(Late.initialList h m s)[j]?.getD 0) (128+p) (by omega) (by change 128+p<16777216;omega)
      change hpTree (128+p)=parent h (128+p) (hpTree (2*(128+p))) (hpTree (2*(128+p)+1)) at step
      rw [show 256+2*p=2*(128+p) by omega,show 256+(2*p+1)=2*(128+p)+1 by omega];exact step
    unfold parentAt parentFrom PairCap.Children.parent childrenAt
    cases l : firstAt input (2*p) with
    | none =>
      have noL := absent input (2*p) l
      cases rr : firstAt input (2*p+1) with
      | none =>
        have noR := absent input (2*p+1) rr
        apply slots.trans
        apply slot_eq _ _ _ _ (fun _=>rfl)
        intro r hr e
        have nl:=noL r (by omega);have nr:=noR r (by omega)
        change ix r/65536≠_ at nl nr
        change ix r/131072=p at e
        omega
      | some r =>
        have eq := hit _ _ rr
        have slot := slot_eq t ps p (node t 16 (2*p))
          (by intro miss; have wrong:=miss r (by have z:=(found input _ _ rr).1;omega);change ix r/131072≠p at wrong;omega)
          (by intro z hz pair;have no:=noL z (by omega);change ix z/65536≠_ at no
              change ix z/131072=p at pair;change node t 16 ((ix z/65536) ^^^ 1)=_
              rw [show ix z/65536=2*p+1 by omega,Nat.xor_one_of_odd (Nat.odd_iff.mpr (by omega))]
              congr 1 <;> omega)
        simpa only [Option.map_none,Option.map_some,Option.isNone_some,Option.isNone_none,Bool.and_false,Bool.false_and,Bool.false_eq_true,ite_false,slots,slot,digest _ _ rr] using par.symm
    | some a =>
      cases rr : firstAt input (2*p+1) with
      | some z => simpa only [Option.map_some,Option.isNone_some,Bool.false_and,Bool.false_eq_true,ite_false,digest _ _ l,digest _ _ rr] using par.symm
      | none =>
        have noR := absent input (2*p+1) rr
        have eq := hit _ _ l
        have slot := slot_eq t ps p (node t 16 (2*p+1))
          (by intro miss;have no:=miss a (by have z:=(found input _ _ l).1;omega);change ix a/131072≠p at no;omega)
          (by intro z hz pair;have no:=noR z (by omega);change ix z/65536≠_ at no
              change ix z/131072=p at pair;change node t 16 ((ix z/65536) ^^^ 1)=_
              rw [show ix z/65536=2*p by omega,Nat.xor_one_of_even (Nat.even_iff.mpr (by omega))])
        simpa only [Option.map_none,Option.map_some,Option.isNone_some,Option.isNone_none,Bool.and_false,Bool.false_and,Bool.false_eq_true,ite_false,slots,slot,digest _ _ l] using par.symm
  constructor
  · change (wideOpening t s ps).length=72704;rw [Late.wide_size,if_pos b]
  · intro r hr
    let u := ix r/65536
    let p := ix r/131072
    have lookup : (firstAt input u).map (fun z=>lowerHash h input z) = some (lowerHash h input r) := by
      cases eqn : firstAt input u with
      | none => exact False.elim (absent input u eqn r hr rfl)
      | some z => simp [digest _ _ eqn,lo r hr,u]
    change (childrenAt h input p).child ((ix r).testBit 16) = _
    unfold PairCap.Children.child childrenAt
    rw [Nat.testBit_eq_decide_div_mod_eq]
    by_cases right : u%2=1
    · rw [if_pos (by change decide (u%2=1)=true;simp [right])]
      simpa only [show 2*p+1=u by dsimp [p,u] at *;omega] using lookup
    · rw [if_neg (by change ¬decide (u%2=1)=true;simp [right])]
      simpa only [show 2*p=u by dsimp [p,u] at *;omega] using lookup
  · let hpTree:=Late.heap h m s
    have ref:=heap_eq_reference h 128 (capTable h input) hpTree (fun n lo hi=>
      reference_heap_parent h LENGTH _ n lo (by change n<16777216;omega)) (fun j hj=>by
        rw [capTable,if_pos hj,cap j hj];exact (Late.heapLevel h m s 17 j (by decide) hj).symm)
      1 (by decide) (by decide)
    exact ref.symm.trans (Late.heapLevel h m s LOG_LENGTH 0 (by decide) (by decide)).symm

end CommitGolfCandidate.Trunc
