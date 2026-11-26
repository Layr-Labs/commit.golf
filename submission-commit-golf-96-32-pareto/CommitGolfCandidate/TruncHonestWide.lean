import CommitGolfCandidate.TruncCommitTruth
import CommitGolfCandidate.TruncCap
import CommitGolfCandidate.PairHonestRead
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open PairCap (hnode honestInput batchRecords parsedSalt parsedBlock batchSlot overrideSlot saved outBase opening_proof_length proofBytes)
set_option maxRecDepth 9000
set_option maxHeartbeats 230000
attribute [local irreducible] lowerHash readBuffer

theorem honestLower (o : Oracle) (s : MachineState) (m : Message) (ps : Positions) (ok : CommittedState o m s)
    (hb : ps.card=BATCH) (r : Nat) (hr : r<128) :
    lowerHash o.compression (honestInput s m ps) r = hnode s (256+openingIndex ps r/65536) := by
  let input := honestInput s m ps
  let i := recordIndex input r
  have present : r<ps.card := by rw [hb]; exact hr
  have vv : recordValue input r = m i := by
    unfold recordValue
    rw [dif_pos (show r < input.positions.card from present)]
    apply congrArg m
    apply Fin.ext
    exact sorted_value_index ps r present
  have raw := batchRecords s ps hb r hr
  have salt : batchSalt input r = readBuffer s (5905584160+16*i.val) 16 := by
    unfold batchSalt PairCap.batchSalt
    rw [parsedSalt s m ps hb (528*r) (by omega)]
    exact raw.1
  have sib (l : Nat) (bl : l<16) :
      lowerSibling input r l = hnode s (((LENGTH+i.val)/2^l) ^^^ 1) := by
    unfold lowerSibling PairCap.lowerSibling
    rw [show 10871640096+528*r+16+32*l=10871640096+(528*r+16+32*l) by omega,
      parsedBlock s m ps hb _ (by omega)]
    rw [show 10871640096+(528*r+16+32*l) = 10871640096+528*r+16+32*l by omega]
    exact raw.2 l bl
  have pp : recordPathPrefix 16 i (lowerSibling input r) = heapPath (hnode s) (LENGTH+i.val) 16 := by
    apply List.ext_getElem
    · rw [record_path_prefix_length,heap_path_length]
    · intro l h1 h2
      have bl : l<16 := by simpa only [record_path_prefix_length] using h1
      rw [heap_path_get _ _ _ _ bl]
      simp only [recordPathPrefix,List.getElem_map,List.getElem_range]
      exact Prod.ext ((heap_leaf_direction 24 i.val l i.isLt (by omega)).symm) (sib l bl)
  unfold lowerHash
  change recordAncestor _ 16 _ _ i _ = _
  unfold recordAncestor
  rw [vv,salt,pp,← ok.2.2 i]
  have b : i.val<16777216 := i.isLt
  have calcHeap := reconstruct_heap_ancestor o.compression (hnode s) LENGTH ok.2.1 16 (LENGTH+i.val)
    (by change 16777216+i.val<2*16777216; omega) (by change 65536≤16777216+i.val; omega)
  apply calcHeap.trans; apply congrArg (hnode s)
  change (16777216+i.val)/65536=256+i.val/65536; omega


private theorem found (input : CheckInput) (u r : Nat) (h : firstAt input u=some r) :
    r<128 ∧ openingIndex input.positions r/65536=u := by
  unfold firstAt PairCap.firstAt at h
  have hit := List.find?_some (p := fun k => openingIndex input.positions k/65536 == u) h
  exact ⟨List.mem_range.mp (List.mem_of_find?_eq_some h),beq_iff_eq.mp hit⟩

private theorem absent (input : CheckInput) (u : Nat) (h : firstAt input u=none) :
    ∀ r<128, openingIndex input.positions r/65536≠u := by
  intro r hr same
  have no := List.find?_eq_none.mp h r (List.mem_range.mpr hr)
  exact no (beq_iff_eq.mpr same)

private theorem noOverride {α : Type} (bucket : Nat → Nat) (repl : Nat → α) (p n : Nat)
    (miss : ∀ r<n, bucket r≠p) (fallback : α) : overrideSlot bucket repl p n fallback=fallback := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [overrideSlot,if_neg (miss n (by omega))]
    exact ih (fun r h => miss r (by omega))

private theorem fixedOverride {α : Type} (bucket : Nat → Nat) (repl : Nat → α) (p n : Nat) (d : α)
    (same : ∀ r<n, bucket r=p → repl r=d) (fallback : α) :
    overrideSlot bucket repl p n fallback = if ∃ r<n, bucket r=p then d else fallback := by
  classical
  induction n generalizing fallback with
  | zero => simp [overrideSlot]
  | succ n ih =>
    rw [overrideSlot,ih (fun r h => same r (by omega))]
    by_cases ex : ∃ r<n, bucket r=p
    · rw [if_pos ex,if_pos (by obtain ⟨r,hr,hb⟩ := ex; exact ⟨r,by omega,hb⟩)]
    · rw [if_neg ex]
      by_cases cur : bucket n=p
      · rw [if_pos cur, same n (by omega) cur,if_pos (by exact ⟨n,by omega,cur⟩)]
      · rw [if_neg cur,if_neg (by rintro ⟨r,hr,hb⟩; rcases Nat.lt_succ_iff_lt_or_eq.mp hr with lt|rfl
                                  · exact ex ⟨r,lt,hb⟩
                                  · exact cur hb)]

private theorem suppliedHonest (s : MachineState) (m : Message) (ps : Positions) (b : ps.card=BATCH)
    (p : Nat) (bp : p<128) :
    supplied (honestInput s m ps) p =
    overrideSlot (fun k => openingIndex ps k/131072) (fun k => hnode s ((256+openingIndex ps k/65536) ^^^ 1))
        p BATCH (hnode s (128+p)) := by
  unfold supplied PairCap.supplied
  rw [show 10871707680+32*p = 10871640096 + (67584+32*p) by omega,
    parsedBlock s m ps b _ (by omega),show 10871640096+(67584+32*p)=outBase+32*p by dsimp [outBase];omega]
  exact batchSlot s ps b p bp

theorem honestModel (o : Oracle) (m : Message) (s : MachineState) (ok : CommittedState o m s)
    (ps : Positions) (b : ps.card=BATCH) : BatchValid o.compression (honestInput s m ps) := by
  let input := honestInput s m ps
  let ix := fun r => openingIndex ps r
  have lower (r : Nat) (hr : r<128) : lowerHash o.compression input r=hnode s (256+ix r/65536) :=
    honestLower o s m ps ok b r hr
  have hit (u r : Nat) (eqn : firstAt input u=some r) : ix r/65536=u := (found input u r eqn).2
  have digest (u r : Nat) (eqn : firstAt input u=some r) :
      lowerHash o.compression input r=hnode s (256+u) := by rw [lower _ (found input u r eqn).1,hit _ _ eqn]
  have parent (p : Nat) (hp : p<128) : parentAt o.compression input p = hnode s (128+p) := by
    have slots := suppliedHonest s m ps b p hp
    change supplied input p = overrideSlot (fun k => ix k/131072) _ p 128 _ at slots
    have tree := ok.2.1 (128+p) (by omega) (by change 128+p<16777216;omega)
    change hnode s (128+p) = storeNode (128+p) (combine o.compression (hnode s (2*(128+p))) (hnode s (2*(128+p)+1))) at tree
    have laddr : 256+2*p=2*(128+p) := by omega
    have raddr : 256+(2*p+1)=2*(128+p)+1 := by omega
    unfold parentAt parentFrom PairCap.Children.parent childrenAt
    cases l : firstAt input (2*p) with
    | none =>
      have noL := absent input (2*p) l
      cases rr : firstAt input (2*p+1) with
      | none =>
        have noR := absent input (2*p+1) rr
        exact slots.trans (noOverride _ _ _ _ (by
          intro k hk e; have nl := noL k hk; have nr := noR k hk
          change ix k/65536≠_ at nl nr; omega) _)
      | some r =>
        have h := hit _ _ rr
        have dr := digest _ _ rr
        have ex : ∃ k<128, ix k/131072=p := ⟨r,(found input _ _ rr).1,by omega⟩
        rw [fixedOverride _ _ _ _ (hnode s (2*(128+p))) (by
          intro k hk ek
          have nl := noL k hk; change ix k/65536≠_ at nl
          have hu : ix k/65536=2*p+1 := by omega
          change hnode s ((256+ix k/65536) ^^^ 1) = _
          rw [hu,Nat.xor_one_of_odd (Nat.odd_iff.mpr (by omega))]
          congr 1 <;> omega) _,if_pos ex] at slots
        simpa [slots,dr,raddr] using tree.symm
    | some lrow =>
      have dl := digest _ _ l
      cases rr : firstAt input (2*p+1) with
      | some r => simpa [dl,digest _ _ rr,laddr,raddr] using tree.symm
      | none =>
        have noR := absent input (2*p+1) rr
        have h := hit _ _ l
        have ex : ∃ k<128, ix k/131072=p := ⟨lrow,(found input _ _ l).1,by omega⟩
        rw [fixedOverride _ _ _ _ (hnode s (2*(128+p)+1)) (by
          intro k hk ek
          have nr := noR k hk; change ix k/65536≠_ at nr
          have hu : ix k/65536=2*p := by omega
          change hnode s ((256+ix k/65536) ^^^ 1) = _
          rw [hu,Nat.xor_one_of_even (Nat.even_iff.mpr (by omega))]
          congr 1 <;> omega) _,if_pos ex] at slots
        simpa [slots,dl,laddr] using tree.symm
  constructor
  · exact (PairCap.opening_proof_length (PairCap.saved s) ps).trans (by simp [PairCap.proofBytes,b])
  · intro r hr
    let u := ix r/65536
    let p := ix r/131072
    have lookup : (firstAt input u).map (lowerHash o.compression input) = some (lowerHash o.compression input r) := by
      cases eqn : firstAt input u with
      | none => exact False.elim (absent input u eqn r hr rfl)
      | some z => simp [digest _ _ eqn,lower r hr,u]
    change (childrenAt o.compression input p).child ((ix r).testBit 16) = _
    unfold PairCap.Children.child childrenAt
    rw [Nat.testBit_eq_decide_div_mod_eq]
    by_cases right : u%2=1
    · rw [if_pos (by change decide (u%2=1)=true; simp [right])]
      simpa only [show 2*p+1=u by dsimp [p,u] at *; omega] using lookup
    · rw [if_neg (by change ¬decide (u%2=1)=true; simp [right])]
      simpa only [show 2*p=u by dsimp [p,u] at *; omega] using lookup
  · have root := heap_eq_reference o.compression 128 (capTable o.compression input) (hnode s)
      (fun p pos hp => ok.2.1 p pos (by change p<16777216; omega))
      (fun p hp => by rw [capTable,if_pos hp]; exact (parent p hp).symm) 1 (by decide) (by decide)
    exact root.symm.trans ok.1.symm
end CommitGolfCandidate.Trunc
