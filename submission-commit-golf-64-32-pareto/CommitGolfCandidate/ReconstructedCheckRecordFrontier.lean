import CommitGolfCandidate.ReconstructedCheckRecordLedger
import CommitGolfCandidate.ReconstructedCheckHonestOrdinals

namespace CommitGolfCandidate.Reconstruction.CheckRecordFrontier
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding CheckRecordABI CheckRecordSlots CheckRecordLedger
open TwoPermutationPrototype.Sampling
set_option maxRecDepth 13000
set_option maxHeartbeats 1500000

theorem exhaust (input : CheckInput) (p : {k // k∈input.positions}) : ∃ i : Ordinal input,position input i=p := by
  let xs:=input.positions.attach.sort (fun a b=>a.val≤b.val)
  have member : p∈xs:=by simp [xs]
  obtain ⟨j,bound,e⟩:=List.mem_iff_getElem.mp member
  have hj : j < input.positions.card:=by simpa [xs] using bound
  exact ⟨⟨j,hj⟩,e⟩

private theorem marked (xs : List (Fin (2^24))) (bs : List Bool) (n : Nat) (bound : n<bs.length) :
    (xs.foldl Frontier.mark bs)[n]?.getD false=true ↔ bs[n]?.getD false=true ∨ ∃ p∈xs,p.val/32768=n := by
  induction xs generalizing bs with
  | nil=>simp
  | cons p xs ih=>
    rw [List.foldl_cons,ih (Frontier.mark bs p) (by simpa [Frontier.mark] using bound)]
    by_cases same : p.val/32768=n
    · simp [Frontier.mark,same,List.getElem?_set_self bound]
    · rw [Frontier.mark,List.getElem?_set_ne same];simp [same]

private theorem sortedMem (ps : Positions) (p : Index) : p∈ps.sort (·≤·) ↔ p∈ps :=
  Finset.mem_sort (α:=Index) (s:=ps) (a:=p) (fun a b : Index=>a≤b)

theorem flags (input : CheckInput) (n : Nat) (small : n<512) :
    CapEntry.flags input.positions n=true ↔ ∃ i : Ordinal input,slot input i=512+n := by
  let xs : List (Fin (2^24)):=input.positions.sort (·≤·)
  have mag:=marked xs (List.replicate 512 false) n (by simpa using small)
  refine mag.trans ?_
  rw [List.getElem?_replicate_of_lt small]
  simp only [Option.getD_some,Bool.false_eq_true,false_or]
  have mem_iff (p : Fin (2^24)) : p∈xs ↔ p∈input.positions:=sortedMem input.positions p
  simp only [mem_iff]
  constructor
  · rintro ⟨p,mem,id⟩;obtain ⟨i,hi⟩:=exhaust input ⟨p,mem⟩
    use i;change (2^24+(position input i).val.val)/2^15=512+n
    rw [hi,(Frontier.heap_endpoint p).1,id]
  · rintro ⟨i,hi⟩
    exact ⟨index input i,(position input i).property,by
      have ep:=(Frontier.heap_endpoint (index input i)).1;change (2^24+(index input i).val)/2^15=512+n at hi;omega⟩

theorem flagsEqual {o : Oracle} {input : CheckInput} {a : Slots} {rs : List PublicRow} (h : Ledger o input input.positions.card a rs)
    (j : Nat) (small : j<512) : (a (512+j)).isSome=CapEntry.flags input.positions j := by
  apply Bool.eq_iff_iff.mpr
  rw [flags input j small]
  constructor
  · intro active;cases v : a (512+j) with
    | none=>rw [v] at active;contradiction
    | some x=>obtain ⟨i,_,k,_⟩:=h.origin _ _ v;exact ⟨i,k⟩
  · rintro ⟨i,k⟩;have v:=(h.record i i.isLt).1;rw [k] at v;rw [v];rfl

theorem honest (o : Oracle) (key : Generator.Key) (msg : Message) (input : CheckInput)
    (proof : input.proof=Wire.bytes (Encoding.fields (LeafTree.tree o key msg) input.positions (HonestDelivery.salts o key input.positions)))
    (values : ∀ p,input.values p=msg p.val) : GoodData o input := by
  intro i
  have status:=CheckHonestOrdinals.project o key msg input i proof values
  refine ⟨status.1,?_⟩
  intro j hit
  exact (CheckHonestOrdinals.project o key msg input j proof values).2.trans
    ((congrArg (LeafTree.tree o key msg 9) hit).trans status.2.symm)

theorem initial {o : Oracle} {input : CheckInput} {a : Slots} {rs : List PublicRow} {s : MachineState}
    (h : Ledger o input input.positions.card a rs) (sh : Holds s a) : HonestFlagState.Initial (CapEntry.flags input.positions) s := by
  have init:=(capStart sh (beforeCap h)).1
  refine ⟨init.1,?_⟩;intro j bound;rw [←flagsEqual h j bound];exact init.2 j bound

theorem cells {o : Oracle} {input : CheckInput} {a : Slots} {rs : List PublicRow} {s : MachineState}
    (h : Ledger o input input.positions.card a rs) (sh : Holds s a)
    (j : Nat) (small : j<512) (on : CapEntry.flags input.positions j=true) :
    ∃ i : Ordinal input,slot input i=512+j ∧ CommitParents.cell s (4194304+32*(512+j))=(view o input i).node ∧
      Canonical 9 (view o input i).node := by
  obtain ⟨i,id⟩:=(flags input j small).mp on
  have val:=(h.record i i.isLt).1;rw [id] at val
  exact ⟨i,id,physical s _ _ (sh.words _ (by omega) _ val),h.canonical _ _ val⟩

end CommitGolfCandidate.Reconstruction.CheckRecordFrontier
