import CommitGolfCandidate.ReconstructedCheckRecordDecision
import CommitGolfCandidate.ReconstructedCheckRecordEvidence

namespace CommitGolfCandidate.Reconstruction.CheckRecordLedger
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding CheckRecordABI CheckRecordSpec CheckRecordSlots CheckRecordDecision CheckWalkValues
open TwoPermutationPrototype TwoPermutationPrototype.Sampling
set_option maxRecDepth 12500
set_option maxHeartbeats 1200000

abbrev Ordinal (i : CheckInput) := Fin i.positions.card

def bits (i : CheckInput):=Wire.unpackBytes i.proof
def index (input : CheckInput) (i : Ordinal input) := (position input i).val
def message (input : CheckInput) (i : Ordinal input) := input.values (position input i)
def slot (input : CheckInput) (i : Ordinal input) := heap (index input i) 9
def parse (o : Oracle) (input : CheckInput) (i : Ordinal input) := lower o (index input i) (bits input) (cursor i) (entryWords (message input i))
def view (o : Oracle) (input : CheckInput) (i : Ordinal input) := (parse o input i).1
def log (o : Oracle) (input : CheckInput) (i : Ordinal input) := rows o (index input i) (bits input) (cursor i) (entryWords (message input i))

def GoodData (o : Oracle) (input : CheckInput) := ∀ i : Ordinal input,
  (view o input i).header=[0,0,0,0] ∧ ∀ j : Ordinal input,slot input j=slot input i→(view o input j).node=(view o input i).node

structure Ledger (o : Oracle) (input : CheckInput) (ordinal : Nat) (a : Slots) (log : List PublicRow) : Prop where
  record : ∀ i : Ordinal input,i.val<ordinal→a (slot input i)=some (view o input i).node ∧
    CheckRecordEvidence.Evidence o (index input i) (message input i) (view o input i).node log
  origin : ∀ k v,a k=some v→∃ i : Ordinal input,i.val<ordinal ∧ slot input i=k ∧ (view o input i).node=v
  canonical : ∀ k v,a k=some v→Canonical 9 v

theorem empty (o : Oracle) (input : CheckInput) : Ledger o input 0 (fun _=>none) [] := by
  constructor
  · intro i h;omega
  · intro k v h;cases h
  · intro k v h;cases h

theorem compatible {o : Oracle} {input : CheckInput} {a : Slots} {ord : Nat} {rs : List PublicRow}
    (l : Ledger o input ord a rs) (i : Ordinal input) (ok : GoodData o input) : Compatible a (slot input i) (view o input i).node := by
  cases h : a (slot input i) with
  | none=>exact Or.inl h
  | some v=>
    obtain ⟨j,_,same,val⟩:=l.origin _ _ h
    have equal : v=(view o input i).node:=val.symm.trans ((ok i).2 j same)
    exact Or.inr (h.trans (congrArg some equal))

theorem extend {o : Oracle} {input : CheckInput} {a : Slots} {old : List PublicRow} (i : Ordinal input) (l : Ledger o input i a old)
    (valid : Compatible a (slot input i) (view o input i).node)
    (can : Canonical 9 (view o input i).node)
    (path : CheckRecordEvidence.Evidence o (index input i) (message input i) (view o input i).node (log o input i)) :
    Ledger o input (i.val+1) (replace a (slot input i) (view o input i).node) (old++log o input i) := by
  constructor
  · intro j hj
    by_cases last : j=i
    · subst j;exact ⟨by simp [replace],CheckRecordEvidence.mono path (fun _ h=>List.mem_append_right _ h)⟩
    · have earlier : j.val < i.val:=by have ne : j.val ≠ i.val:=fun e=>last (Fin.ext e);omega
      obtain ⟨slotValue,evidence⟩:=l.record j earlier
      refine ⟨?_,CheckRecordEvidence.mono evidence (fun _ h=>List.mem_append_left _ h)⟩
      by_cases hit : slot input j=slot input i
      · rw [replace,ite_eq_left hit];rw [hit] at slotValue
        rcases valid with absent|existing
        · rw [slotValue] at absent;contradiction
        · exact existing.symm.trans slotValue
      · rw [replace,ite_eq_right hit];exact slotValue
  · intro k v h
    by_cases hit : k=slot input i
    · subst k;rw [replace,ite_eq_left rfl,Option.some.injEq] at h;exact ⟨i,by omega,rfl,h⟩
    · rw [replace,ite_eq_right hit] at h
      obtain ⟨j,earlier,key,value⟩:=l.origin _ _ h;exact ⟨j,by omega,key,value⟩
  · intro k v h;by_cases hit : k=slot input i
    · rw [replace,ite_eq_left hit,Option.some.injEq] at h;exact h ▸ can
    · rw [replace,ite_eq_right hit] at h;exact l.canonical k v h

theorem beforeCap {o : Oracle} {input : CheckInput} {a : Slots} {ord : Nat} {rs : List PublicRow}
    (l : Ledger o input ord a rs) (k : Nat) (low : k<512) : a k=none := by
  cases h : a k with
  | none=>rfl
  | some v=>
    obtain ⟨i,_,slot,_⟩:=l.origin k v h
    have range:=(hashRange (index input i)).1;change 512≤CheckRecordLedger.slot input i at range;omega

end CommitGolfCandidate.Reconstruction.CheckRecordLedger
