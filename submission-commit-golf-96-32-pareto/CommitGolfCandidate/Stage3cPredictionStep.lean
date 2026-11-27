import CommitGolfCandidate.Stage3cForecast
set_option Elab.async false
namespace CommitGolfCandidate.Chained.Fixed
open CommitGolf OracleComp OracleSpec

theorem repeat_valid {limit known : Nat} {enc} {s : State} {q : PublicSpec.Domain}
    (v : Valid limit enc s known) (skip : kind limit enc s q=none) :
    Valid limit enc (finish limit enc s q s.trace) (known+1) := by
  constructor
  · exact v.available.trans (by omega)
  · change Weighted.work calls (Weighted.advance s.counts (kind limit enc s q))≤limit
    simpa [skip,Weighted.advance] using v.work
  · intro room good safe
    have oldSafe : ¬s.won := fun win=>safe (Or.inl win)
    have facts:=v.track room good oldSafe
    exact ⟨(by simpa [finish,skip,Weighted.advance] using facts.1),facts.2⟩

theorem append_valid {limit known : Nat} {enc} {s : State} {x : Input} (out : Output)
    (missing : ¬∃j,s.trace.input j=x) (small : 2*limit<2^256) (v : Valid limit enc s known) :
    Valid limit enc (finish limit enc s (.inl x) (s.trace.insert x out missing)) (known+1) := by
  let fresh := fun j (eq : s.trace.input j=x) => missing ⟨j,eq⟩
  constructor
  · exact Nat.succ_le_succ v.available
  · exact forecast small v (.inl x)
  · intro room good safe
    have size : s.trace.size+1≤limit := room
    have oldGood : Good enc s.trace := good_of_append enc s.trace x out fresh good
    have oldSafe : ¬ s.won := fun e => safe (Or.inl e)
    have live : Live limit enc s := ⟨by omega,oldGood,oldSafe⟩
    obtain ⟨counts,_⟩:=v.track (by omega) oldGood oldSafe
    refine ⟨?_,fun hit=>safe (Or.inr ⟨by omega,good,hit⟩)⟩
    funext h
    change Weighted.advance s.counts (kind limit enc s (.inl x)) h=_
    simp only [kind,if_pos live,dif_neg missing,advance_bump,counts]
    exact (counter_update (fresh:=fresh) out good (by omega) h).symm

theorem append_loss {limit known : Nat} {enc} {s : State} {x : Input}
    (missing : ¬∃j,s.trace.input j=x) (live : Live limit enc s) (small : 2*limit<2^256)
    (v : Valid limit enc s known) :
    Pr{let reply←$ᵗ Output}[(finish limit enc s (.inl x) (s.trace.insert x reply missing)).won] ≤
      Weighted.hazard width s.counts (kind limit enc s (.inl x)) := by
  let fresh:=fun j (e : s.trace.input j=x)=>missing ⟨j,e⟩
  obtain ⟨counts,safe⟩:=v.track live.1.le live.2.1 live.2.2
  have room:=live.1
  have ref:=fresh_final_hazard (input:=x) (fresh:=fresh) live.2.1 (by omega) safe
    (show ∀ h, width h≤256 by decide +kernel)
  have same (r : Output) : (finish limit enc s (.inl x) (s.trace.insert x r missing)).won ↔
      Good enc (s.trace.append x r fresh) ∧ FinalCollision enc calls width (s.trace.append x r fresh) := by
    change (s.won ∨ s.trace.size<limit ∧ _) ↔ _;simp only [live.2.2,false_or,room,true_and];rfl
  simp_rw [same]
  simp only [kind,if_pos live,dif_neg missing,counts]
  apply ref.trans_eq
  unfold finalHazard Weighted.hazard
  cases prediction enc calls s.trace x fresh <;> rfl
end CommitGolfCandidate.Chained.Fixed
