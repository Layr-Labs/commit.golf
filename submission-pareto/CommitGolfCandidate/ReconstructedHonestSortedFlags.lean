import CommitGolfCandidate.ReconstructedHonestNameKernel
import CommitGolfCandidate.ReconstructedFrontier

namespace CommitGolfCandidate.Reconstruction.HonestSortedFlags
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 HonestNames HonestFlagState
open HonestFlagEffect (Effect flags base)
open HonestRanges (Contains)

attribute [local irreducible] ArtifactEncoding.decode execute
set_option maxRecDepth 8192

theorem mark_address (v : Values) (p : Index) (loaded : v.position=W p.val) :
    HonestNameKernel.markAddr v=W (base+(512+p.val/32768)) := by
  change ((v.position+16777216) >>> 15)+4259840=W (base+(512+p.val/32768))
  have bound := p.isLt
  change p.val<16777216 at bound
  have low : (W p.val+16777216).toNat=p.val+16777216 := by
    rw [BitVec.toNat_add,show (W p.val).toNat=p.val from Nat.mod_eq_of_lt (by omega),
      show (16777216:Word).toNat=16777216 from rfl,Nat.mod_eq_of_lt (by omega)]
  have shifted : ((W p.val+16777216) >>> (15:Nat)).toNat=512+p.val/32768 := by
    rw [BitVec.toNat_ushiftRight,low,Nat.shiftRight_eq_div_pow,Nat.add_comm p.val]
    exact (Frontier.heap_endpoint p).1
  rw [loaded]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add,shifted,show (4259840:Word).toNat=4259840 from rfl]
  change (512+p.val/32768+4259840)%2^64=(4259840+(512+p.val/32768))%2^64
  rw [Nat.add_comm (512+p.val/32768)]

theorem flags_length (xs : List Index) : (Frontier.flags xs).length=512 := by
  have fold (ys : List (Fin (2^24))) (bs : List Bool) : (ys.foldl Frontier.mark bs).length=bs.length := by
    induction ys generalizing bs with
    | nil => rfl
    | cons head tail ih => simp only [List.foldl_cons,ih,Frontier.mark,List.length_set]
  exact (fold xs _).trans (List.length_replicate)

def prefixFlags (ps : Positions) (i : Nat) := Frontier.flags ((ps.sort (· ≤ ·)).take i)
def current (bs : List Bool) (s : MachineState) := Initial (fun k => bs[k]?.getD false) s

theorem first (trap : HonestInputs.Trapdoor) (ps : Positions) (pos : 0<ps.card) :
    current (prefixFlags ps 0) (HonestInputs.first trap ps) := by
  refine ⟨fun k low => before trap ps pos k (by omega),?_⟩
  intro k low
  have prior := before trap ps pos (512+k) (by omega)
  change atByte _ (512+k)=code ((List.replicate 512 false)[k]?.getD false)
  rw [prior,List.getElem?_replicate_of_lt low]; rfl

private theorem contained (k : Nat) (h : k<1024) : Contains flags (W (base+k)) := by
  simp only [Contains,flags,BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by dsimp [base]; omega)]
  omega

theorem write {s t : MachineState} (bs : List Bool) (size : bs.length=512) (p : Index)
    (known : current bs s) (effect : Effect s t (some (W (base+(512+p.val/32768))))) :
    current (Frontier.mark bs p) t := by
  have inside : p.val/32768 < 512 := (Frontier.heap_endpoint p).2
  have inj (k : Nat) (hk : k<1024) : W (base+(512+p.val/32768))=W (base+k) ↔ k=512+p.val/32768 := by
    constructor
    · intro h
      have eq := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat] at eq
      rw [Nat.mod_eq_of_lt (by dsimp [base];omega),Nat.mod_eq_of_lt (by dsimp [base];omega)] at eq
      omega
    · intro eq; rw [eq]
  refine ⟨?_,?_⟩
  · intro k hk
    have h := effect _ (contained k (by omega))
    simp only [Option.some.injEq,inj k (by omega),ite_eq_right (show k≠512+p.val/32768 by omega)] at h
    exact h.trans (known.1 k hk)
  · intro k hk
    have h := effect _ (contained (512+k) (by omega))
    simp only [Option.some.injEq,inj (512+k) (by omega),Nat.add_right_inj] at h
    by_cases hit : k=p.val/32768
    · subst k
      have valid : p.val/32768 < bs.length := size ▸ inside
      simp only [Frontier.mark,List.getElem?_set_self valid,Option.getD_some]
      change t.getByte _=1
      simpa only [ite_true] using h
    · have out := (by simpa only [ite_eq_right hit] using h : t.getByte _=s.getByte _)
      exact (out.trans (known.2 k hk)).trans (by simp only [Frontier.mark,List.getElem?_set_ne (Ne.symm hit)])

theorem advance {s t : MachineState} (ps : Positions) (i : Nat) (hi : i<ps.card) (v : Values)
    (loaded : v.position=W ((ps.sort (·≤·))[i]'(by simpa using hi)).val)
    (known : current (prefixFlags ps i) s) (effect : Effect s t (some (HonestNameKernel.markAddr v))) :
    current (prefixFlags ps (i+1)) t := by
  let xs : List (Fin (2^24)) := ps.sort (·≤·)
  have h : i<(ps.sort (·≤·)).length := by simpa using hi
  change i<xs.length at h
  change current (Frontier.flags (xs.take (i+1))) t
  rw [List.take_succ_eq_append_getElem h]
  change current ((xs.take i ++ [xs[i]]).foldl Frontier.mark _) t
  rw [List.foldl_append]
  exact write (prefixFlags ps i) (flags_length _) xs[i] known (by rwa [←mark_address v xs[i] loaded])

theorem finish (ps : Positions) (s : MachineState) (done_ : current (prefixFlags ps ps.card) s) :
    current (Frontier.flags (ps.sort (·≤·))) s := by
  let xs : List (Fin (2^24)) := ps.sort (·≤·)
  have len : (ps.sort (·≤·)).length=ps.card := by simp
  change xs.length=ps.card at len
  change current (Frontier.flags (xs.take ps.card)) s at done_
  rw [←len,List.take_length] at done_
  exact done_

end CommitGolfCandidate.Reconstruction.HonestSortedFlags
