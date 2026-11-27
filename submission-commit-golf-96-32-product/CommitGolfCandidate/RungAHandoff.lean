import CommitGolfCandidate.RungAGroup
import CommitGolfCandidate.S4OpenEntry
namespace CommitGolfCandidate.RungA
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open S4.Machine (W byte indexBase)
open S4.Open (initial indices)
open Late (Trapdoor slice nodeAddress levelCount)
def savedTD (s : MachineState) : Trapdoor:=readBuffer s tdAddress 3355443200
theorem savedSlice (s : MachineState) (a n : Nat) (lo:tdAddress ≤ a) (hi:a+n ≤ indexBase) :
    slice (savedTD s) a n=readBuffer s a n := by
  unfold slice savedTD
  exact (read_buffer_slice s tdAddress 3355443200 (a-tdAddress) n (by unfold tdAddress indexBase at *;omega)).trans
    (congrArg (fun v=>readBuffer s v n) (show tdAddress+(a-tdAddress)=a by omega))

private theorem readOne (s : MachineState) (a : Nat) : readBuffer s a 1=byte s a := by
  exact (show (readBuffer s a 1).extractLsb' (8*0) 8=readBuffer s a 1 from BitVec.extractLsb'_eq_self).symm.trans (read_buffer_byte s a 1 0 (by decide))

theorem savedRebuilt {H td ps s} (view : View H td ps (selected .twentyFour ps) s) :
    Rebuilt .twentyFour H ps td (savedTD s) := by
  constructor
  · intro h j hit;obtain ⟨_,real⟩:=view.valid h j hit
    rw [savedSlice];exact view.nodes _ _ hit
    · unfold tdAddress nodeAddress;omega
    · have:=Late.parent_below_salts h j real;unfold Late.rowBase indexBase at *;omega
  · intro a lo hi outside
    have cap:a+1 ≤ indexBase:=by unfold tdAddress indexBase at *;omega
    rw [savedSlice s a 1 lo cap,←S4.Open.fixed_in td ps a 1 lo cap,readOne,readOne]
    exact view.frame a (by unfold indexBase at cap;omega) outside

private theorem outsideInitial (a : Nat) (ba:a<2^36) (notTD : a<tdAddress ∨ indexBase≤a) (x y : Trapdoor) (ps : Positions) :
    byte (initial x ps) a=byte (initial y ps) a := by
  rw [show byte (initial x ps) a=inputByte Late.submission .opening (x,ps) a from initial_input_byte _ _ _ _ (by omega),
    show byte (initial y ps) a=inputByte Late.submission .opening (y,ps) a from initial_input_byte _ _ _ _ (by omega)]
  let k:=positionsBuffer indexBase ps
  have skip (t : Trapdoor) : ¬((fixedBuffer tdAddress t).address≤a ∧ a<(fixedBuffer tdAddress t).address+(fixedBuffer tdAddress t).length):=by
    change ¬(tdAddress ≤ a ∧ a<tdAddress+3355443200);unfold tdAddress indexBase at *;omega
  unfold inputByte
  change (match ([fixedBuffer tdAddress x,k].find? _) with | some b=>b.byteAt (a-b.address) | none=>_) =
    (match ([fixedBuffer tdAddress y,k].find? _) with | some b=>b.byteAt (a-b.address) | none=>_)
  simp only [List.find?_cons,skip,decide_false,Bool.false_eq_true,ite_false]

theorem savedBytes {H td ps s} (view : View H td ps (selected .twentyFour ps) s) (a : Nat) (bound:a<2^36) :
    byte s a=byte (initial (savedTD s) ps) a := by
  by_cases included : tdAddress ≤ a ∧ a < indexBase
  · have lim : a+1 ≤ indexBase:=by omega
    exact (readOne s a).symm.trans ((savedSlice s a 1 included.1 lim).symm.trans
      ((S4.Open.fixed_in (savedTD s) ps a 1 included.1 lim).symm.trans (readOne _ a)))
  · have out : a<tdAddress ∨ indexBase≤a:=by omega
    apply (view.frame a bound ?_).trans (outsideInitial _ bound out td _ ps)
    intro h j sel
    have upper:=Late.parent_below_salts h j (view.valid _ _ sel).2
    unfold Late.rowBase at upper
    have lower : tdAddress≤nodeAddress h j:=by unfold nodeAddress tdAddress;omega
    unfold indexBase at out;omega

theorem selectedSeen (ps : Positions) (h j : Nat) : seen (indices ps) h j ↔ selected .twentyFour ps h j := by
  unfold seen inGroup selected
  constructor
  · rintro ⟨i,mem,b,valid,g⟩
    exact ⟨b,valid,i,(by simpa [indices] using mem),g.symm⟩
  · rintro ⟨b,valid,i,mem,g⟩
    exact ⟨i,(by simpa [indices] using mem),b,valid,g.symm⟩
end CommitGolfCandidate.RungA
