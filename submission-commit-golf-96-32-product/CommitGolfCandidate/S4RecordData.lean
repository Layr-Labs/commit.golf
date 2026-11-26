import CommitGolfCandidate.S4OutputFrame
import CommitGolfCandidate.S4FieldMath
namespace CommitGolfCandidate.S4.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (Trapdoor Digest)
open Machine (W byte wordAt indexBase proofBase)

def placeAt : Nat→Place | 0=>none | n+1=>some ((n+1)-2,if n+1=2 then 1 else 0)
def payload (td : Trapdoor) (b : Bool) (i : Index) (q : Nat) :=
  mainBytes (field td b i (placeAt q))
def recordPrefix (td : Trapdoor) (b : Bool) (i : Index) (q : Nat) := (List.range q).flatMap (payload td b i)

private theorem placeDirectory : ∀ b : Bool,places b=(List.range (fieldsIn b)).map placeAt := by decide

theorem completeRecord (td : Trapdoor) (b : Bool) (i : Index) : recordPrefix td b i (fieldsIn b)=rawRecord td b i := by
  rw [rawRecord,placeDirectory,List.flatMap_map];rfl

theorem payloadSize (td : Trapdoor) (b : Bool) (i : Index) (q : Nat) (bound : q<fieldsIn b) :
    (payload td b i q).length=widthAt b q := by
  cases q with
  | zero=>simp only [payload,placeAt,field,mainBytes,List.length_map,List.length_range];rfl
  | succ n=>
    simp only [payload,placeAt,field,mainBytes,List.length_map,List.length_range]
    have table : ∀ b : Bool,∀ q : Fin 26,0<q.val → q.val<fieldsIn b →
        (if b then bits .byte (q.val-2) else 256)/8=widthAt b q:=by decide
    have lim : n+1<26:=by unfold fieldsIn at bound;split at bound <;> omega
    exact table b ⟨n+1,lim⟩ (Nat.succ_pos _) bound

theorem prefixStep (td : Trapdoor) (b : Bool) (i : Index) (q : Nat) :
    recordPrefix td b i (q+1)=recordPrefix td b i q++payload td b i q := by
  simp only [recordPrefix,List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]

theorem fieldBounds (b : Bool) (q : Nat) (i : Index) (bq : q<fieldsIn b) :
    tdBase≤targetAddr i q ∧ targetAddr i q+32 ≤ indexBase ∧ targetAddr i q%8=0 := by
  by_cases z : q=0
  · subst q;have bound:=i.isLt;change i.val<16777216 at bound
    change tdBase≤Late.saltAddress i ∧ Late.saltAddress i+32 ≤ indexBase ∧ Late.saltAddress i%8=0
    unfold Late.saltAddress tdBase indexBase Late.rowBase;split <;> omega
  · let h:=q-2
    have ht : h<24:=by unfold fieldsIn at bq;dsimp [h];split at bq <;> omega
    let p:=nodeIndex i.val (h+1);let k:=(childPos i.val h+(if q=2 then 1 else 0)+1)%radix h
    have hk : k<3:=by
      have r : 0<radix h ∧ radix h≤3:=by unfold radix;split <;> decide
      exact (Nat.mod_lt _ r.1).trans_le r.2
    have bp : p<Late.levelCount (h+1):=by rw [Late.levelCount,Nat.min_eq_left (by omega)];exact indexInside i _
    have row:=Late.row_after h p ht bp
    have top:=Late.padded_region (h+1)
    have al:=Late.rowAligned h p
    rw [targetAddr,if_neg z]
    change tdBase≤Late.rowAddress h p+32*k ∧ Late.rowAddress h p+32*k+32 ≤ indexBase ∧ (Late.rowAddress h p+32*k)%8=0
    refine ⟨by unfold tdBase Late.rowAddress;omega,?_,by omega⟩
    unfold indexBase Late.rowBase at *;omega

theorem sourceField (td : Trapdoor) (ps : Positions) (b : Bool) (i : Index) (q : Nat) (s : MachineState)
    (src : Sources td ps s) (bound : q<fieldsIn b) : Contains s (targetAddr i q) (payload td b i q) := by
  obtain ⟨lo,hi,_⟩:=fieldBounds b q i bound
  cases q with
  | zero=>exact saltRead (src.fixed _ 24 lo (by omega))
  | succ n=>
    let h:=n+1-2
    have sizes : ∀ b : Bool,∀ q : Fin 26,0<q.val → q.val<fieldsIn b →
        (if b then bits .byte (q.val-2) else 256)=8*widthAt b q ∧ widthAt b q≤32 := by decide
    have lim : n+1<26:=by unfold fieldsIn at bound;split at bound <;> omega
    obtain ⟨eqv,small⟩:=sizes b ⟨n+1,lim⟩ (Nat.succ_pos _) bound
    change Contains s _ (mainBytes ((if b then bits .byte h else 256),Late.slice td (targetAddr i (n+1)) 32))
    change (if b then bits .byte h else 256)=_ at eqv
    rw [eqv];exact fieldRead small (src.fixed _ 32 lo hi)

theorem wordExact (s : MachineState) (a : Nat) (al : a%8=0) : wordAt s a=readBuffer s a 8 := by
  have take:=read_buffer_slice s a 32 0 8 (by decide)
  have w:=read_digest_word s a 0 al (by decide)
  exact w.symm.trans take

theorem Sources.index {td : Trapdoor} {ps : Positions} {s : MachineState} (src : Sources td ps s)
    (r : Nat) (br : r<ps.card) : wordAt s (indexBase+8*r)=W (recordIndex ps r).val := by
  have bound : ps.card≤LENGTH:=by simpa using Finset.card_le_univ ps
  change ps.card≤16777216 at bound
  have al : (indexBase+8*r)%8=0:=by unfold indexBase;omega
  rw [wordExact _ _ al,src.read _ 8 (by unfold tdBase indexBase;omega) (by unfold indexBase Machine.valueBase;omega),←wordExact _ _ al]
  exact index_loaded td ps r (by change r<(ps.sort (·≤·)).length;simpa using br)
end CommitGolfCandidate.S4.Open
