import CommitGolfCandidate.R4bSchedule
namespace CommitGolfCandidate.R4b
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open CommitGolfCandidate.S4
open S4.Open
open Machine (W Safe byte proofBase)

def tape (td : Late.Trapdoor) (ps : Positions) (k : Nat) := (returnedRecords td ps true 128)[k]?.getD 0

private theorem extend {α : Type} (xs : Nat→List α) (bound : Nat)
    (more : ∀ k,k<bound → ∃ e,xs (k+1)=xs k++e) (a b : Nat) (le : a≤b) (hi : b≤bound) :
    ∃ tail,xs b=xs a++tail := by
  induction b with
  | zero=>
    have z:a=0:=by omega
    subst a;exact ⟨[],by simp⟩
  | succ b ih=>
    by_cases e:a=b+1
    · subst a;exact ⟨[],by simp⟩
    · obtain ⟨t,eqv⟩:=ih (by omega) (by omega)
      obtain ⟨k,h⟩:=more b (by omega)
      exact ⟨t++k,by rw [h,eqv,List.append_assoc]⟩

theorem offsetMore (q : Nat) (h : q<17) :
    Open.offsetAt true q + Open.widthAt true q=Open.offsetAt true (q+1) ∧
    Open.offsetAt true q + Open.widthAt true q≤510 ∧ Open.widthAt true q≤32 :=
  (show ∀ q : Fin 17,Open.offsetAt true q+Open.widthAt true q=Open.offsetAt true (q.val+1) ∧
    Open.offsetAt true q+Open.widthAt true q≤510 ∧ Open.widthAt true q≤32 by decide) ⟨q,h⟩
theorem prefixLen (td : Late.Trapdoor) (i : Index) (q : Nat) (h : q≤17) :
    (recordPrefix td true i q).length=Open.offsetAt true q := by
  induction q with
  | zero=>rfl
  | succ q ih=>rw [prefixStep,List.length_append,ih (by omega),payloadSize _ _ _ _ (by change q<17;omega),(offsetMore q (by omega)).1]

theorem tapeSource (td : Late.Trapdoor) (ps : Positions) (batch : ps.card=128)
    (r q : Nat) (br : r<128) (bq : q<17) (s : MachineState) (src : Sources td ps s) :
    let i:=recordIndex ps r
    ∀ j,j<Open.widthAt true q →
      byte s (targetAddr i q+j)=tape td ps (510*r+Open.offsetAt true q+j) := by
  intro i j hj
  obtain ⟨tail,whole⟩:=extend (returnedRecords td ps true) 128
    (fun a ha=>⟨_,returnedStep td ps true a (by omega)⟩) (r+1) 128 (by omega) le_rfl
  rw [returnedStep td ps true r (by omega)] at whole
  obtain ⟨more,rec⟩:=extend (recordPrefix td true i) 17 (fun a _=>⟨_,prefixStep td true i a⟩) (q+1) 17 (by omega) le_rfl
  change recordPrefix td true i (fieldsIn true)=_ at rec
  rw [completeRecord,prefixStep] at rec
  change returnedRecords td ps true 128=(returnedRecords td ps true r++rawRecord td true i)++tail at whole
  rw [rec] at whole
  let pre:=returnedRecords td ps true r++recordPrefix td true i q
  let cur:=payload td true i q
  have all : returnedRecords td ps true 128=pre++(cur++(more++tail)) := by simpa only [pre,cur,List.append_assoc] using whole
  have preLen : pre.length=510*r+Open.offsetAt true q:=by
    rw [List.length_append,returnedLen _ _ _ _ (by omega),prefixLen _ _ _ (by omega)];rfl
  have valid : j<cur.length:=by rw [payloadSize _ _ _ _ bq];exact hj
  have given:=sourceField td ps true i q s src bq j valid
  rw [tape,all,←preLen,List.getElem?_append_right (by omega),Nat.add_sub_cancel_left,
    List.getElem?_append_left valid,List.getElem?_eq_getElem valid]
  exact given

theorem tapeDone {td : Late.Trapdoor} {ps : Positions} (batch : ps.card=128) {s : MachineState}
    (h : Cursor (tape td ps) 65280 s) : Contains s proofBase (returnedRecords td ps true 128) := by
  intro j inside
  have bound:=returnedLen td ps true 128 batch.symm.le
  change _=65280 at bound
  have e:=h.filled j (by change j<65280;omega)
  simpa only [tape,List.getElem?_eq_getElem inside,Option.getD_some] using e
end CommitGolfCandidate.R4b
