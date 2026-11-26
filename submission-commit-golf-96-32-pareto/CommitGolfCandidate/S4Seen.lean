import CommitGolfCandidate.S4Frames
import CommitGolfCandidate.S4Stores
import CommitGolfCandidate.S4ReadField
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (Digest)
theorem servedOther (H : Compression) (v : View) (n u : Nat) (ne : bucket v n≠u) :
    served H v (n+1) u=served H v n u := by
  unfold served;rw [firstNext,if_neg ne];cases firstBefore v n u <;> rfl

theorem Seen.sameMem {H : Compression} {v : View} {n : Nat} {s t : MachineState} (old : Seen H v n s) (eqv : t.mem=s.mem) :
    Seen H v n t := by
  refine ⟨fun j bj=>?_,fun j bj d h=>(read_buffer_memory_congr t s eqv _ _).trans (old.leaves j bj d h),old.agree⟩
  simpa only [byte,MachineState.getByte,MachineState.getMem,eqv] using old.flags j bj

theorem Seen.scratch {H : Compression} {v : View} {n : Nat} {s t : MachineState} (old : Seen H v n s)
    (frame : SameOutside s t 256 352) : Seen H v n t:=by
  refine ⟨fun j bj=>(frame _ (by omega) (Or.inr (by omega))).trans (old.flags j bj),?_,old.agree⟩
  intro j bj d h;exact (frame.read (by omega) (Or.inr (by omega))).trans (old.leaves j bj d h)

theorem Seen.duplicate {H : Compression} {v : View} {n : Nat} {s : MachineState} (old : Seen H v n s)
    (hit : served H v n (bucket v n)=some (lower .packed H v n)) : Seen H v (n+1) s := by
  have same (j : Nat) : served H v (n+1) j=served H v n j:=by
    by_cases eqv : j=bucket v n
    · subst j;exact (servedKeeps _ _ _ _ _ hit).trans hit.symm
    · exact servedOther _ _ _ _ (Ne.symm eqv)
  exact ⟨fun j bj=>by rw [same];exact old.flags j bj,fun j bj d h=>old.leaves j bj d ((same j) ▸ h),
    agreesNext _ _ _ old.agree (fun d e=>Option.some.inj (e.symm.trans hit))⟩

theorem Seen.insert {H : Compression} {v : View} {n : Nat} {s t : MachineState} (old : Seen H v n s)
    (empty : served H v n (bucket v n)=none)
    (flagged : ∀ j<342,byte t (768+j)=if j=bucket v n then 1 else byte s (768+j))
    (saved : ∀ j<342,readBuffer t (2048+32*j) 32=if j=bucket v n then lower .packed H v n else readBuffer s (2048+32*j) 32) :
    Seen H v (n+1) t := by
  have new :=servedFirst H v n (bucket v n) empty
  rw [if_pos rfl] at new
  refine ⟨?_,?_,agreesNext _ _ _ old.agree (fun d e=>by rw [empty] at e;contradiction)⟩
  · intro j bj;rw [flagged j bj];by_cases e : j=bucket v n
    · subst j;rw [if_pos rfl,new];rfl
    · rw [if_neg e,servedOther _ _ _ _ (Ne.symm e)];exact old.flags j bj
  · intro j bj d h;rw [saved j bj];by_cases e : j=bucket v n
    · subst j;rw [if_pos rfl,new] at *;exact Option.some.inj h
    · rw [if_neg e];rw [servedOther _ _ _ _ (Ne.symm e)] at h;exact old.leaves j bj d h

theorem changedSlot {H : Compression} {v : View} {n : Nat} {s u t : MachineState}
    (old : Seen H v n s) (empty : served H v n (bucket v n)=none) (bk : bucket v n<342)
    (val : readBuffer s 256 32=lower .packed H v n)
    (flag : Wrote s u (768+bucket v n) 1 (fun _=>1))
    (save : Moved u t 256 (2048+32*bucket v n) 32) : Seen H v (n+1) t := by
  apply old.insert empty
  · intro j bj
    rw [save.frame (768+j) (by omega) (Or.inl (by omega)),flag _ (by omega)]
    by_cases e : j=bucket v n
    · rw [if_pos (by omega),if_pos e]
    · rw [if_neg (by omega),if_neg e]
  · intro j bj;by_cases e : j=bucket v n
    · subst j;rw [if_pos rfl];exact (save.read (by omega)).trans ((flag.away (by decide) (Or.inl (by omega))).trans val)
    · rw [if_neg e];exact (save.away (by omega) (by omega)).trans (flag.away (by omega) (Or.inr (by omega)))

end CommitGolfCandidate.S4.Machine
