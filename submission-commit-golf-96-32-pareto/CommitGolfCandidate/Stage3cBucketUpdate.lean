import CommitGolfCandidate.Stage3cBucketMemory
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W Outside)
theorem lookup_other (H : Compression) (x : CheckInput) (n k : Nat) (ne : bucket x n≠k) :
    lookup H x (n+1) k=lookup H x n k:=by rw [lookup_next,if_neg ne];cases lookup H x n k <;> rfl

theorem BucketTable.repeat {H x n s} (old : BucketTable H x n s) {prev : Late.Digest} (hit : lookup H x n (bucket x n)=some prev) :
    BucketTable H x (n+1) s := by
  have same (j : Nat) : lookup H x (n+1) j=lookup H x n j:=by
    by_cases eq : bucket x n=j
    · subst j;rw [lookup_next,hit];rfl
    · exact lookup_other H x n j eq
  exact ⟨fun j h=>(old.mark j h).trans (congrArg markBit (same j).symm),fun j h d v=>old.data j h d ((same j).symm.trans v),old.blank⟩

theorem BucketWrite.frame {o s t j} (w : BucketWrite o s t j) (limit : j<512) : Outside s t marksBuf bucketSpan := by
  intro q h al sep
  have away : q<bucketAddress j ∨ bucketAddress j+32≤q:=by dsimp [bucketAddress,compBase,marksBuf,bucketSpan] at sep ⊢;omega
  have far : q<marksBuf ∨ marksBuf+512≤q:=sep.imp id (fun hi=>(by decide : marksBuf+512≤marksBuf+bucketSpan).trans hi)
  exact (w.copied.outside q h al away).trans (flag_outside s j limit q h al far)
theorem write_bucket_table (H : Compression) (x : CheckInput) (n : Nat) (o : Oracle) (s t : MachineState)
    (old : BucketTable H x n s) (w : BucketWrite o s t (bucket x n)) (absent : lookup H x n (bucket x n)=none)
    (digest : readBuffer s digestBuf 32=lower H x n) : BucketTable H x (n+1) t := by
  let j:=bucket x n
  have limit : j<512:=bucket_bound x n
  have dAlign : bucketAddress j%8=0:=by dsimp [bucketAddress,compBase];omega
  have dBound : bucketAddress j+32≤MEMORY_BYTES:=by dsimp [bucketAddress,compBase,MEMORY_BYTES];omega
  have recorded : lookup H x (n+1) j=some (lower H x n):=by rw [lookup_next,show lookup H x n j=none from absent,if_pos rfl];rfl
  have actual : readBuffer t (bucketAddress j) 32=lower H x n:=
    (copied_read (a:=digestBuf) (b:=bucketAddress j) (n:=4) w.copied (by decide) dAlign).trans
      ((Open.outside_read (flag_outside s j limit) (by decide) (by decide) digestBuf 32 (by decide) (Or.inl (by decide))).trans digest)
  refine ⟨?_,?_,?_⟩
  · intro k small
    have unchanged:=Open.outside_byte w.copied.outside dAlign (by decide) (a:=marksBuf+k)
      (by dsimp [marksBuf,MEMORY_BYTES];omega) (Or.inl (by dsimp [bucketAddress,compBase,marksBuf];omega))
    have byte:=set_byte_read s (W (marksBuf+j)) (W (marksBuf+k)) 1
    apply unchanged.trans;apply byte.trans
    by_cases same : k=j
    · subst k;rw [recorded,if_pos rfl];rfl
    · have different : W (marksBuf+k)≠W (marksBuf+j):=by
        intro e;have h:=congrArg BitVec.toNat e
        simp only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by dsimp [marksBuf];omega : marksBuf+k<2^64),
          Nat.mod_eq_of_lt (by dsimp [marksBuf];omega : marksBuf+j<2^64)] at h;omega
      rw [if_neg different,lookup_other _ _ _ _ (Ne.symm same)];exact old.mark k small
  · intro k small d found
    by_cases same : k=j
    · subst k;rw [recorded] at found;exact actual.trans (Option.some.inj found)
    · have prior:=old.data k small d ((lookup_other H x n k (Ne.symm same)).symm.trans found)
      have before:=Open.outside_read (flag_outside s j limit) (by decide) (by decide) (bucketAddress k) 32
        (by dsimp [bucketAddress,compBase,MEMORY_BYTES];omega) (Or.inr (by dsimp [bucketAddress,compBase,marksBuf];omega))
      exact (Open.outside_read w.copied.outside dAlign (by decide) (bucketAddress k) 32
        (by dsimp [bucketAddress,compBase,MEMORY_BYTES];omega) (by dsimp [bucketAddress];omega)).trans (before.trans prior)
  · intro q lo hi al
    exact (w.frame limit q (by unfold saltBuf at hi;unfold MEMORY_BYTES;omega) al (Or.inr (by unfold marksBuf bucketSpan;unfold capBase at lo;omega))).trans (old.blank q lo hi al)
end CommitGolfCandidate.Chained.BinaryMachine.Check
