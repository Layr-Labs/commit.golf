import CommitGolfCandidate.S5CheckRecordInput
import CommitGolfCandidate.S5Trials
namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W Outside)
def compBase:=67584
def slotBase:=86016
def capBase:=98304
def bucket (x : CheckInput) (r : Nat):=S5.Auth.bucket (view true x) r
def lower (H : Compression) (x : CheckInput) (r : Nat):=S5.Auth.lower H (view true x) r
def lookup (H : Compression) (x : CheckInput) (n j : Nat) : Option Late.Digest :=
  ((List.range n).find? (fun r=>bucket x r==j)).map (lower H x)
def Consistent (H : Compression) (x : CheckInput) (n : Nat) :=∀ r<n,lookup H x n (bucket x r)=some (lower H x r)
def markBit (v : Option Late.Digest) : Byte :=if v.isSome then 1 else 0
def BlankTree (s : MachineState) := ∀ j,capBase≤j → j<saltBuf → j%8=0 → Open.wordAt s j=0
structure BucketTable (H : Compression) (x : CheckInput) (n : Nat) (s : MachineState) : Prop where
  mark : ∀ j<342,Open.byteAt s (marksBuf+j)=markBit (lookup H x n j)
  data : ∀ j<342,∀ v,lookup H x n j=some v → readBuffer s (compBase+32*j) 32=v
  blank : BlankTree s

theorem lookup_next (H : Compression) (x : CheckInput) (n j : Nat) :
    lookup H x (n+1) j=(lookup H x n j).or (if bucket x n=j then some (lower H x n) else none) := by
  simp only [lookup,List.range_succ,List.find?_append,List.find?_cons,List.find?_nil]
  cases (List.range n).find? (fun r=>bucket x r==j) <;> by_cases e:bucket x n=j
  all_goals first | (rw [beq_eq_false_iff_ne.mpr e];simp [e]) | simp [e]
theorem lookup_persists {H x n j d} (found : lookup H x n j=some d) {m : Nat} (le : n≤m) : lookup H x m j=some d := by
  obtain ⟨a,rfl⟩:=Nat.exists_eq_add_of_le le
  induction a with
  | zero=>exact found
  | succ a ih=>rw [←Nat.add_assoc,lookup_next,ih (by omega)];rfl
theorem consistent_next {H x n} (prev : Consistent H x n) (ok : (lookup H x n (bucket x n)).getD (lower H x n)=lower H x n) :
    Consistent H x (n+1) := by
  intro r h;by_cases same : r=n
  · subst r;rw [lookup_next,if_pos rfl];cases e:lookup H x n (bucket x n) <;> simp_all
  · exact lookup_persists (prev r (by omega)) (by omega)
theorem inconsistent {H x n k} (no : (lookup H x n (bucket x n)).getD (lower H x n)≠lower H x n) (inSet : n<k) :
    ¬Consistent H x k := by
  intro all
  cases e:lookup H x n (bucket x n) with
  | none=>rw [e] at no;exact no rfl
  | some d=>
    have same:=(lookup_persists e inSet.le).symm.trans (all n inSet)
    apply no;rw [e];exact Option.some.inj same

theorem bucket_bound (x : CheckInput) (r : Nat) : bucket x r<342:=S5.Auth.indexInside _ 15
theorem lookup_all (H : Compression) (x : CheckInput) (j : Nat) : lookup H x 128 j=S5.Auth.select (view true x) (S5.Auth.lower H (view true x)) j:=rfl
theorem batch_condition (H : Compression) (x : CheckInput) (q : Fin 4) :
    S5.Auth.BatchValid H (S5.batchView x q) x.commitment ↔ Consistent H x 128 ∧ S5.Auth.batchRoot H (S5.batchView x q)=x.commitment := by
  unfold S5.Auth.BatchValid;rw [S5.trial_consistent];rfl

theorem initial_zero (x : CheckInput) (a : Nat) (sm : a<rootBase) : byte (initial x) a=0 := by
  apply (initial_input_byte Artifact.submission .check x a (by unfold rootBase at sm;omega)).trans
  unfold inputByte
  change (match [fixedBuffer rootBase x.commitment,positionsBuffer indexBase x.positions,valuesBuffer valueBase x.positions x.values,
    (⟨proofBase,x.proof.length,fun j=>x.proof[j]?.getD 0⟩ : InputBuffer)].find? _ with
    | some b=>b.byteAt (a-b.address) | none=>if MEMORY_BYTES≤a then _ else _)=_
  have r : ¬rootBase≤a:=by omega
  have i : ¬indexBase≤a:=by unfold rootBase at sm;unfold indexBase;omega
  have v : ¬valueBase≤a:=by unfold rootBase at sm;unfold valueBase;omega
  have p : ¬proofBase≤a:=by unfold rootBase at sm;unfold proofBase;omega
  have room : ¬MEMORY_BYTES≤a:=by unfold rootBase at sm;unfold MEMORY_BYTES;omega
  simp only [List.find?_cons,fixedBuffer,positionsBuffer,valuesBuffer,r,i,v,p,false_and,decide_false,
    Bool.false_eq_true,ite_false,List.find?_nil,room]

theorem buckets_initial (H : Compression) (x : CheckInput) (s : MachineState) (mem : s.mem=(initial x).mem) :
    BucketTable H x 0 s := by
  refine ⟨?_,?_,?_⟩
  · intro j small
    change Open.byteAt s (marksBuf+j)=0
    exact (Open.byte_mem mem _).trans (initial_zero x _ (by dsimp [marksBuf,rootBase];omega))
  · intro j _ v found;cases found
  · intro j lo hi al
    apply (congrFun mem _).trans
    change (initial x).getMem (W j)=0
    apply (read_word (initial x) j al).symm.trans
    unfold readBuffer
    rw [Finset.sum_eq_zero (fun q h=>?_)];rfl
    have bound:=Finset.mem_range.mp h
    change (byte (initial x) (j+q)).toNat*_=0
    rw [initial_zero x _ (by unfold rootBase;unfold saltBuf at hi;omega)];simp
end CommitGolfCandidate.S5Machine.Check
