import CommitGolfCandidate.ReconstructedCheckWalkStep

namespace CommitGolfCandidate.Reconstruction.CheckWalk
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding CheckRecorded CheckLayout CheckWalkValues
open TwoPermutationPrototype.Sampling
set_option maxRecDepth 17000
set_option maxHeartbeats 1550000

def idx15 (k : Nat) : Fin 15:=⟨k%15,by omega⟩

def evaluate (o : Oracle) (idx : Index) (stream : Nat) : Nat→View→View×List PublicRow
  | 0,v=>(v,[])
  | k+1,v=>
    let head:=prep o idx stream (idx15 k) v
    let tail:=evaluate o idx stream k head.1
    (tail.1,head.2++tail.2)

def fee : Nat→Nat | 0=>0 | k+1=>work (9+k)+fee k

def Lifts (o : Oracle) (idx : Index) (log : List PublicRow) (hi : Nat) (leaf cap : Binding.Digest) :=
  ∀ rows : List PublicRow,log⊆rows→∀ root : Binding.Digest,
    Binding.Path (history rows) (oracleCompression o) 9 (CheckPath.dirs idx 9) root cap →
      Binding.Path (history rows) (oracleCompression o) hi (CheckPath.dirs idx hi) root leaf

private theorem lift (o : Oracle) (idx : Index) (i : Fin 15) (leaf mid cap : Binding.Digest) (xs ys : List PublicRow)
    (next : CheckPath.Edge o xs (CheckLowerRound.depth i) (side idx ((CheckLowerRound.depth i).val+1)) leaf mid)
    (rest : Lifts o idx ys (CheckLowerRound.depth i) mid cap) :
    Lifts o idx (xs++ys) ((CheckLowerRound.depth i).val+1) leaf cap := by
  intro whole inc root p
  have m1 : xs⊆whole:=fun _ h=>inc (List.mem_append_left _ h)
  have m2 : ys⊆whole:=fun _ h=>inc (List.mem_append_right _ h)
  let edge : CheckPath.Edge o whole (CheckLowerRound.depth i) (side idx ((CheckLowerRound.depth i).val+1)) leaf mid:=
    {next with observed:=fun _ h=>m1 (next.observed h)}
  have path:=edge.extend (rest whole m2 root p)
  rw [direction idx i] at path
  exact path

theorem positive (o : Oracle) (idx : Index) (stream : Nat) (k : Nat) (v : View) (s : MachineState)
    (limited : k≤15) (good : Ready v (9+k)) (atInput : At s idx (9+k) v)
    (data : StreamMemory s stream) (tables : CheckLayout.Tables s) :
    let parsed:=evaluate o idx stream k v
    ∃ t n,n≤305*k ∧ Segment o n s t parsed.2 ∧ At t idx 9 parsed.1 ∧ Ready parsed.1 9 ∧
      Lifts o idx parsed.2 (9+k) v.node parsed.1.node ∧ parsed.2.length=fee k ∧ Untouched s t := by
  induction k generalizing s v with
  | zero=>exact ⟨s,0,by decide,empty o s,atInput,good,fun _ _ _ h=>h,rfl,fun _ _ _=>rfl⟩
  | succ k ih=>
    let i:=idx15 k
    let d:=CheckLowerRound.depth i
    have iv : i.val=k:=Nat.mod_eq_of_lt (by omega)
    have dv : d.val=9+k:=congrArg (9+·) iv
    have av : At s idx (d.val+1) v:=by rw [dv];exact atInput
    have gv : Ready v (d.val+1):=by rw [dv];exact good
    obtain ⟨u,n,nb,step,atU,⟨edge⟩,fr⟩:=CheckWalkStep.positive o idx stream i v s gv av data tables
    have au : At u idx (9+k) (prep o idx stream i v).1:=by rw [←dv];exact atU
    have gu : Ready (prep o idx stream i v).1 (9+k):=by rw [←dv];exact remains o idx stream i v gv
    have roU:=table_frame s u fr tables
    have inpU:=stream_frame s u stream fr data
    obtain ⟨t,m,mb,rest,atT,finalGood,restLifts,size,frame⟩:=ih (prep o idx stream i v).1 u (by omega) gu au inpU roU
    have lifted:=lift o idx i _ _ _ _ _ edge (by rw [dv];exact restLifts)
    have wordCount : (prep o idx stream i v).2.length=work (9+k):=by
      change (CheckParentExecution.rows _ _ 0 (work d)).length=_
      simp only [CheckParentExecution.rows,List.length_map,List.length_range',dv]
    dsimp only [evaluate]
    refine ⟨t,n+m,by omega,compose step rest,atT,finalGood,?_,?_,?_⟩
    · rw [show 9+(k+1)=d.val+1 by omega];exact lifted
    · rw [List.length_append,wordCount,size];rfl
    · intro a ha safe;exact (frame a ha safe).trans (fr a ha safe)

/-- Positive execution of all fifteen lower parent calls, with the exact 82
compression rows and a path extension for any later upper-cap transcript. -/
theorem records (o : Oracle) (idx : Index) (stream : Nat) (v : View) (s : MachineState)
    (good : Ready v 24) (atInput : At s idx 24 v) (data : StreamMemory s stream) (tables : CheckLayout.Tables s) :
    let parsed:=evaluate o idx stream 15 v
    ∃ t n,n≤4575 ∧ Segment o n s t parsed.2 ∧ At t idx 9 parsed.1 ∧ Ready parsed.1 9 ∧
      Lifts o idx parsed.2 24 v.node parsed.1.node ∧ parsed.2.length=82 ∧ Untouched s t := by
  simpa only [show 305*15=4575 by decide,show fee 15=82 by decide] using positive o idx stream 15 v s (by decide) good atInput data tables

end CommitGolfCandidate.Reconstruction.CheckWalk
