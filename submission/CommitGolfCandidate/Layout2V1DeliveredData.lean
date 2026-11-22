import CommitGolfCandidate.Layout2TableData
import CommitGolfCandidate.Layout2V1Bank1
import CommitGolfCandidate.Layout2V1Bank2
import CommitGolfCandidate.Layout2V1Bank3
import CommitGolfCandidate.Layout2V1Bank4
namespace CommitGolfCandidate.Layout2
open CommitGolf
open CommitGolfCandidate.Layout2Helpers (pget pget_get)
set_option maxRecDepth 22000
set_option maxHeartbeats 1800000
theorem v1_entry (r i : Nat) (lo : 1≤r) (hi : r≤4) (inside : i<4272*r) :
    decTables r i<4272*r ∧
      pget K1Artifact.checkData (tableOffset r+2*i)+256*pget K1Artifact.checkData (tableOffset r+2*i+1)=decTables r i := by
  have ok : entryCheck r i=true := by
    interval_cases r
    · exact bank_1 i inside
    · exact bank_2 i inside
    · exact bank_3 i inside
    · exact bank_4 i inside
  simpa only [entryCheck,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] using ok

theorem v1_delivered_wellFormed : WellFormed decTables :=
  fun r lo hi i inside=>(v1_entry r i lo hi inside).1

private theorem bank_partition (k : Nat) (hk : k<85440) :
    let r:=multiplicity k
    1≤r ∧ r≤4 ∧ tableOffset r≤k ∧ k<tableOffset r+2*(4272*r) ∧ tableOffset r%2=0 := by
  dsimp only
  unfold multiplicity;split_ifs <;> norm_num [tableOffset] <;> omega

private theorem bank_end (r : Nat) (lo : 1≤r) (hi : r≤4) : tableOffset r+2*(4272*r)≤85440 := by
  interval_cases r <;> decide

private theorem byte_fit (j : Nat) (hj : j<85440) : pget K1Artifact.checkData j<256 := by
  rw [←pget_get K1Artifact.checkData ⟨j,by omega⟩]
  exact BitVec.isLt _

attribute [local irreducible] decTables K1Artifact.checkData

theorem v1_physical (k : Nat) (hk : k<85440) :
    pget K1Artifact.checkData k=tableByte decTables k := by
  let r:=multiplicity k
  let bankStart:=tableOffset r
  let i:=(k-bankStart)/2
  obtain ⟨lo,hi,start,stop,even⟩:=bank_partition k hk
  change bankStart≤k at start
  change k<bankStart+2*(4272*r) at stop
  change bankStart%2=0 at even
  have iFits : i<4272*r := by dsimp [i];omega
  have e:= (v1_entry r i lo hi iFits).2
  let a:=bankStart+2*i
  have finish : a+1<85440 := by
    have bound : bankStart+2*(4272*r)≤85440 := bank_end r lo hi
    dsimp [a];omega
  have v0:=byte_fit a (by omega)
  have v1:=byte_fit (a+1) finish
  change pget K1Artifact.checkData a+256*pget K1Artifact.checkData (a+1)=decTables r i at e
  change pget K1Artifact.checkData k=if k%2=0 then decTables r i%256 else decTables r i/256%256
  split
  · rename_i evenK
    have eq : k=a := by dsimp [a,i];omega
    exact (congrArg (pget K1Artifact.checkData) eq).trans (by omega)
  · rename_i oddK
    have eq : k=a+1 := by dsimp [a,i];omega
    exact (congrArg (pget K1Artifact.checkData) eq).trans (by omega)

end CommitGolfCandidate.Layout2
