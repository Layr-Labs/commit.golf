import CommitGolfCandidate.PhaseWalk

namespace TwoPermutationPrototype.PhaseOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CommitGolfCandidate
open GroupedOpening
set_option maxRecDepth 22000
set_option maxHeartbeats 3000000

def groupOld (s : MachineState) : Nat → MachineState
  | 0 => saltStart s
  | j+1 => if h : j<3 then groupStep ⟨j,h⟩ (groupOld s j) else groupOld s j

def upperOld (s : MachineState) : Nat → MachineState
  | 0 => recordPrefix s
  | j+1 => if h : j<14 then siblingBlock ⟨j,h⟩ (upperOld s j) else upperOld s j

def atCopy (s : MachineState) (f : Fin 18) : MachineState :=
  if z : f.val=0 then nonceSetup s
  else if h : f.val<4 then quartetHead ⟨f.val-1,by omega⟩ (groupOld s (f.val-1))
  else headPrefix (upperOld s (f.val-4)) 3

def afterCopy (s : MachineState) (f : Fin 18) : MachineState := copyState (oldSite f) (atCopy s f)

def beforeCopy (s : MachineState) (f : Fin 18) : MachineState :=
  if z : f.val=0 then s else afterCopy s ⟨f.val-1,by omega⟩

def sourceAt (i : Index) (f : Fin 18) : Nat :=
  if f.val=0 then nonceAddress i else if f.val<4 then leafAddress (i.val ^^^ f.val) else siblingAddress i (f.val-4)
def destAt (o : Nat) (f : Fin 18) : Nat :=
  if f.val=0 then recordBase o else if f.val<4 then recordBase o+(16+32*(f.val-1))
  else siblingDestination o (f.val-4)

theorem before_relation (s : MachineState) (f : Fin 18) :
    straight (beforeCopy s f) (beforeOps f)=atCopy s f := by
  fin_cases f <;> rfl

theorem group_cursor (s : MachineState) (i : Index) (o j : Nat) (fit : o<LENGTH) (lim : j≤3)
    (start : PrefixStart s i o) : GroupCursor (groupOld s j) i o j := by
  induction j with
  | zero => exact (run_salt_start s i o fit start).2.1
  | succ j ih =>
    have small : j<3 := by omega
    rw [groupOld, dif_pos small]
    exact (run_group_step _ i o ⟨j,small⟩ fit (ih (by omega))).2.1

theorem upper_cursor (s : MachineState) (i : Index) (o l : Nat) (fit : o<LENGTH) (lim : l≤14)
    (start : PrefixStart s i o) : LowerCursor (upperOld s l) i o l := by
  induction l with
  | zero => exact (execute_record_prefix s i o fit start).2.1
  | succ l ih =>
    have small : l<14 := by omega
    rw [upperOld,dif_pos small]
    exact (execute_sibling _ i o fit ⟨l,small⟩ (ih (by omega))).next

theorem atCopy_witness (s : MachineState) (i : Index) (o : Nat) (fit : o<LENGTH)
    (start : PrefixStart s i o) (f : Fin 18) :
    FieldInputs (oldSite f) (atCopy s f) (sourceAt i f) (destAt o f) := by
  fin_cases f
  · exact nonce_witness s i o fit start
  · exact quartet_witness (groupOld s 0) i o 0 fit (group_cursor s i o 0 fit (by decide) start)
  · exact quartet_witness (groupOld s 1) i o 1 fit (group_cursor s i o 1 fit (by decide) start)
  · exact quartet_witness (groupOld s 2) i o 2 fit (group_cursor s i o 2 fit (by decide) start)
  · exact sibling_witness (upperOld s 0) i o fit 0 (upper_cursor s i o 0 fit (by decide) start)
  · exact sibling_witness (upperOld s 1) i o fit 1 (upper_cursor s i o 1 fit (by decide) start)
  · exact sibling_witness (upperOld s 2) i o fit 2 (upper_cursor s i o 2 fit (by decide) start)
  · exact sibling_witness (upperOld s 3) i o fit 3 (upper_cursor s i o 3 fit (by decide) start)
  · exact sibling_witness (upperOld s 4) i o fit 4 (upper_cursor s i o 4 fit (by decide) start)
  · exact sibling_witness (upperOld s 5) i o fit 5 (upper_cursor s i o 5 fit (by decide) start)
  · exact sibling_witness (upperOld s 6) i o fit 6 (upper_cursor s i o 6 fit (by decide) start)
  · exact sibling_witness (upperOld s 7) i o fit 7 (upper_cursor s i o 7 fit (by decide) start)
  · exact sibling_witness (upperOld s 8) i o fit 8 (upper_cursor s i o 8 fit (by decide) start)
  · exact sibling_witness (upperOld s 9) i o fit 9 (upper_cursor s i o 9 fit (by decide) start)
  · exact sibling_witness (upperOld s 10) i o fit 10 (upper_cursor s i o 10 fit (by decide) start)
  · exact sibling_witness (upperOld s 11) i o fit 11 (upper_cursor s i o 11 fit (by decide) start)
  · exact sibling_witness (upperOld s 12) i o fit 12 (upper_cursor s i o 12 fit (by decide) start)
  · exact sibling_witness (upperOld s 13) i o fit 13 (upper_cursor s i o 13 fit (by decide) start)

theorem sources_aligned (i : Index) (f : Fin 18) : sourceAt i f%8=0 := by
  unfold sourceAt
  split
  · have nz : nonceBase%8=0 := by decide
    unfold nonceAddress;omega
  · split
    · unfold leafAddress
      have v : groupSlots%8=0 := by decide
      omega
    · have v : trapdoorBase%8=0 := by decide
      unfold siblingAddress;omega

theorem destinations (o : Nat) (f : Fin 18) : destAt o f=recordBase o+fieldOffset f := by
  fin_cases f <;> rfl

theorem dst_residue (o : Nat) (f : Fin 18) :
    destAt o f%8=(6*(o%4)+fieldOffset f)%8 := by
  rw [destinations]
  have z : proofBase%8=0 := by decide
  have r := phase_alignment o (fieldOffset f) 0
  simp only [Nat.add_zero] at r
  unfold recordBase recordBytes
  omega

theorem pre_ready (s : MachineState) (i : Index) (o : Nat) (start : PrefixStart s i o) (f : Fin 18) :
    readyOps (beforeOps f) (beforeCopy s f) := by
  fin_cases f
  · simpa [beforeOps,beforeCopy,readyOps,memoryArgumentsValid,memAccess,signExtend12] using start.readable
  all_goals simp [beforeOps,readyOps,memoryArgumentsValid,memAccess]

#print axioms atCopy_witness
#print axioms before_relation
end TwoPermutationPrototype.PhaseOpening
