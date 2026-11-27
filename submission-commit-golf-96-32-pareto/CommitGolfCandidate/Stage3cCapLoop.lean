import CommitGolfCandidate.Stage3cCapField
import CommitGolfCandidate.Stage3cBatchPath
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (Levels SaltTape)
open Writer (widths)

def capFields (tree : Levels) (xs : List Index) (p n : Nat) := (List.range' p n).map (Binary.slot tree xs)
def capPrice (xs : List Index) (p n : Nat) := ((List.range' p n).map (costAt xs)).sum

theorem cap_loop (s : MachineState) (p n : Nat) (xs : List Index) (tree : Levels) (salt : SaltTape)
    (fs : List Binary.Field) (size : xs.length≤LENGTH) (stop : p+n≤256) (lim : widths fs+230*n≤542720)
    (old : CapRegs s p) (env : InputRows s xs xs tree salt) (cur : FieldCursor tree s fs) :
    let cost:=capPrice xs p n+energy (widths fs) (capFields tree xs p n)
    ∃ t,Runs s t cost cost ∧ CapRegs t (p+n) ∧ InputRows t xs xs tree salt ∧
      FieldCursor tree t (fs++capFields tree xs p n) := by
  induction n generalizing s p fs with
  | zero=>
    simp only [capPrice,capFields,List.range'_zero,List.map_nil,List.sum_nil,energy,List.append_nil,Nat.add_zero]
    exact ⟨s,Runs.refl _,old,env,cur⟩
  | succ n ih=>
    let f:=Binary.slot tree xs p
    have width : widths (fs++[f])=widths fs+230:=by simp [widths,f,Binary.slot]
    obtain ⟨u,step,reg,input,packed⟩:=cap_field s p (by omega) xs tree salt fs size (by omega) old env cur
    obtain ⟨t,tail,last,data,c⟩:=ih (s:=u) (p:=p+1) (fs:=fs++[f]) (by omega) (by rw [width];omega) reg input packed
    refine ⟨t,?_,?_,data,?_⟩
    · have all:=step.trans tail
      rw [width] at all
      simp only [capPrice,capFields,List.range'_succ,List.map_cons,List.sum_cons,energy]
      change Runs s t _ _ at all
      convert all using 1 <;> change _=_ <;> dsimp only [capPrice,capFields,Binary.slot] at * <;> omega
    · simpa only [Nat.add_assoc,Nat.add_comm 1 n] using last
    · simpa only [f,capFields,List.range'_succ,List.map_cons,List.append_assoc,List.singleton_append] using c
end CommitGolfCandidate.Chained.BinaryMachine.Open
