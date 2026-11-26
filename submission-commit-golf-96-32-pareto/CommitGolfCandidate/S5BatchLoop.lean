import CommitGolfCandidate.S5BatchCycle
namespace CommitGolfCandidate.S5Machine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (Levels SaltTape)
open Writer (widths)
def recordFields (tree : Levels) (salt : SaltTape) (xs : List Index) := xs.flatMap fun i=>S5.record tree salt i true
def recordSteps (tree : Levels) (salt : SaltTape) (n : Nat) (xs : List Index) :=
  206*xs.length+(xs.map biased).sum+energy n (recordFields tree salt xs)

set_option maxRecDepth 12000
attribute [local irreducible] S5.record energy ix
theorem batch_loop (s : MachineState) (xs seen ys : List Index) (tree : Levels) (salt : SaltTape)
    (r : Nat) (fs : List S5.Field) (size : xs.length≤LENGTH) (suffix : xs.drop r=ys)
    (limit : widths fs+4030*ys.length≤555170) (reg : BatchRegs s r xs.length)
    (env : InputRows s xs seen tree salt) (cursor : FieldCursor tree s fs) :
    let steps:=recordSteps tree salt (widths fs) ys
    ∃ t,Runs s t steps (steps+12*ys.length) ∧ BatchRegs t (r+ys.length) xs.length ∧
      FieldCursor tree t (fs++recordFields tree salt ys) ∧ InputRows t xs (seen++ys) tree salt := by
  induction ys generalizing r s fs seen with
  | nil=>
    simp only [recordSteps,recordFields,List.length_nil,List.map_nil,List.sum_nil,List.flatMap_nil,List.append_nil,Nat.mul_zero,
      Nat.zero_add,Nat.add_zero,energy]
    exact ⟨s,Runs.refl _,reg,cursor,env⟩
  | cons i ys ih=>
    have len:=congrArg List.length suffix
    simp only [List.length_drop,List.length_cons] at len
    have hr : r<xs.length:=by omega
    have selected : ix xs r=i := by
      have e:=congrArg (fun l : List Index=>l[0]?) suffix
      simpa only [ix,List.getElem?_drop,Nat.add_zero,List.getElem?_cons_zero,Option.getD_some] using congrArg (fun v : Option Index=>v.getD ⟨0,by decide⟩) e
    have rest : xs.drop (r+1)=ys := by
      have e:=congrArg (List.drop 1) suffix
      simpa only [List.drop_drop,Nat.add_comm 1 r,List.drop_succ_cons,List.drop_zero] using e
    let fields:=S5.record tree salt i true
    have wrec : widths (fs++fields)=widths fs+4030:=by rw [sum_append,batch_record_width]
    simp only [List.length_cons,Nat.mul_add,Nat.mul_one] at limit
    obtain ⟨u,head⟩:=batch_cycle s r xs seen tree salt fs hr size (by have le:=Nat.zero_le (4030*ys.length);omega) env cursor reg
    have cur : FieldCursor tree u (fs++fields):=by simpa only [selected,fields] using head.cursor
    have data : InputRows u xs (seen++[i]) tree salt:=by simpa only [selected] using head.input
    obtain ⟨t,tail,last,packed,input⟩:=ih u (seen++[i]) (r+1) (fs++fields) rest (by rw [wrec];omega) head.regs data cur
    refine ⟨t,?_,?_,?_,?_⟩
    · have first:=head.run
      simp only [selected] at first
      have all:=first.trans tail
      have expense : energy (widths fs) (recordFields tree salt (i::ys))=energy (widths fs) fields+energy (widths (fs++fields)) (recordFields tree salt ys) := by
        change energy _ (fields++recordFields tree salt ys)=_;rw [energy_append,sum_append]
      simp only [recordSteps,List.length_cons,List.map_cons,List.sum_cons,expense,Nat.mul_add,Nat.mul_one] at all ⊢
      change Runs s t _ _ at all
      convert all using 1 <;> dsimp only [fields] <;> omega
    · simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm 1 ys.length] using last
    · simpa only [fields,recordFields,List.flatMap_cons,List.append_assoc] using packed
    · simpa only [List.append_assoc,List.singleton_append] using input
end CommitGolfCandidate.S5Machine.Open
