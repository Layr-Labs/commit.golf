import CommitGolfCandidate.S5BatchField
namespace CommitGolfCandidate.S5Machine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (Levels SaltTape)
open Writer (widths)

def energy (n : Nat) : List S5.Field→Nat
  | []=>0
  | f::fs=>(Writer.measureField ⟨n%64,0⟩ f.1).cycles+energy (n+f.1) fs
theorem sum_append (xs ys : List S5.Field) : widths (xs++ys)=widths xs+widths ys := by simp [widths]
theorem energy_append (n : Nat) (xs ys : List S5.Field) :
    energy n (xs++ys)=energy n xs+energy (n+widths xs) ys := by
  induction xs generalizing n with
  | nil=>simp [energy,widths]
  | cons x xs ih=>simp [energy,ih,widths,Nat.add_assoc]

def binaryFields (tree : Levels) (i : Index) (d n : Nat) := (List.range' (d+1) n).map (siblingField tree i)
theorem fields_next (tree : Levels) (i : Index) (d n : Nat) : binaryFields tree i d (n+1)=
    siblingField tree i (d+1)::binaryFields tree i (d+1) n := by simp only [binaryFields,List.range'_succ,List.map_cons]

theorem batch_path (s : MachineState) (d n : Nat) (i : Index) (xs seen : List Index) (tree : Levels)
    (salt : SaltTape) (size : xs.length≤LENGTH) (env : InputRows s xs seen tree salt) (fs : List S5.Field)
    (depth : d+n≤14) (bound : widths fs+widths (binaryFields tree i d n)≤555170)
    (cur : FieldCursor tree s fs) (pc : s.pc=pcAt (179+12*d)) (gp : s.getReg .x3=W 2048)
    (idx : s.getReg .x14=W (indexAbove i (d+1))) :
    let fields:=binaryFields tree i d n
    let cost:=12*n+energy (widths fs) fields
    ∃ t,Runs s t cost cost ∧ t.pc=pcAt (179+12*(d+n)) ∧ t.getReg .x14=W (indexAbove i (d+n+1)) ∧
      FieldCursor tree t (fs++fields) ∧ InputRows t xs seen tree salt ∧ OuterKeeps s t := by
  induction n generalizing s d fs with
  | zero=>
    simp only [binaryFields,List.range'_zero,List.map_nil,energy,Nat.mul_zero,Nat.add_zero,List.append_nil]
    exact ⟨s,Runs.refl _,pc,idx,cur,env,fun _ _=>rfl⟩
  | succ n ih=>
    let l : Fin 14:=⟨d,by omega⟩
    let f:=siblingField tree i (d+1)
    obtain ⟨u,step,ip,j,packed,data,keep⟩:=batch_sibling s l i xs seen tree salt size env fs (by omega) cur pc gp idx
    have room : widths (fs++[f])+widths (binaryFields tree i (d+1) n)≤555170 := by
      rw [fields_next] at bound
      simp only [widths,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] at bound ⊢
      dsimp only [f];omega
    obtain ⟨t,tail,last,pos,result,src,frame⟩:=ih (s:=u) (d:=d+1) (fs:=fs++[f]) data (by omega) room packed ip ((keep .x3 (by decide)).trans gp) j
    have eqn : d+1+n=d+(n+1) :=by omega
    rw [eqn] at last pos
    refine ⟨t,?_,last,pos,?_,src,keep.then frame⟩
    · have both:=step.trans tail
      have w : widths (fs++[f])=widths fs+f.1:=by simp [widths]
      rw [w] at both
      simp only [fields_next,energy,Nat.mul_succ]
      change Runs s t _ _ at both
      convert both using 1 <;> dsimp [emitCycles,f,EmitSite.width,l,siblingField] <;> omega
    · rw [fields_next];simpa only [List.append_assoc,List.singleton_append,f] using result
end CommitGolfCandidate.S5Machine.Open
