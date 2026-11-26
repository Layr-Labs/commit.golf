import CommitGolfCandidate.S5TailRegs
namespace CommitGolfCandidate.S5Machine
open CommitGolfCandidate.Chained
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def tailPrefix (d : Height) (p : Nat) := p*(laneWords d+6)+p/2
private theorem tail_price_step (d : Height) (p : Nat) :
    tailPrefix d (p+1)=tailPrefix d p+(laneWords d+(tailOps (tailOdd p)).length+1) := by
  by_cases odd : p%2=1 <;> simp [tailPrefix,tailOps,tailOdd,odd,Nat.succ_mul] <;> omega
private theorem price_mono (d : Height) (p n : Nat) : tailPrefix d p≤tailPrefix d (p+n) := by
  induction n with
  | zero=>simp
  | succ k ih=>rw [Nat.add_succ,tail_price_step];omega

theorem tail_lanes (o : Oracle) (d : Height) (n p : Nat) (s : MachineState) (base : Nat→Output) (salt : Late.SaltTape)
    (frame : TailFrame d p s) (simple : ¬chained d) (inner : d.val<23) (rp : 0<remainder d)
    (available : p+n≤count d) (tree : TreeState o.compression base salt d.val s) (rows : doneRows o.compression base d.val p s) :
    ∃ t,TailFrame d (p+n) t ∧ TreeState o.compression base salt d.val t ∧ doneRows o.compression base d.val (p+n) t ∧
      Runs .commit true o s t (tailPrefix d (p+n)-tailPrefix d p) (tailPrefix d (p+n)-tailPrefix d p+7*n) n := by
  induction n generalizing p s with
  | zero=>exact ⟨s,by simpa using frame,tree,by simpa using rows,by simpa using runs_id .commit true o s⟩
  | succ n ih=>
    have ok : p<count d:=by omega
    obtain ⟨first,next,eff⟩:=tail_step o frame simple inner ok rp tree.pads
    obtain ⟨t,tf,st,rd,rest⟩:=ih (p+1) _ next (by omega) (node_frame tree eff ok) (grow_row tree rows eff ok)
    rw [show p+(n+1)=p+1+n by omega]
    refine ⟨t,tf,st,rd,?_⟩
    have up:=tail_price_step d p
    have mono:=price_mono d (p+1) n
    have total:=runs_comp first rest
    convert total using 1 <;> omega

def mainCount (d : Height) := tiles d*tileSize d
theorem parts (d : Height) : mainCount d+remainder d=count d := by
  unfold mainCount tiles remainder
  rw [Nat.mul_comm];exact Nat.div_add_mod _ _
theorem main_even (d : Height) : mainCount d%2=0 := (by decide +kernel : ∀ d : Height,mainCount d%2=0) d

def rebaseOps (d : Height) : List Instr := [.ADDI .x21 .x21 2048,.ADDI .x22 .x22 2048,
  .ADDI .x20 .x0 (BitVec.ofNat 12 (remainder d)),.ADDI .x7 .x0 0]
private theorem rebase_sites : ∀ d : Height,¬chained d →0<tileSize d →
    mainExit d+4=tailPC d ∧ tailPC d<18492 ∧ 0<remainder d ∧
    signExtend12 (BitVec.ofNat 12 (remainder d))=BitVec.ofNat 64 (remainder d) ∧
    ∀ j : Fin 4,decoded (mainExit d+j.val)=some (.base ((rebaseOps d).get ⟨j.val,j.isLt⟩)) := by decide +kernel

theorem rebase (o : Oracle) {d s} (simple : ¬chained d) (used : 0<tileSize d)
    (frame : Boundary d (mainCount d) 0 s) :
    let t:=(rebaseOps d).foldl execInstrBr s
    TailFrame d (mainCount d) t ∧ t.mem=s.mem ∧ Runs .commit true o s t 4 4 0 := by
  obtain ⟨end_,range,positive,sign,code⟩:=rebase_sites d simple used
  have total:=parts d
  have valid : mainCount d<count d := by omega
  have pc : s.pc=pcAt (mainExit d):=frame.pc.trans (by rw [if_neg (by decide : ¬0<0)])
  have legal : (rebaseOps d).all setupOp=true := rfl
  have ok := fun op mem=>List.all_eq_true.mp legal op mem
  obtain ⟨mem,finish⟩:=header_properties (rebaseOps d) s ok
  let t:=(rebaseOps d).foldl execInstrBr s
  have kept (r : Reg) (a : Reg.x21≠r) (b : Reg.x22≠r) (c : Reg.x20≠r) (z : Reg.x7≠r) :t.getReg r=s.getReg r := by
    simp only [t,rebaseOps,List.foldl_cons,List.foldl_nil,execInstrBr,MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ a,MachineState.getReg_setReg_ne _ _ _ _ b,
      MachineState.getReg_setReg_ne _ _ _ _ c,MachineState.getReg_setReg_ne _ _ _ _ z]
  have cm : Common t := by
    obtain ⟨q1,q2,q3,q4,q5,q6,q7,q8,q9⟩:=frame.toCommon
    constructor <;> apply (kept _ (by decide) (by decide) (by decide) (by decide)).trans <;> assumption
  refine ⟨⟨cm,fun w=>(kept .x30 (by decide) (by decide) (by decide) (by decide)).trans (frame.selectMask w),?_,?_,?_,?_,?_⟩,mem,?_⟩
  · rw [finish,pc,if_pos valid,←end_];change pcAt _+BitVec.ofNat 64 16=pcAt _
    unfold pcAt;rw [←BitVec.ofNat_add];congr 1 <;> omega
  · change s.getReg .x21+signExtend12 2048=_
    rw [frame.src,BitVec.add_assoc];exact BitVec.add_zero _
  · change s.getReg .x22+signExtend12 2048=_
    rw [frame.dst,BitVec.add_assoc];exact BitVec.add_zero _
  · change 0+signExtend12 (BitVec.ofNat 12 (remainder d))=_
    rw [sign,show count d-mainCount d=remainder d by omega];exact BitVec.zero_add _
  · rw [main_even];rfl
  · apply runs_pure;intro fuel
    apply execute_linear .commit true (rebaseOps d) _ _ _ pc
    · exact fun op mem=>header_straight _ (ok op mem)
    · intro i hi;change i<4 at hi;exact decoded_site (by omega) (code ⟨i,hi⟩)
end CommitGolfCandidate.S5Machine
