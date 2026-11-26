import CommitGolfCandidate.S5TrialPathModel
import CommitGolfCandidate.S5UpperArgs

namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W)

private structure ClimbState (H : Compression) (x : CheckInput) (q0 q : Fin 4)
    (d : Nat) (s : MachineState) : Prop where
  pc : s.pc = pcAt (trialPathPC d)
  cache : Cache s (trialValues H x q0 q d)
  evidence : Evidence H x q s
  chain : s.getReg .x26 = W chainBuf

attribute [local irreducible] capVal readBuffer Sym.evaluated

private theorem climb_step (o : Oracle) (x : CheckInput) (q0 q : Fin 4)
    (d : Nat) (s : MachineState) (hd : d < 8) (st : ClimbState o.compression x q0 q d s) :
    ∃ t n, n ≤ 27 ∧ Flow o s t n 1 ∧ CapKeeps s t ∧ ClimbState o.compression x q0 q (d+1) t := by
  let p := trialIndex (d+1)
  let ops := trialPathOps d
  obtain ⟨bound,listed,req,source,dest,written,len,sites,legal,next⟩ := trial_path_sites ⟨d,hd⟩
  change p < layerCount (d+1) at bound
  change writers ops [.x10,.x12] at written
  change Sym.requirements Sym.original ops = [] at req
  let u := Sym.evaluated ops s
  obtain ⟨setup,regs,mem,ip⟩ := Sym.compiled o ops (trialPathPC d) s st.pc listed
    (by rw [req]; simp)
  have a : u.getReg .x10 = W (rowAt d p) := (regs .x10).trans (congrArg (fun e : Sym.Expr => e.eval s) source)
  have b : u.getReg .x12 = W (nodeAt (d+1) p) := (regs .x12).trans (congrArg (fun e : Sym.Expr => e.eval s) dest)
  have keep : CapKeeps s u := by
    intro r hr
    apply (regs r).trans
    apply sym_keep _ _ _ written
    cases r <;> simp_all [capRegs]
  have cache := st.cache.same (t:=u) mem
  have raw : readBuffer u (rowAt d p) 96 =
      Late.parentBlock (capVal o.compression x q d (2*p)) (capVal o.compression x q d (2*p+1)) := by
    simpa only [trialValues,Nat.le_refl,ite_true] using cache_row u _ cache d p hd bound
  obtain ⟨t,n,cost,hash⟩ := hash_upper o x q u d p (trialHashPC d) hd bound sites legal ip a b
    ((keep _ (by decide)).trans st.chain) raw
  have keep' := keep.trans hash.keep
  have h9 : d+1 < 9 := by omega
  have geometry := cap_geometry ⟨d+1,h9⟩
  have pad : p < paddedCount (d+1) := bound.trans_le geometry.2.2.2.2.1
  obtain ⟨lo,hi,aligned⟩ := node_range (d+1) p h9 pad
  have data := (st.evidence.same (t:=u) mem).after_node hash.frame (geometry.1.trans lo)
    (hi.trans geometry.2.1) aligned
  have stored := cache.write h9 pad _ hash.value hash.frame
  change (trialPathOps d).length ≤ 4 at len
  refine ⟨t,ops.length+n,by dsimp only [ops]; omega,setup.trans hash.run,keep',?_⟩
  refine ⟨hash.pc.trans (congrArg pcAt next),?_,data,(keep' _ (by decide)).trans st.chain⟩
  rw [← trial_next_values]
  exact stored

private theorem climb (o : Oracle) (x : CheckInput) (q0 q : Fin 4)
    (d k : Nat) (s : MachineState) (st : ClimbState o.compression x q0 q d s) (inside : d+k ≤ 8) :
    ∃ t n, n ≤ 27*k ∧ Flow o s t n k ∧ CapKeeps s t ∧ ClimbState o.compression x q0 q (d+k) t := by
  induction k generalizing d s with
  | zero => exact ⟨s,0,by decide,Flow.refl o s,fun _ _ => rfl,st⟩
  | succ k ih =>
    obtain ⟨u,a,ac,first,keep,mid⟩ := climb_step o x q0 q d s (by omega) st
    obtain ⟨t,b,bc,rest,keep',last⟩ := ih (d+1) u mid (by omega)
    refine ⟨t,a+b,by omega,?_,keep.trans keep',?_⟩
    · simpa only [Nat.add_comm 1 k] using first.trans rest
    · simpa only [Nat.add_assoc,Nat.add_comm 1 k] using last

theorem trial_path (o : Oracle) (x : CheckInput) (q0 q : Fin 4) (s : MachineState)
    (pc : s.pc=pcAt 1197) (env : CapEnv x s) (data : Evidence o.compression x q s)
    (cache : Cache s (replaceNode (capVal o.compression x q0) 0 170 (capVal o.compression x q 0 170))) :
    ∃ t n, n≤300 ∧ Flow o s t n 8 ∧ t.pc=pcAt 1260 ∧ Cache t (capVal o.compression x q) ∧
      Evidence o.compression x q t ∧ CapKeeps s t := by
  rw [trial_start_values] at cache
  obtain ⟨t,n,cost,run,keep,last⟩ := climb o x q0 q 0 8 s ⟨pc,cache,data,env.chain⟩ (by decide)
  exact ⟨t,n,by omega,run,last.pc,trial_done_cache last.cache,last.evidence,keep⟩

end CommitGolfCandidate.S5Machine.Check
