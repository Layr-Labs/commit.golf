import CommitGolfCandidate.S5CapUpperMemory
namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W)
private theorem fold_keep (ops : List Sym.Calc) (f : Reg→Sym.Expr) (r : Reg) (ok : ∀ c∈ops,c.dst≠r) : (ops.foldl Sym.bump f) r=f r := by
  induction ops generalizing f with
  | nil=>rfl
  | cons c cs ih=>rw [List.foldl_cons,ih _ (fun a h=>ok a (List.mem_cons_of_mem _ h))];exact if_neg (ok c (List.mem_cons_self ..))
def writers (ops : List Sym.Calc) (out : List Reg):=ops.all fun c=>out.contains c.dst
theorem sym_keep (s : MachineState) (ops : List Sym.Calc) (allowed : List Reg) (good : writers ops allowed) (r : Reg) (safe : r∉allowed) :
    ((ops.foldl Sym.bump Sym.original) r).eval s=s.getReg r := by
  rw [fold_keep _ _ r (fun c hc eq=>safe (eq ▸ List.contains_iff_mem.mp (List.all_eq_true.mp good c hc)))]
  cases r <;> rfl

def rowExpr : Sym.Expr:=.op .add (.reg .x14) (.op .shl (.op .add (.op .shl (.reg .x23) (.lit 1)) (.reg .x23)) (.lit 5))
def nodeExpr (d : Nat) : Sym.Expr :=
  let k:=Sym.Expr.reg .x23
  let half:=Sym.Expr.op .shr k (.lit 1)
  let body:=Sym.Expr.op .shl (.op .add (.op .shl half (.lit 1)) half) (.lit 5)
  let lane:=Sym.Expr.op .shl (.op .and k (.lit 1)) (.lit 5)
  .op .add (.reg .x15) (if d=7 then .lit 0 else .op .add body lane)
theorem upper_symbols : ∀ j : Fin 8,let d:=j.val;let f:=(upperHeader d).foldl Sym.bump Sym.original;let g:=(upperAddress d).foldl Sym.bump Sym.original;
    Sym.requirements Sym.original (upperHeader d)=[] ∧ Sym.requirements Sym.original (upperAddress d)=[] ∧
    writers (upperHeader d) [.x14,.x15,.x23,.x9] ∧ writers (upperAddress d) [.x6,.x7,.x10,.x12] ∧
    f .x14=.lit (W (layerStart d)) ∧ f .x15=.lit (W (layerStart (d+1))) ∧ f .x23=.lit 0 ∧ f .x9=.lit (W (layerCount (d+1))) ∧
    g .x10=rowExpr ∧ g .x12=nodeExpr d := by decide +kernel

private theorem offset_numeric (p : Fin 171) :
  (((W p.val <<< 1)+W p.val) <<< 5)=W (96*p.val) ∧
  (((((W p.val >>> 1) <<< 1)+(W p.val >>> 1)) <<< 5)+((W p.val &&& 1) <<< 5))=W (96*(p.val/2)+32*(p.val%2)) :=
  (by decide +kernel : ∀ q : Fin 171,(((W q.val <<< 1)+W q.val) <<< 5)=W (96*q.val) ∧
    (((((W q.val >>> 1) <<< 1)+(W q.val >>> 1)) <<< 5)+((W q.val &&& 1) <<< 5))=W (96*(q.val/2)+32*(q.val%2))) p

theorem upper_args (o : Oracle) (s : MachineState) (d p : Nat) (hd : d<8) (hp : p<layerCount (d+1))
    (pc : s.pc=pcAt (upperLoop d)) (ctr : s.getReg .x23=W p) (from_ : s.getReg .x14=W (layerStart d)) (to_ : s.getReg .x15=W (layerStart (d+1))) :
    ∃ t, Flow o s t (upperAddress d).length 0 ∧ t.pc=pcAt (configPC d) ∧ t.getReg .x10=W (rowAt d p) ∧
      t.getReg .x12=W (nodeAt (d+1) p) ∧ t.mem=s.mem ∧ CapKeeps s t := by
  obtain ⟨_,req,_,written,_,_,_,_,regA,regB⟩:=upper_symbols ⟨d,hd⟩
  have small : p<171:=hp.trans_le ((by decide +kernel : ∀ j : Fin 8,layerCount (j.val+1)≤171) ⟨d,hd⟩)
  obtain ⟨run,regs,mem,ip⟩:=Sym.compiled o (upperAddress d) (upperLoop d) s pc (upper_sites ⟨d,hd⟩).2.2.2.1
    (by change Sym.requirements Sym.original (upperAddress d)=[] at req;rw [req];simp)
  have ka := (regs .x10).trans (congrArg (fun e : Sym.Expr=>e.eval s) regA)
  have kb := (regs .x12).trans (congrArg (fun e : Sym.Expr=>e.eval s) regB)
  refine ⟨_,run,ip,?_,?_,mem,?_⟩
  · apply ka.trans;change s.getReg .x14+(((s.getReg .x23 <<< 1)+s.getReg .x23) <<< 5)=_
    rw [from_,ctr,(offset_numeric ⟨p,small⟩).1];exact (BitVec.ofNat_add ..).symm
  · apply kb.trans;by_cases last : d=7
    · have zero : p=0:=by rw [last] at hp;change p<1 at hp;omega
      subst p;simp only [nodeExpr,last,ite_true,Sym.Expr.eval,Sym.Bin.apply,BitVec.add_zero,to_];rfl
    · simp only [nodeExpr,last,ite_false,Sym.Expr.eval,Sym.Bin.apply]
      change s.getReg .x15+(((((s.getReg .x23 >>> 1) <<< 1)+(s.getReg .x23 >>> 1)) <<< 5)+((s.getReg .x23 &&& 1) <<< 5))=_
      rw [to_,ctr,(offset_numeric ⟨p,small⟩).2]
      apply (BitVec.ofNat_add ..).symm.trans;apply congrArg W;dsimp [nodeAt];omega
  · intro q h;apply (regs q).trans;apply sym_keep _ _ _ written;cases q <;> simp_all [capRegs]

structure UpperWrite (o : Oracle) (x : CheckInput) (q : Fin 4) (s t : MachineState) (d p pc n : Nat) : Prop where
  run : Flow o s t n 1
  pc : t.pc=pcAt pc
  value : readBuffer t (nodeAt (d+1) p) 32=capVal o.compression x q (d+1) p
  keep : CapKeeps s t
  frame : ChainOutside s t (nodeAt (d+1) p)

theorem hash_upper (o : Oracle) (x : CheckInput) (q : Fin 4) (s : MachineState) (d p pc : Nat) (hd : d<8) (hp : p<layerCount (d+1))
    (code : parentSites pc (16+d)) (legal : pc+4<2336) (ip : s.pc=pcAt pc) (a : s.getReg .x10=W (rowAt d p))
    (b : s.getReg .x12=W (nodeAt (d+1) p)) (sc : s.getReg .x26=W chainBuf)
    (raw : readBuffer s (rowAt d p) 96=Late.parentBlock (capVal o.compression x q d (2*p)) (capVal o.compression x q d (2*p+1))) :
    ∃ t n,n≤23 ∧ UpperWrite o x q s t d p (pc+4) n := by
  have bounds:=child_bounds d p hd hp
  obtain ⟨_,hi,al⟩:=gap_range d p hd bounds.1
  obtain ⟨_,dest,dalign⟩:=node_range (d+1) p (by omega) (hp.trans_le (cap_geometry ⟨d+1,by omega⟩).2.2.2.2.1)
  have srcFit : rowAt d p+96≤MEMORY_BYTES:=by
    have fin:=(cap_geometry ⟨d,by omega⟩).2.1
    change areaEnd d≤saltBuf at fin
    unfold gapAt at hi
    have lim : saltBuf≤MEMORY_BYTES:=by decide
    omega
  have row : S5.Auth.row (16+d) (capVal o.compression x q d (2*p)) (capVal o.compression x q d (2*p+1)) 0=Late.parentBlock (capVal o.compression x q d (2*p)) (capVal o.compression x q d (2*p+1)):=by unfold S5.Auth.row;split <;> rfl
  obtain ⟨t,n,lim,done_⟩:=cap_hash o s pc (16+d) (rowAt d p) (nodeAt (d+1) p) _ _ 0 (by omega) legal code ip a b sc srcFit
    (by unfold gapAt at al;omega) (dest.trans ((cap_geometry ⟨d+1,by omega⟩).2.1.trans (by decide))) dalign (raw.trans row.symm) (by omega)
  have facts:=upper_sites ⟨d,hd⟩
  have fuel : parentFuel (16+d)=19:=facts.2.2.2.2.2.2.2.2.2.2.1
  have calls : levelCalls (16+d)=1:=facts.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨t,n,by omega,⟨?_,done_.pc,?_,done_.keep,done_.frame⟩⟩
  · rw [←calls];exact done_.run
  · rw [cache_next _ _ _ _ _ hp,←row];exact done_.value
end CommitGolfCandidate.S5Machine.Check
