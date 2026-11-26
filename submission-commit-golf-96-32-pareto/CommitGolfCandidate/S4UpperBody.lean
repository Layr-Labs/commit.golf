import CommitGolfCandidate.S4UpperHeader
import CommitGolfCandidate.S4SaltAssembly
import CommitGolfCandidate.S4RowValues
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt Digest)

structure UpperHashed (o : Oracle) (x : CheckInput) (k i : Nat) (s t : MachineState) : Prop where
  run : CheckRuns o s t (21+(2+callSteps (cutUpper k))) 1
  pc : t.pc=pcAt (afterHash k)
  env : Env x t
  table : RowMemory o.compression (readView x) k (i+1) t
  keep : ∀ r,r∈[Reg.x29,.x30,.x19] → t.getReg r=s.getReg r

theorem upperBody (o : Oracle) (x : CheckInput) (k : Fin 8) (i : Nat) (s : MachineState)
    (inside : i<nextWidth k) (f : UpperCursor o.compression x k i s) : ∃ t,UpperHashed o x k i s t := by
  let n:=upperLoop k;let a:=upperAddr (2*i);let d:=upperAddr i
  have range:=upperGeometry k;have bound : i<86:=lt_of_lt_of_le inside range.1
  have code:=upperSites k
  have known : ∀ h : Fin 8,upperLoop h+32≤22492:=by decide
  have space : n+32≤Code.check.count:=known k
  have pc : s.pc=pcAt n:=by have t:=f.pc;rw [if_pos inside] at t;exact t
  let u:=execInstrBr s (ptrCode .x14 512)
  have ptr:=stepAdd .check s n .x14 .x0 512 (by omega) pc code.copy.head
  have mv:=dwordBlock .check u .x29 .x14 (n+1) a 512 0 0 8 (by decide) (by decide) (addPC _ _ _ pc) (by omega) code.copy.tail
    ((keepAdd s .x14 .x0 .x29 512 (by decide)).trans f.source) rfl (by dsimp [a,upperAddr];omega) (by decide) (by decide) (by decide)
    (by dsimp [a,upperAddr,MEMORY_BYTES];omega) (by decide) (Or.inr (by dsimp [a,upperAddr];omega))
  let v:=copyBlock .x29 .x14 0 0 (dwords 8) u
  have copied : Moved s v a 512 64:=mv.bytes.congr rfl rfl
  let z:=clearState v 4
  have rv : v.getReg .x14=W 512:=(mv.regs .x14 (by decide)).trans rfl
  obtain ⟨pad,padRead⟩:=zeroRow v (n+17) mv.endPC rv (by omega) code.zeros
  have hold (r : Reg) (h1 : r≠.x6) (h2 : r≠.x14) : z.getReg r=s.getReg r:=(pad.regs r).trans
    ((mv.regs r (Ne.symm h1)).trans (keepAdd s .x14 .x0 r 512 (Ne.symm h2)))
  have localFrame : SameOutside s z 512 96:=copied.frame.combined pad.outside (by decide)
  have even : readBuffer s a 32=nodeValue o.compression (readView x) k (2*i):=
    f.table.rest _ le_rfl (by change 2*i<2*nextWidth k;omega)
  have odd : readBuffer s (a+32) 32=nodeValue o.compression (readView x) k (2*i+1):=by
    rw [show a+32=upperAddr (2*i+1) by dsimp [a,upperAddr];omega]
    exact f.table.rest _ (by omega) (by change 2*i+1<2*nextWidth k;omega)
  have row : readBuffer z 512 96=rowInput o.compression (readView x) k i:=by
    have l:=(pad.outside.read (b:=512) (m:=32) (by decide) (Or.inl (by decide))).trans
      ((copied.subread (by decide) 0 32 (by decide)).trans even)
    have r:=(pad.outside.read (b:=544) (m:=32) (by decide) (Or.inl (by decide))).trans
      ((copied.subread (by decide) 32 32 (by decide)).trans odd)
    have sub:=Late.readTriple z 512
    change readBuffer z 512 96=readBuffer z 576 32 ++ readBuffer z 544 32 ++ readBuffer z 512 32 at sub
    have zero : readBuffer z 576 32=0:=padRead
    rw [zero,l,r] at sub;exact sub
  have cs : callSteps (cutUpper k)≤2:=by unfold callSteps;split <;> decide
  have maskFitsUpper : ∀ h : Fin 8,maskFits (upperLoop h+24) (17+h.val):=by decide
  have maskSite:=maskFitsUpper k
  have call:=tableHash o z (n+21) d (cutUpper k) (fun yes=>(maskSite yes).1) pad.pc (by omega) code.compress
    ((hold .x5 (by decide) (by decide)).trans f.mode) ((hold .x13 (by decide) (by decide)).trans f.kind)
    ((hold .x11 (by decide) (by decide)).trans f.width) ((pad.regs .x14).trans rv)
    ((hold .x30 (by decide) (by decide)).trans f.dest) ⟨by dsimp [d,upperAddr];omega,by dsimp [d,upperAddr,MEMORY_BYTES];omega⟩
  let t:=tableReply o z (n+21) d (cutUpper k)
  have keep (r : Reg) (h : r∉[Reg.x6,.x10,.x12,.x14]) : t.getReg r=s.getReg r:=by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at h
    exact (call.keep r h.2.1 h.2.2.1).trans (hold r h.1 h.2.2.2)
  have high : HighExcept s t d 32:=(highOnly localFrame (by decide)).trans (highWrite call.outside)
  have value : readBuffer t d 32=nodeValue o.compression (readView x) (k.val+1) i:=by
    rw [nextUpper _ _ _ _ inside]
    exact call.value.trans ((trimIsRetained (n+24) (17+k.val) maskSite _).trans (congrArg (fun b=>retained .packed (17+k.val) (o.compression b)) row))
  have envOK : ∀ r : Reg,envReg r → r∉[Reg.x6,.x10,.x12,.x14]:=by intro r;cases r <;> decide
  have savedRegs : ∀ r : Reg,r∈[Reg.x29,.x30,.x19] → r∉[Reg.x6,.x10,.x12,.x14]:=by intro r;cases r <;> decide
  exact ⟨t,⟨(ofRuns o ((ptr.trans mv.run).trans pad.run)).trans call.run,call.pc,
    f.toEnv.move (fun r hr=>keep r (envOK r hr)) (high.env (by dsimp [d,upperAddr];omega) f.data),
    rowNextMemory _ _ _ _ k.isLt inside s t f.table value high,fun r h=>keep r (savedRegs r h)⟩⟩
end CommitGolfCandidate.S4.Machine
