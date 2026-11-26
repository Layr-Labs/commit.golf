import CommitGolfCandidate.S5BatchPeers
import CommitGolfCandidate.S5SaltLookup
namespace CommitGolfCandidate.S5Machine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (Levels SaltTape)
open Writer (widths)
set_option maxRecDepth 16000
attribute [local irreducible] emitted saltStart readBuffer ix

theorem batch_salt (s : MachineState) (r : Nat) (xs seen : List Index) (tree : Levels) (salt : SaltTape)
    (fs : List S5.Field) (hr : r<xs.length) (size : xs.length≤LENGTH) (limit : widths fs≤555170)
    (cur : FieldCursor tree s fs) (env : InputRows s xs seen tree salt) (pc : s.pc=pcAt 144)
    (indexPtr : s.getReg .x9=W (indexBase+8*r)) (row : s.getReg .x20=W rowBase) :
    let i:=ix xs r
    let cost:=(if i.val%2=0 then 10 else 9)+emitCycles .salt (widths fs)
    ∃ t,Runs s t cost cost ∧ t.pc=pcAt 156 ∧ t.getReg .x14=W i.val ∧ t.getReg .x9=W (indexBase+8*(r+1)) ∧
      FieldCursor tree t (fs++[(192,(salt i).toNat)]) ∧ InputRows t xs seen tree salt ∧
      ∀ reg∈outerRegs,reg≠.x9 → t.getReg reg=s.getReg reg := by
  let i:=ix xs r
  let a:=indexBase+8*r
  let u:=saltStart true s i
  have nmax : xs.length≤16777216:=size
  have av : accessValid (W a) 8=true := by
    apply access_ok <;> dsimp [a,indexBase] <;> first | omega | (change _≤2^36;omega)
  obtain ⟨first,ip,src,cursor,index,mem,keep⟩:=salt_lookup s true a i pc indexPtr av (env.sources.index r hr) row
  let v:=execInstrBr u (.ADDI .x10 .x6 0)
  obtain ⟨move,next,from_,mem',regs⟩:=mov_run u 153 .x10 .x6 (by decide) ip (site (by decide) (by rfl))
  have eq : v.mem=s.mem:=mem'.trans mem
  have stable (reg : Reg) (ok : reg∉([.x6,.x7,.x9,.x10,.x14] : List Reg)) : v.getReg reg=s.getReg reg := by
    apply (regs reg (by intro e;subst reg;simp at ok)).trans
    apply keep <;> intro e <;> subst reg <;> simp at ok
  have ready:=cursor_same cur eq (stable _ (by decide)) (stable _ (by decide)) (stable _ (by decide)) (stable _ (by decide))
  have bounds:=salt_ok i
  have below : saltAddress i+32≤proofBase := by have h:=bounds.2.1;unfold tdEnd at h;unfold proofBase;omega
  have written:=put_field v .salt fs tree (saltAddress i) 24 (salt i) ready next (from_.trans src) bounds.2.2 below limit
    (fun _=>(salt i).isLt) ((read_congr_mem v s _ 24 eq).trans (env.sources.salts i)) (by decide)
  let t:=emitted .salt (widths fs) v
  refine ⟨t,?_,written.pc,?_,?_,written.cursor,inputs_below (inputs_mem env eq) size written.low,?_⟩
  · have all:=(first.trans move).trans written.run
    by_cases even : i.val%2=0 <;> simpa only [i,even,decide_true,decide_false,ite_true,ite_false,Bool.false_eq_true] using all
  · exact (written.keep _ (by simp [Writer.preserved]) (by decide) (by decide)).trans ((regs _ (by decide)).trans index)
  · exact (written.outer .x9 (by decide)).trans ((regs _ (by decide)).trans (cursor.trans (congrArg W (by dsimp [a];omega))))
  · intro reg hr diff
    apply (written.outer reg hr).trans
    apply stable;cases reg <;> simp_all [outerRegs]
end CommitGolfCandidate.S5Machine.Open
