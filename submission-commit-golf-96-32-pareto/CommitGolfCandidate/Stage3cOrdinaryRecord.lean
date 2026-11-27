import CommitGolfCandidate.Stage3cOrdinaryPath
import CommitGolfCandidate.Stage3cSaltLookup
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open CommitGolfCandidate.Late (Levels SaltTape bytes)

set_option maxRecDepth 14000
set_option maxHeartbeats 1000000
attribute [local irreducible] saltStart copyWords readBuffer pathBytes Late.record

theorem ordinary_record (s : MachineState) (r dst : Nat) (xs : List Index) (tree : Levels) (salt : SaltTape)
    (hr : r<xs.length) (size : xs.length≤LENGTH) (pc : s.pc=pcAt 460) (gp : s.getReg .x3=W 2048) (tab : Capacity s)
    (indexPtr : s.getReg .x9=W (indexBase+8*r)) (row : s.getReg .x20=W rowBase) (ptr : s.getReg .x19=W dst)
    (high : proofBase≤dst) (valid : AddrOK dst 792) (source : Sources s xs tree salt) :
    let i:=ix xs r
    let cost:=473
    ∃ t,Runs s t cost (cost+3) ∧ t.pc=pcAt 933 ∧ t.getReg .x19=W (dst+792) ∧ t.getReg .x9=W (indexBase+8*(r+1)) ∧
      Capacity t ∧ Sources t xs tree salt ∧
      (∀ reg,reg∉([.x4,.x6,.x7,.x9,.x14,.x19,.x28] : List Reg)→t.getReg reg=s.getReg reg) ∧
      Written s t dst (Late.record tree salt LOG_LENGTH i) := by
  let i:=ix xs r
  let a:=indexBase+8*r
  let u:=saltStart false s i
  have nmax : xs.length≤16777216:=size
  have av : accessValid (W a) 8=true := by
    apply access_ok <;> dsimp [a,indexBase] <;> first | omega | (change _≤2^36;omega)
  obtain ⟨first,ip₁,src,cursor,index,mem,keep⟩:=salt_lookup s false a i pc indexPtr av (source.index r hr) row
  have dest := (keep .x19 (by decide) (by decide) (by decide) (by decide)).trans ptr
  have bounds:=salt_ok i
  have fit : AddrOK (saltAddress i) 24 := ⟨bounds.2.2,bounds.2.1.trans (by decide)⟩
  have room:=valid.2
  have copy:=copy_run .salt u ip₁ _ dst src dest 3 le_rfl fit ⟨valid.1,by omega⟩
  let v:=copyWords u 3
  have w:=copied_bytes (copied u _ dst src dest 3 (by decide) fit ⟨valid.1,by omega⟩
    (bounds.2.1.trans ((by decide : tdEnd≤proofBase).trans high))) fit.1 valid.1 (salt i)
    ((read_congr_mem u s _ _ mem).trans (source.salts i))
  have vp : v.pc=pcAt 476 := by rw [show v.pc=_ from copy_pc u 3,ip₁];rfl
  let y:=execInstrBr v (.ADDI .x19 .x19 24)
  have advance : Runs v y 1 1 := one 476 (by decide) _ (by rfl) _ _ vp rfl
  have yp : y.pc=pcAt 477 := by change v.pc+4=_;rw [vp];rfl
  have changed (q : Reg) (ne : q≠.x19) : y.getReg q=v.getReg q :=
    MachineState.getReg_setPC.trans (MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm ne))
  have afterKeep (q : Reg) (out : q∉([.x6,.x7,.x9,.x14,.x19,.x28] : List Reg)) : y.getReg q=s.getReg q := by
    apply (changed q (by intro e;subst q;simp at out)).trans
    apply (copy_keeps u 3 q (by intro e;subst q;simp at out)).trans
    apply keep <;> intro e <;> subst q <;> simp at out
  have yi : y.getReg .x14=W (indexAbove i 0) :=
    (changed _ (by decide)).trans ((copy_keeps u 3 _ (by decide)).trans (by simpa [indexAbove] using index))
  have yd : y.getReg .x19=W (dst+24) := by
    change v.getReg .x19+24=_
    rw [copy_keeps u 3 _ (by decide),dest];exact (BitVec.ofNat_add dst 24).symm
  have saltBytes:=w.congr_mem mem.symm (show y.mem=v.mem from rfl)
  have slen : (bytes (n:=24) (salt i)).length=24 := by simp [bytes]
  have outside:=saltBytes.outside
  rw [slen] at outside
  have table : Capacity y := by
    intro j hj;exact (outside _ (by change _<2^36;omega) (by omega) (Or.inl (by unfold proofBase at high;omega))).trans (tab _ hj)
  have ys:=source.after size dst 24 outside high valid.1 (by decide)
  have al:=valid.1
  obtain ⟨t,path,last,pout,_,cap,sources,same,written⟩:=ordinary_path y 0 24 (dst+24) i xs tree salt le_rfl yp
    ((afterKeep _ (by decide)).trans gp) table yi yd (by omega) ⟨by omega,by omega⟩ ys size
  refine ⟨t,?_,last,?_,?_,cap,sources,?_,?_⟩
  · have total:=((first.trans copy).trans advance).trans path
    by_cases even : i.val%2=0 <;> simpa [even,i] using total
  · exact pout.trans (congrArg W (by omega))
  · have ycursor:=(changed .x9 (by decide)).trans ((copy_keeps u 3 _ (by decide)).trans cursor)
    exact (same _ (by decide)).trans (ycursor.trans (congrArg W (by unfold a;omega)))
  · intro q out
    apply (same q (by intro h;apply out;cases q <;> simp_all)).trans
    apply afterKeep;intro h;apply out;cases q <;> simp_all
  · rw [record_eq];apply saltBytes.append
    · rw [slen];exact written
    · rw [slen];omega
    · rw [path_len];omega
    · rw [slen];omega
end CommitGolfCandidate.Chained.BinaryMachine.Open
