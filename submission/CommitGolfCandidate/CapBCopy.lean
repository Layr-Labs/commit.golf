import CommitGolfCandidate.CapBFlow
import CommitGolfCandidate.CapBWalk
import CommitGolfCandidate.Layout2Memory
namespace CommitGolfCandidate.CapB
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Layout2Helpers
open TwoPermutationPrototype.GroupedOpening (openingImage)
set_option maxRecDepth 12000
set_option maxHeartbeats 1400000

theorem addr_inj {a b : Nat} (aFit : a<2^64) (bFit : b<2^64) : addr a=addr b ↔ a=b := by
  constructor
  · intro eq;have val:=congrArg BitVec.toNat eq
    simpa only [addr,BitVec.toNat_ofNat,Nat.mod_eq_of_lt aFit,Nat.mod_eq_of_lt bFit] using val
  · intro e;rw [e]

theorem copyLoop (s : MachineState) (a b N i : Nat) (bound : i≤N) (space : a+N≤b ∧ b+N≤MEMORY_BYTES)
    (here : s.pc=(if i=N then pc 6670 else pc 6665))
    (src : s.getReg .x6=addr (a+i)) (dst : s.getReg .x14=addr (b+i)) (stop : s.getReg .x21=addr (a+N))
    (orig : MachineState) (buff : Layout2.Writes orig s b i (fun j=>gbyte orig (a+j))) :
    ∃ t, Run openingImage s t (5*(N-i)) (5*(N-i)) ∧ t.pc=pc 6670 ∧
      t.getReg .x14=addr (b+N) ∧ t.getReg .x20=s.getReg .x20 ∧ Layout2.Writes orig t b N (fun j=>gbyte orig (a+j)) := by
  by_cases end_ : i=N
  · subst i;exact ⟨s,by simpa using Run.zero openingImage s,by simpa using here,dst,rfl,buff⟩
  have lim : MEMORY_BYTES<2^64 := by decide
  obtain ⟨u,ru,pu,mu,rU⟩:=nav_copyRead s (by simpa [end_] using here) (by rw [src];exact access_ok _ _ (by omega) (by omega))
  obtain ⟨v,rv,pv,mv,rV⟩:=nav_copyWrite u pu (by rw [rU];change accessValid (s.getReg .x14) 1=true;rw [dst];exact access_ok _ _ (by omega) (by omega))
  obtain ⟨w,rw_,pw,mw,rW⟩:=nav_copyNext v pv
  have read : s.getByte (s.getReg .x6)=gbyte orig (a+i) := by rw [src];exact buff.outside _ (by omega) (Or.inl (by omega))
  have store : w.mem=(s.setByte (addr (b+i)) (gbyte orig (a+i))).mem := by
    rw [mw,mv];simp only [rU,ite_true,ite_false,reduceCtorEq,dst,read,BitVec.setWidth_setWidth_of_le]
    have shrink (v : Byte) : (v.zeroExtend 64).truncate 8=v := by change (v.setWidth 64).setWidth 8=v;rw [BitVec.setWidth_setWidth_of_le _ (by decide),BitVec.setWidth_eq]
    rw [shrink]
    change (u.setByte _ _).mem=(s.setByte _ _).mem
    simp only [MachineState.setByte,MachineState.setMem,MachineState.getMem,mu]
  have nextW := (buff.store (gbyte orig (a+i)) rfl (by omega)).move (s':=orig) rfl store
  have advance (x : Nat) : addr (x+i)+1#64=addr (x+(i+1)) := by change addr (x+i)+addr 1=_;rw [add_addr];congr 1
  have x6 : w.getReg .x6=addr (a+(i+1)) := by simp [rW,rV,rU,src,advance]
  have x14 : w.getReg .x14=addr (b+(i+1)) := by simp [rW,rV,rU,dst,advance]
  have endW : w.getReg .x21=addr (a+N) := by simp [rW,rV,rU,stop]
  have atW : w.pc=if i+1=N then pc 6670 else pc 6665 := by
    rw [pw];simp only [rV,rU,reduceCtorEq,ite_false,src,advance,stop]
    by_cases done_ : i+1=N
    · simp [done_]
    · have diff : addr (a+(i+1))≠addr (a+N) := by rw [ne_eq,addr_inj (by omega) (by omega)];omega
      simp [done_,diff]
  obtain ⟨t,rt,pt,dt,keep,out⟩:=copyLoop w a b N (i+1) (by omega) space atW x6 x14 endW orig nextW
  have len : 1+1+3+5*(N-(i+1))=5*(N-i) := by omega
  exact ⟨t,by simpa only [len] using ((ru.thenDo rv).thenDo rw_).thenDo rt,pt,dt,
    keep.trans (by simp [rW,rV,rU]),out⟩
termination_by N-i

theorem scratchCopy (s : MachineState) (b N : Nat) (space : 12288+N≤b ∧ b+N≤MEMORY_BYTES)
    (here : s.pc=pc 6663) (dst : s.getReg .x14=addr b) (stop : s.getReg .x21=addr (12288+N)) :
    ∃ t, Run openingImage s t (3+5*N) (3+5*N) ∧ t.pc=pc 6671 ∧ t.getReg .x21=addr (b+N) ∧
    t.getReg .x20=s.getReg .x20 ∧ Layout2.Writes s t b N (fun j=>gbyte s (12288+j)) := by
  have lim : MEMORY_BYTES<2^64 := by decide
  obtain ⟨u,ru,pu,mu,rU⟩:=nav_copyStart s here
  have atU : u.pc=if 0=N then pc 6670 else pc 6665 := by
    rw [pu,stop];by_cases z : 0=N
    · subst N;rfl
    · have ne : 12288#64≠addr (12288+N) := by change addr 12288≠_;rw [ne_eq,addr_inj (by decide) (by omega)];omega
      simp [z,ne]
  obtain ⟨v,rv,pv,dv,ov,bv⟩:=copyLoop u 12288 b N 0 (by omega) space atU (by simp [rU,addr]) (by simp [rU,dst]) (by simp [rU,stop]) s
    ((Layout2.writes_zero s _ _).move rfl mu)
  obtain ⟨t,rt,pt,regM,regT⟩:=nav_copyDone v pv
  have len : 2+5*(N-0)+1=3+5*N := by omega
  exact ⟨t,by simpa only [len] using (ru.thenDo rv).thenDo rt,pt,by simp [regT,dv],by simp [regT,ov,rU],bv.move rfl regM⟩
end CommitGolfCandidate.CapB
