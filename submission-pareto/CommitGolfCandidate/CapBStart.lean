import CommitGolfCandidate.CapBInvariant
import CommitGolfCandidate.CapBWalk
import CommitGolfCandidate.CapBRaw
namespace CommitGolfCandidate.CapB
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.GroupedOpening (openingImage)
open TwoPermutationPrototype.GroupedOpening.CapB (handlers)
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000

structure CapEntry (gs : List Nat) (heap : Nat→D) (k : Nat) (s : MachineState) : Prop where
  pcAt : s.pc=pc 6960
  count : k≤16777216
  marked : capIsMarked gs 1 8=true
  marks : ByteMarks gs s
  x26 : s.getReg .x26=addr markBase
  x25 : s.getReg .x25=addr heapBase
  x27 : s.getReg .x27=256#64
  x23 : s.getReg .x23=1#64
  x20 : s.getReg .x20=addr proofBase
  x21 : s.getReg .x21=addr (capStart k)
  source : ∀ n,n<512 → ∀ i,i<4 → gword s (heapBase+32*n+8*i)=dw (heap n) i

theorem limit_frontier (gs : List Nat) : (capFrontierNodes gs 1 8).length≤128 := by
  rw [cap_frontier_length];exact TwoPermutationPrototype.production_boundary_bound _

def extraInit (k : Nat) := if k%4=0 then 0 else 2

theorem start {gs H k s} (e : CapEntry gs H k s) :
    ∃ ref u z,Run openingImage s u (201+extraInit k) (297+extraInit k) ∧
    Env gs H k ref ∧ Inv H k ref z [] u ∧ u.pc=pc 661 ∧ u.getReg .x6=addr 1 ∧
    (∀ w : Word, markBase+512≤w.toNat → ref.getMem w=s.getMem w) := by
  obtain ⟨a,ra,pa,marked,kept,frame⟩:=prep_done s gs e.pcAt e.x26 e.marks
  have env : Env gs H k a := by
    refine ⟨e.count,marked,?_⟩;intro n hn i hi
    have inside : heapBase+32*n+8*i<2^64 := by unfold heapBase;omega
    exact (frame _ (Or.inr (by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt inside];unfold heapBase markBase;omega))).trans (e.source n hn i hi)
  obtain ⟨b,rb,pb,mb,regsB⟩:=nav_init a pa
  have x21 : a.getReg .x21=addr (capStart k) := (kept _ (by decide)).trans e.x21
  have mask : ((addr (capStart k)) &&& 7#64)=addr (capStart k%8) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and,BitVec.toNat_ofNat,show (7#64).toNat=2^3-1 from rfl,Nat.and_two_pow_sub_one_eq_mod]
    simp [addr,Nat.mod_mod_of_dvd,show 8∣2^64 by decide];omega
  have alg : (addr (capStart k%8)=0#64) ↔ k%4=0 := by
    constructor
    · intro eq;have number:=congrArg BitVec.toNat eq;change (capStart k%8)%2^64=0 at number;unfold capStart proofBase at number;omega
    · intro ok;have zero : capStart k%8=0 := by unfold capStart proofBase;omega
      rw [zero]
  rw [x21,mask] at pb regsB
  have setup {d : MachineState} (pcD : d.pc=pc 7162) (mem : d.mem=a.mem)
      (copy : d.getReg .x14=addr (copyDest k)) (dest : d.getReg .x21=addr (work k))
      (regs : ∀ r,r≠.x21 → r≠.x14 → d.getReg r=b.getReg r) :
      ∃ u,Run openingImage d u 1 1 ∧ Inv H k a (u.getReg .x22) [] u ∧ u.pc=pc 661 ∧ u.getReg .x6=addr 1 := by
    obtain ⟨u,ru,pu,mu,regU⟩:=nav_enter d pcD
    refine ⟨u,ru,?_,pu,?_⟩
    · refine ⟨(Buffer.empty a (work k)).mem (mu.trans mem),?_,?_,rfl,?_,?_,?_,?_,?_,?_,?_⟩
      · rw [regU,regs _ (by decide) (by decide),regsB];rfl
      · exact (regU _).trans dest
      · simpa [regU,regs _ (by decide : Reg.x20≠.x21) (by decide),regsB,kept _ (by decide : Reg.x20∉_),e.x20]
      · rw [regU,regs _ (by decide) (by decide),regsB];exact (kept _ (by decide)).trans e.x23
      · rw [regU,regs _ (by decide) (by decide),regsB];rfl
      · rw [regU,regs _ (by decide) (by decide),regsB];exact (kept _ (by decide)).trans e.x25
      · rw [regU,regs _ (by decide) (by decide),regsB];exact (kept _ (by decide)).trans e.x26
      · rw [regU,regs _ (by decide) (by decide),regsB];exact (kept _ (by decide)).trans e.x27
      · exact (regU _).trans copy
    · rw [regU,regs _ (by decide) (by decide),regsB];rfl
  by_cases align : k%4=0
  · have zero:=alg.2 align
    obtain ⟨u,ru,iu,pu,nu⟩:=setup (d:=b) (by simpa [zero] using pb) mb (by simp [regsB,zero,copyDest,align,addr]) (by simp [regsB,work,align,x21]) (fun _ _ _=>rfl)
    exact ⟨a,u,_,by simpa [extraInit,align] using (ra.thenDo rb).thenDo ru,env,iu,pu,nu,fun w h=>frame w (Or.inr h)⟩
  · have nz:=mt alg.1 align
    obtain ⟨d,rd,pd,md,regsD⟩:=nav_useScratch b (by simpa [nz] using pb)
    obtain ⟨u,ru,iu,pu,nu⟩:=setup pd (md.trans mb) (by simp [regsD,regsB,x21,copyDest,align]) (by simp [regsD,work,align,scratch,addr])
      (by intro r h l;simp [regsD,h.symm,l.symm])
    exact ⟨a,u,_,by simpa [extraInit,align] using ((ra.thenDo rb).thenDo rd).thenDo ru,env,iu,pu,nu,fun w h=>frame w (Or.inr h)⟩

theorem walk_root {gs H k s} (e : CapEntry gs H k s) :
    let ns:=capFrontierNodes gs 1 8
    let cost:=walkCost gs 1 5 0
    ∃ ref t z,Run openingImage s t (201+extraInit k+cost) (297+extraInit k+cost) ∧
    Inv H k ref z ns t ∧ t.pc=pc 707 ∧ (∀ w : Word,markBase+512≤w.toNat → ref.getMem w=s.getMem w) := by
  obtain ⟨ref,u,z,ru,env,iu,pu,nu,frame⟩:=start e
  obtain ⟨t,rt,pt,it,_⟩:=walk (walk_api z env) 5 1 [] u (by decide) (by decide) (fun _=>e.marked)
    (by have:=limit_frontier gs;change 0+(capFrontierNodes gs 1 8).length≤256;omega) iu pu nu
  exact ⟨ref,t,z,ru.thenDo rt,by change Inv H k ref z ([]++capFrontierNodes gs 1 8) t at it;exact it,by simpa only [if_true] using pt,frame⟩
end CommitGolfCandidate.CapB
