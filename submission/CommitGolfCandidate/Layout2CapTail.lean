import CommitGolfCandidate.Layout2CapClear
namespace CommitGolfCandidate.Layout2.Cap
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Layout2Helpers
open CommitGolfCandidate.Layout2.Quartet (checkImage)

private theorem dir_addr (r : Nat) (hr : r<952) :
    ((86016#64+signExtend12 3520)+addr tableBase)+((rv64_divu (addr r+6#64) 30#64) <<< (3:Nat))=addr (entryBase (tag r)) := by
  have quot : rv64_divu (addr r+6#64) 30#64=addr (tag r) := by
    rw [show 6#64=addr 6 from rfl,addr_add]
    unfold rv64_divu
    simp only [show (30#64 == 0#64)=false from rfl,Bool.false_eq_true,ite_false]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_udiv,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show r+6<2^64 by omega),
      Nat.mod_eq_of_lt (show tag r<2^64 by unfold tag;omega)]
    rfl
  rw [quot,BitVec.shiftLeft_eq_mul_twoPow]
  change addr (tableBase+85440)+addr (tag r)*addr 8=_
  rw [←BitVec.ofNat_mul,addr_add];congr 1;unfold entryBase;omega

/-- A directory mismatch rejects immediately; a match converts the entire suffix. -/
theorem tail {s u base n} (c : Cursor s u base n (n/952))
    (data : AtData s) (scratch : s.getReg .x10=addr scratchBase) (sp : s.getReg .x2=addr tableBase)
    (sep : scratchBase+2136≤base) (room : base+n≤tableBase) :
    let r:=n%952
    ∃ t h cost, h≤21+106*r ∧ Runs checkImage u t h cost ∧
      (if size (tag r)=r then t.pc=pc 1034 ∧ Output s t base n (result s base n) ∧ Kept temps s t
       else t.pc=pc 364) := by
  dsimp only
  let r:=n%952
  let m:=tag r
  have rs : r<952 := by dsimp [r];omega
  have mm : m<32 := by dsimp [m,tag];omega
  have mlim:=limits ⟨m,by omega⟩
  change size m≤952 ∧ offset m%2=0 ∧ offset m+16*size m≤337472 at mlim
  have small : tableBase+337472+16<2^64 := by decide
  have remR : u.getReg .x9=addr r := by rw [c.rem];congr 1;dsimp [r];omega
  obtain ⟨a,ra,pa,ma,regsA,ka⟩:=ctl_choose u c.start
  have pcA : a.pc=pc 1019 := by rw [remR,c.size,ult _ _ (by omega) (by decide)] at pa;simpa [show r<952 from rs] using pa
  obtain ⟨b,rb,pb,mb,regsB,kb⟩:=ctl_locate a pcA
  have dir : b.getReg .x19=addr (entryBase m) := by
    rw [regsB,if_pos rfl,regsA,regsA,remR,c.kept _ (by decide),sp];exact dir_addr r rs
  have diag:=(data.records (c.output.mem (mb.trans ma)).records (by omega)).directory m mm
  have align : entryBase m%8=0 := by unfold entryBase tableBase;omega
  have inRam : entryBase m+8≤MEMORY_BYTES := by unfold entryBase tableBase MEMORY_BYTES;omega
  obtain ⟨d,rd,pd,md,regsD,kd⟩:=ctl_compare b pb (by rw [dir];apply access_ok <;> omega)
  have remB : b.getReg .x9=addr r := by simp [regsB,regsA,remR]
  rw [dir,diag.1,remB] at pd
  have half : (BitVec.ofNat 16 (size m)).zeroExtend 64=addr (size m) := by
    apply BitVec.eq_of_toNat_eq;simp [addr,BitVec.toNat_setWidth,Nat.mod_eq_of_lt (by omega : size m<65536),Nat.mod_eq_of_lt (by omega : size m<2^64)]
  rw [half] at pd
  have runs:=(ra.thenDo rb).thenDo rd
  by_cases hit : size m=r
  · simp only [if_pos (show size (tag (n%952))=n%952 from hit)]
    have pcD : d.pc=pc 1029 := by simpa [hit] using pd
    obtain ⟨e,re,pe,me,regsE,ke⟩:=ctl_zeroTail d pcD
    have remE : d.getReg .x9=addr r := by simp [regsD,remB]
    rw [remE] at pe
    have stable:=c.kept.trans (ka.trans (kb.trans (kd.trans ke)))
    have prior:=c.output.mem (me.trans (md.trans (mb.trans ma)))
    by_cases z : r=0
    · have pcE : e.pc=pc 1034 := by simpa [z,addr] using pe
      have full : 952*(n/952)=n := by dsimp [r] at z;omega
      rw [full] at prior
      exact ⟨e,12,14+1,by omega,runs.thenDo re,pcE,prior,stable⟩
    · have ne : addr r≠0#64 := (addr_ne (by omega) (by decide : 0<2^64)).2 z
      have pcE : e.pc=pc 1030 := by simpa [ne] using pe
      have dirE : e.getReg .x19=addr (entryBase m) := by simp [regsE,regsD,dir]
      have addr4 : e.getReg .x19+4#64=addr (entryBase m+4) := by rw [dirE];exact addr_add _ _
      obtain ⟨v,rv,pv,mv,regsV,kv⟩:=ctl_partial e pcE (by rw [addr4];apply access_ok <;> omega)
      have baseV : v.getReg .x8=addr (base+952*(n/952)) := by simp [regsV,regsE,regsD,regsB,regsA,c.dst]
      have sizeV : v.getReg .x18=addr (size m) := by simp [regsV,regsE,remE,hit]
      have readE:=(data.records prior.records (by omega)).directory m mm
      have ptr : ((e.getWord32 (e.getReg .x19+4#64)).zeroExtend 64)=addr (offset m) := by
        rw [addr4,readE.2];apply BitVec.eq_of_toNat_eq
        simp [addr,BitVec.toNat_setWidth,Nat.mod_eq_of_lt (by omega : offset m<2^32),Nat.mod_eq_of_lt (by omega : offset m<2^64)] <;> omega
      have tbl : v.getReg .x19=addr (tableBase+offset m) := by rw [regsV];simp only [reduceCtorEq,ite_false,ite_true,ptr,stable _ (by decide : Reg.x2∉temps),sp,addr_add]
      have allN : 952*(n/952)+size m=n := by rw [hit];dsimp [r];omega
      have vStable:=stable.trans kv
      have pos : 1≤m := by
        by_contra h
        have nil : m=0 := by omega
        rw [nil] at hit
        exact z hit.symm
      obtain ⟨t,rt,pt,wt,kt⟩:=block_run (m:=m) (ret:=1034) data pos
        (by omega) (by simp [m,r]) sep room allN.le (prior.mem mv) pv baseV sizeV tbl
        ((vStable _ (by decide)).trans scratch) (by simp [regsV,regsE,regsD,regsB,regsA,c.eight])
        (by rw [regsV,if_pos rfl];decide)
      rw [allN] at wt
      exact ⟨t,_,_,by dsimp [r] at hit;omega,((runs.thenDo re).thenDo rv).thenDo rt,pt,wt,vStable.trans (kt.weaken call_temps)⟩
  · simp only [if_neg (show size (tag (n%952))≠n%952 from hit)]
    have ne : addr (size m)≠addr r := (addr_ne (by omega) (by omega)).2 hit
    exact ⟨d,11,14,by omega,runs,by simpa [ne] using pd⟩
end CommitGolfCandidate.Layout2.Cap
