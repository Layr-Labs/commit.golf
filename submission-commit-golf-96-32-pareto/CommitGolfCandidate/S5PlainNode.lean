import CommitGolfCandidate.S5PlainValue
import CommitGolfCandidate.S5MaskCore
import CommitGolfCandidate.S5PlainSites
namespace CommitGolfCandidate.S5Machine
open CommitGolf Chained CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 16000

def plainEnd (h : Height) (z : MachineState) :=
  if wireWidth h=256 then z else if wireWidth h=240 then execInstrBr z (.SH .x12 .x0 30) else maskOut z

def plainResult (H : Compression) (h : Height) (p : Nat) (s : MachineState) (f t : BitVec 12) :=
  plainEnd h (callState s .x21 .x22 f t (H (readBuffer s (srcAddr h p) 96)))

theorem plain_widths (h : Height) (simple : ¬chained h) :
    wireWidth h=256 ∨ wireWidth h=240 ∨ wireWidth h=238 :=
  (by decide +kernel : ∀ d : Height,¬chained d → wireWidth d=256 ∨ wireWidth d=240 ∨ wireWidth d=238) h simple

private theorem half_keep (q : MachineState) (r : Reg) : (execInstrBr q (.SH .x12 .x0 30)).getReg r=q.getReg r := by cases r <;> rfl

theorem plain_keeps (H : Compression) (d : Height) (p : Nat) (s : MachineState) (f t : BitVec 12) (r : Reg)
    (a : Reg.x10≠r) (b : Reg.x12≠r) (c : Reg.x31≠r) : (plainResult H d p s f t).getReg r=s.getReg r := by
  let z:=callState s .x21 .x22 f t (H (readBuffer s (srcAddr d p) 96))
  have keep : z.getReg r=s.getReg r:=call_register _ _ _ r _ _ _ a b
  unfold plainResult plainEnd;split
  · exact keep
  · split
    · exact (half_keep z r).trans keep
    · change (maskAnd z).getReg r=_
      simp only [maskAnd,maskLoad,execInstrBr,MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ c];exact keep

theorem plain_pc (H : Compression) (d : Height) (p : Nat) (s : MachineState) (f t : BitVec 12) (simple : ¬chained d) :
    (plainResult H d p s f t).pc=s.pc+BitVec.ofNat 64 (4*laneWords d) := by
  let z:=callState s .x21 .x22 f t (H (readBuffer s (srcAddr d p) 96))
  have ip : z.pc=s.pc+12:=call_pc ..
  change (plainEnd d z).pc=_
  rcases plain_widths d simple with w|w|w <;> simp [plainEnd,laneWords,mask240,w,ip,mask_pc,execInstrBr,BitVec.add_assoc] <;> rfl

theorem raw_call (o : Oracle) {s d p f t} (addr : Addr s d p f t) (c : Common s) (inside : p<count d)
    (n : Nat) (pc : s.pc=pcAt n) (op0 : Site .commit n (.ADDI .x10 .x21 f)) (op1 : Site .commit (n+1) (.ADDI .x12 .x22 t))
    (op2 : Site .commit (n+2) .ECALL) :
    Runs .commit true o s (callState s .x21 .x22 f t (o.compression (readBuffer s (srcAddr d p) 96))) 3 10 1 := by
  obtain ⟨rs,sa,rd,da⟩:=buffers inside
  obtain ⟨from_,to_⟩:=ready_addr addr
  have xs : srcAddr d p<2^64:=by change _≤2^36 at rs;omega
  have ys : dstAddr d p<2^64:=by change _≤2^36 at rd;omega
  intro fuel
  have run:=execute_compression s n fuel .x21 .x22 f t op0 op1 op2 pc c.mode c.len c.kind (by
    simp only [from_,to_,rangeValid,BitVec.toNat_ofNat,Nat.mod_eq_of_lt xs,Nat.mod_eq_of_lt ys,rs,rd,sa,da,decide_true,and_self])
  have same : ((prepareCall s .x21 .x22 f t).getReg .x10).toNat=srcAddr d p := by rw [from_,BitVec.toNat_ofNat,Nat.mod_eq_of_lt xs]
  rw [run,same];unfold Late.hash;erw [oracle_run_public_bind o (.inl _)]
  simp only [oracle_run_bind,oracle_run_pure,pure_bind,bind_assoc,Nat.add_zero];rfl

theorem plain_observed (o : Oracle) {s h p f t} (addr : Addr s h p f t) (c : Common s) (hp : p<count h)
    (simple : ¬chained h) (n : Nat) (pc : s.pc=pcAt n)
    (op0 : Site .commit n (.ADDI .x10 .x21 f)) (op1 : Site .commit (n+1) (.ADDI .x12 .x22 t))
    (op2 : Site .commit (n+2) .ECALL) (op3 : mask240 h=true → Site .commit (n+3) (.SH .x12 .x0 30))
    (small : n+5<18492) (narrow : Mask238Sites h (n+3)) :
    Runs .commit true o s (plainResult o.compression h p s f t) (laneWords h) (laneWords h+7) 1 := by
  have call:=raw_call o addr c hp n pc op0 op1 op2
  let z:=callState s .x21 .x22 f t (o.compression (readBuffer s (srcAddr h p) 96))
  have next : z.pc=pcAt (n+3) := by
    rw [show z.pc=s.pc+12 from call_pc ..,pc]
    unfold pcAt
    change BitVec.ofNat 64 (4096+4*n)+BitVec.ofNat 64 12=_
    rw [←BitVec.ofNat_add];apply congrArg (BitVec.ofNat 64);omega
  have dest : z.getReg .x12=BitVec.ofNat 64 (dstAddr h p):=(writeBits_register (prepareCall s .x21 .x22 f t) _ _ .x12).trans (ready_addr addr).2
  obtain ⟨_,_,room,align⟩:=buffers hp
  rcases plain_widths h simple with full|half|low
  · simpa [plainResult,plainEnd,laneWords,mask240,full] using call
  · have which : mask240 h=true:=by simp [mask240,half]
    have valid : memoryArgumentsValid z (.SH .x12 .x0 30)=true := by
      change accessValid (z.getReg .x12+signExtend12 30) 2=true
      rw [dest,show signExtend12 30=BitVec.ofNat 64 30 by decide,←BitVec.ofNat_add]
      apply access_ok <;> first | omega | (change _≤2^36 at room;omega)
    have one:=runs_step (coins:=true) (o:=o) (op3 which z next) (show ordinaryStep z (.base (.SH .x12 .x0 30))=some (execInstrBr z (.SH .x12 .x0 30)) by simp only [ordinaryStep,valid,↓reduceIte])
    simpa [plainResult,plainEnd,laneWords,mask240,half,z,instructionCycles] using runs_comp call one
  · obtain ⟨a,b,e⟩:=narrow low
    have tail:=mask_core_run o z (n+3) _ next dest room align (decoded_site (by omega) a)
      (decoded_site (by omega) b) (decoded_site (by omega) e)
    simpa [plainResult,plainEnd,laneWords,mask240,low,z] using runs_comp call tail
end CommitGolfCandidate.S5Machine
