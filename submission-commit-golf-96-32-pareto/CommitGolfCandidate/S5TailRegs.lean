import CommitGolfCandidate.S5TailControl
namespace CommitGolfCandidate.S5Machine
open CommitGolfCandidate.Chained
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

structure TailFrame (d : Height) (p : Nat) (s : MachineState) : Prop extends Common s where
  selectMask : wireWidth d=238 → s.getReg .x30=heldMask d
  pc : s.pc=pcAt (if p<count d then tailPC d else passEnd d)
  src : s.getReg .x21=BitVec.ofNat 64 (srcAddr d p)
  dst : s.getReg .x22=BitVec.ofNat 64 (dstAddr d p)
  counter : s.getReg .x20=BitVec.ofNat 64 (count d-p)
  flag : s.getReg .x7=BitVec.ofNat 64 (p%2)

private theorem flag_reg (s : MachineState) (o : Bool) (flag : s.getReg .x7=(if o then 1 else 0)) :
    s.regs .x7=(if o then 1 else 0) :=flag

set_option maxRecDepth 16000 in
theorem tail_regs (s : MachineState) (odd : Bool) (flag : s.getReg .x7=(if odd then 1 else 0)) :
    let t:=tailUpdated s odd
    t.getReg .x21=s.getReg .x21+96 ∧ t.getReg .x22=s.getReg .x22+(if odd then 64 else 32) ∧
    t.getReg .x20=s.getReg .x20-1 ∧ t.getReg .x7=(if odd then 0 else 1) ∧ t.mem=s.mem := by
  have f:=flag_reg s odd flag
  cases odd <;> simp [tailUpdated,tailOps,execInstrBr,MachineState.getReg,MachineState.setReg,MachineState.setPC,
    f,signExtend12,BitVec.sub_eq_add_neg,BitVec.add_assoc] <;> rfl

theorem tail_keeps (s : MachineState) (odd : Bool) (flag : s.getReg .x7=(if odd then 1 else 0))
    (r : Reg) (a : Reg.x21≠r) (b : Reg.x22≠r) (c : Reg.x20≠r) (d : Reg.x7≠r) :
    (tailUpdated s odd).getReg r=s.getReg r := by
  have one (op : Instr) (mem : op∈tailOps odd) (q : MachineState) : (execInstrBr q op).getReg r=q.getReg r := by
    have shape : op=.ADDI .x21 .x21 96 ∨ op=.ADDI .x22 .x22 32 ∨ op=.BEQ .x7 .x0 8 ∨ op=.XORI .x7 .x7 1 ∨ op=.ADDI .x20 .x20 4095 := by
      cases odd <;> simp_all [tailOps] <;> tauto
    rcases shape with rfl|rfl|rfl|rfl|rfl
    · exact MachineState.getReg_setReg_ne _ _ _ _ a
    · exact MachineState.getReg_setReg_ne _ _ _ _ b
    · change (if q.getReg .x7==q.getReg .x0 then q.setPC (q.pc+signExtend13 8) else q.setPC (q.pc+4)).getReg r=_;split <;> rfl
    · exact MachineState.getReg_setReg_ne _ _ _ _ d
    · exact MachineState.getReg_setReg_ne _ _ _ _ c
  have all (xs : List Instr) (mem : ∀ op∈xs,op∈tailOps odd) (q : MachineState) :
      (xs.foldl execInstrBr q).getReg r=q.getReg r := by
    induction xs generalizing q with
    | nil=>rfl
    | cons op xs ih=>exact (ih (fun x hx=>mem x (List.mem_cons_of_mem _ hx)) _).trans (one op (mem _ (by simp)) q)
  exact all _ (fun _ h=>h) s

theorem tail_addresses {d p s} (f : TailFrame d p s) : Addr s d p 0 0 := by
  constructor
  · rw [f.src];exact BitVec.add_zero _
  · rw [f.dst];exact BitVec.add_zero _

def tailOdd (p : Nat) := decide (p%2=1)
def tailResult (o : Oracle) (d : Height) (p : Nat) (s : MachineState) :=
  let t:=tailUpdated (plainResult o.compression d p s 0 0) (tailOdd p)
  t.setPC (pcAt (if p+1<count d then tailPC d else passEnd d))

set_option maxHeartbeats 1200000 in
attribute [local irreducible] readBuffer writeBits callState in
theorem tail_step (o : Oracle) {d p s} (f : TailFrame d p s) (simple : ¬chained d) (inner : d.val<23)
    (hp : p<count d) (remainderPos : 0<remainder d) (pad : gaps s) :
    let t:=tailResult o d p s
    let n:=laneWords d+(tailOps (tailOdd p)).length+1
    Runs .commit true o s t n (n+7) 1 ∧ TailFrame d (p+1) t ∧ NodeEffect o.compression d p s t := by
  let odd:=tailOdd p
  let r:=plainResult o.compression d p s 0 0
  let u:=tailUpdated r odd
  let t:=tailResult o d p s
  obtain ⟨range,src,dst,hash,mask,maskN⟩:=tail_table d simple remainderPos
  have cutOk : tailPC d+3<18492 := (by decide +kernel : ∀ d : Height,tailPC d+3<18492) d
  have start : s.pc=pcAt (tailPC d):=f.pc.trans (by rw [if_pos hp])
  have addr:=tail_addresses f
  have first : Runs .commit true o s r (laneWords d) (laneWords d+7) 1 :=
    plain_observed _ addr f.toCommon hp simple _ start (decoded_site (by omega) src) (decoded_site (by omega) dst)
      (decoded_site range hash) (fun h=>decoded_site cutOk (mask h)) ((by decide +kernel : ∀ h : Height,tailPC h+5<18492) d) maskN
  have keep (reg : Reg) (a : Reg.x10≠reg) (b : Reg.x12≠reg) (c : Reg.x31≠reg) : r.getReg reg=s.getReg reg := plain_keeps o.compression d p s 0 0 reg a b c
  have flag : r.getReg .x7=(if odd then 1 else 0) := by
    rw [keep _ (by decide) (by decide) (by decide),f.flag];by_cases eq:p%2=1
    · simp [odd,tailOdd,eq]
    · simp [odd,tailOdd,eq,show p%2=0 by omega]
  have ip : r.pc=pcAt (tailCtrlPC d) := by
    rw [show r.pc=_ from plain_pc o.compression d p s 0 0 simple];rw [start,pcAt,pcAt,←BitVec.ofNat_add];apply congrArg (BitVec.ofNat 64);unfold tailCtrlPC;omega
  have ctl:=controller_run o d simple inner r odd flag ip
  have beforeGate:=controller_pc r d simple inner odd flag ip
  obtain ⟨ua,ub,uc,uf,um⟩:=tail_regs r odd flag
  have nextc : u.getReg .x20=BitVec.ofNat 64 (count d-(p+1)) := by
    rw [show u.getReg .x20=_ from uc,keep _ (by decide) (by decide) (by decide),f.counter]
    exact (BitVec.ofNat_sub_ofNat_of_le (w:=64) (count d-p) 1 (by decide) (by omega)).trans (congrArg (BitVec.ofNat 64) (by omega))
  have nz : (u.getReg .x20 != 0)=decide (p+1<count d) := by
    rw [nextc];by_cases more : p+1<count d
    · rw [decide_eq_true more];apply bne_iff_ne.mpr;intro eq
      have bd : count d≤16777216:=level_count_le _
      have v:=congrArg BitVec.toNat eq;rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at v;change _=0 at v;omega
    · rw [show count d-(p+1)=0 by omega,decide_eq_false more];rfl
  have gate:=gate_run false (decide (p+1<count d)) _ _ u o beforeGate (tail_gate d simple inner) nz
  have landed : u.setPC (gatePC (tailPC d) (passEnd d) (decide (p+1<count d)))=t := by
    change u.setPC (pcAt (if decide (p+1<count d) then tailPC d else passEnd d))=u.setPC (pcAt (if p+1<count d then tailPC d else passEnd d));simp
  rw [landed] at gate
  have same (reg : Reg) (x : Reg.x10≠reg) (y : Reg.x12≠reg) (a : Reg.x21≠reg) (b : Reg.x22≠reg) (c : Reg.x20≠reg) (k : Reg.x7≠reg) (l : Reg.x31≠reg) :
      t.getReg reg=s.getReg reg := (tail_keeps r odd flag reg a b c k).trans (keep _ x y l)
  have cm : Common t := by
    obtain ⟨q1,q2,q3,q4,q5,q6,q7,q8,q9⟩:=f.toCommon
    constructor <;> apply (same _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans <;> assumption
  refine ⟨?_,⟨cm,fun w=>(same .x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (f.selectMask w),rfl,?_,?_,nextc,?_⟩,?_⟩
  · have all:=runs_comp (runs_comp first ctl) gate
    change Runs .commit true o s t _ _ _
    convert all using 1 <;> simp [gateWords,odd] <;> omega
  · change u.getReg .x21=_
    rw [show u.getReg .x21=_ from ua,keep _ (by decide) (by decide) (by decide),f.src]
    change BitVec.ofNat 64 _+BitVec.ofNat 64 96=_
    rw [←BitVec.ofNat_add];apply congrArg (BitVec.ofNat 64);unfold srcAddr;rw [source_address,source_address];omega
  · change u.getReg .x22=_
    rw [show u.getReg .x22=_ from ub,keep _ (by decide) (by decide) (by decide),f.dst]
    by_cases e : p%2=1 <;> simp only [odd,tailOdd,e,decide_true,decide_false,ite_true,ite_false,Bool.false_eq_true] <;>
      first | (change BitVec.ofNat 64 _+BitVec.ofNat 64 64=_;rw [←BitVec.ofNat_add];apply congrArg (BitVec.ofNat 64);unfold dstAddr;simp only [binaryAddress];unfold Late.gapOffset;omega)
            | (change BitVec.ofNat 64 _+BitVec.ofNat 64 32=_;rw [←BitVec.ofNat_add];apply congrArg (BitVec.ofNat 64);unfold dstAddr;simp only [binaryAddress];unfold Late.gapOffset;omega)
  · change u.getReg .x7=_
    rw [show u.getReg .x7=_ from uf];by_cases e:p%2=1 <;>
      simp [odd,tailOdd,e,show (p+1)%2=(if p%2=1 then 0 else 1) by split <;> omega]
  · have eff:=plain_effect o.compression addr pad hp simple f.selectMask
    constructor
    · exact (read_congr_mem t r _ _ um).trans eff.value
    · intro a n fit sep extra;exact (read_congr_mem t r a n um).trans (eff.outside _ _ fit sep extra)
end CommitGolfCandidate.S5Machine
