import CommitGolfCandidate.S5Headers
import CommitGolfCandidate.S5Code
namespace CommitGolfCandidate.S5Machine
open CommitGolfCandidate.Chained
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

structure Common (s : MachineState) : Prop where
  mode : s.getReg .x5=0
  len : s.getReg .x11=96
  kind : s.getReg .x13=0
  base : s.getReg .x18=4294975488
  root : s.getReg .x9=4294971392
  scratch : s.getReg .x24=7113547776
  stride₁ : s.getReg .x25=4032
  stride₂ : s.getReg .x26=4032
  stride₃ : s.getReg .x27=4032

theorem seed_inputs (s : MachineState) (c : Common s) : Agrees phaseSeed s := by
  intro r v eq;cases r <;> simp only [phaseSeed,Option.some.injEq,reduceCtorEq] at eq <;>
    subst v <;> first | rfl | exact c.mode | exact c.len | exact c.kind | exact c.base | exact c.root |
      exact c.scratch | exact c.stride₁ | exact c.stride₂ | exact c.stride₃

private theorem common_outputs : ∀ d : Height,
    completeHeader d .x5=some 0 ∧ completeHeader d .x11=some 96 ∧ completeHeader d .x13=some 0 ∧
    completeHeader d .x18=some 4294975488 ∧ completeHeader d .x9=some 4294971392 ∧
    completeHeader d .x24=some 7113547776 ∧ completeHeader d .x25=some 4032 ∧
    completeHeader d .x26=some 4032 ∧ completeHeader d .x27=some 4032 := by decide +kernel

structure EnteredFrame (s : MachineState) (d : Height) : Prop extends Common s where
  pc : s.pc=pcAt (bodyEntry d)
  src : s.getReg .x21=BitVec.ofNat 64 (nodeAddress d.val 0+cursorBias d)
  dst : s.getReg .x22=BitVec.ofNat 64 (nodeAddress (d.val+1) 0+cursorBias d)
  counter : d.val<23 → s.getReg .x20=BitVec.ofNat 64 (if tileSize d=0 then remainder d else tiles d)
  tag : chained d → s.getReg .x29=BitVec.ofNat 64 (2^63+256*(d.val+1))
  mask : chained d → s.getReg .x30=BitVec.ofNat 64 (2^(wireWidth d-224)-1)
  parity : tileSize d=0 → d.val<23 → s.getReg .x7=0

theorem entered_frame (d : Height) (s : MachineState) (atStart : s.pc=pcAt (pureEntry d)) (c : Common s) :
    EnteredFrame (entered s d) d ∧ (entered s d).mem=s.mem := by
  obtain ⟨legal,size,src,dst,ctr,tag,parity⟩:=header_facts d
  have ok:=fun op mem=>List.all_eq_true.mp legal op mem
  have known : Agrees (completeHeader d) (entered s d):=known_header _ _ _ ok (seed_inputs s c)
  obtain ⟨mem,pc⟩:=header_properties (headerOps d) s ok
  obtain ⟨q5,q11,q13,q18,q9,q24,q25,q26,q27⟩:=common_outputs d
  refine ⟨⟨⟨known _ _ q5,known _ _ q11,known _ _ q13,known _ _ q18,known _ _ q9,
    known _ _ q24,known _ _ q25,known _ _ q26,known _ _ q27⟩,?_,known _ _ src,known _ _ dst,
    fun h=>known _ _ (ctr h),fun h=>known _ _ (tag h).1,fun h=>known _ _ (tag h).2,
    fun a b=>known _ _ (parity a b)⟩,mem⟩
  change (List.foldl execInstrBr s (headerOps d)).pc=_
  rw [pc,atStart,←size,pcAt,pcAt,←BitVec.ofNat_add];apply congrArg (BitVec.ofNat 64);omega

def parentSetup : List Instr :=
  [.LUI .x25 1,.ADDI .x25 .x25 4032,.LUI .x26 1,.ADDI .x26 .x26 4032,.LUI .x27 1,.ADDI .x27 .x27 4032]
private theorem setup_table : ∀ i : Fin 6, decodeInstruction (atWord .commit ⟨7224+i.val,by change 7224+i.val<18492;omega⟩)=
    some (.base (parentSetup.get ⟨i.val,i.isLt⟩)) := by decide +kernel
theorem parents_setup_run (s : MachineState) (pc : s.pc=pcAt 7224) (fuel : Nat) :
    execute commitImage (fuel+6) s true=
      (do let r←execute commitImage fuel (parentSetup.foldl execInstrBr s) true;return r.charge 6 0) := by
  apply execute_linear .commit true parentSetup 7224 s fuel pc
  · intro op hm;apply header_straight;exact List.all_eq_true.mp (by decide : parentSetup.all setupOp) op hm
  · intro i hi;change i<6 at hi;apply site (p:=.commit) (by change 7224+i<18492;omega);exact setup_table ⟨i,hi⟩
theorem entered_plain_mask (d : Height) (s : MachineState) (cm : Common s) (w : wireWidth d=238) :
    (entered s d).getReg .x30=16383 := by
  have pureOps := (header_facts d).1
  have known:=known_header (headerOps d) phaseSeed s (List.all_eq_true.mp pureOps) (seed_inputs s cm)
  exact known .x30 16383 ((by decide +kernel : ∀ h : Height,wireWidth h=238→completeHeader h .x30=some 16383) d w)
end CommitGolfCandidate.S5Machine
