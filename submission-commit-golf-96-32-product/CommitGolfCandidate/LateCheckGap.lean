import CommitGolfCandidate.LateCheckHeader
import CommitGolfCandidate.LateCheckCall
import CommitGolfCandidate.LateCheckCopies

namespace CommitGolfCandidate.Late.Check.Micro
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open CommitGolfCandidate.Late.Open (W wordAt)
def da (odd : Bool) : Nat := if odd then 192 else 160
def ga (odd : Bool) : Nat := if odd then 184 else 224
def sa (odd : Bool) : Nat := if odd then 160 else 232
def regBit (odd : Bool) : Word := if odd then 1 else 0

theorem BlockResult.keep {s : MachineState} {b : Part} (h : BlockResult b s) (r : Reg)
    (eq : b.equation r=Open.original r) : (b.after s).getReg r=s.getReg r := by
  rw [h.regs,eq];cases r <;> rfl

private theorem word_read (s : MachineState) (a : Nat) (al : a%8=0) :
    wordAt s a=readBuffer s a 8 :=
  (read_digest_word s a 0 al (by decide)).symm.trans (read_buffer_slice s a 32 0 8 (by decide))

structure Gap (s t : MachineState) (odd : Bool) : Prop where
  pc : t.pc=pcAt 421
  dest : t.getReg .x12=W (sa odd)
  keep : ∀ r, r≠.x12 → t.getReg r=s.getReg r
  outside : Open.Outside s t (ga odd) 8
  zero : readBuffer t (ga odd) 8=0

private theorem written (s : MachineState) (a : Nat) (v : Word) (t : MachineState)
    (mem : t.mem=(s.setMem (W a) v).mem) (al : a%8=0) (small : a<2^64) :
    Open.Outside s t a 8 ∧ readBuffer t a 8=v := by
  have word (q : Nat) (hq : q<2^64) :
      wordAt t q=if q=a then v else wordAt s q := by
    change t.mem (W q)=_;rw [mem];change (if W q == W a then v else s.mem (W q))=_
    by_cases same : q=a
    · subst q;simp [wordAt,W]
    · have ne : W q≠W a := by intro e;have :=congrArg BitVec.toNat e;simp only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hq,Nat.mod_eq_of_lt small] at this;contradiction
      rw [if_neg (fun h=>ne (beq_iff_eq.mp h)),if_neg same];rfl
  constructor
  · intro q hq _ out;rw [word _ (by unfold MEMORY_BYTES at hq;omega),if_neg (by omega)]
  · rw [←word_read _ _ al,word _ small,if_pos rfl]

private theorem clearAt (odd : Bool) (s : MachineState) (pc : s.pc=pcAt (if odd then 417 else 420))
    (dest : s.getReg .x12=W (sa odd)) :
    let t:= (s.setMem (W (ga odd)) 0).setPC (s.pc+4)
    Runs s t 1 1 ∧ t.pc=pcAt (if odd then 418 else 421) := by
  cases odd
  · constructor
    · apply one 420 (by decide) (.SD .x12 .x0 4088) (by rfl) _ _ pc
      have addr : s.getReg .x12+signExtend12 4088=W 224 := by rw [dest];rfl
      have ok : memoryArgumentsValid s (.SD .x12 .x0 4088)=true := by change accessValid (_+_) 8=true;rw [addr];decide
      simp only [ordinaryStep,ok,↓reduceIte,execInstrBr,addr];rfl
    · change s.pc+4=_;rw [pc];rfl
  · constructor
    · apply one 417 (by decide) (.SD .x12 .x0 24) (by rfl) _ _ pc
      have addr : s.getReg .x12+signExtend12 24=W 184 := by rw [dest];rfl
      have ok : memoryArgumentsValid s (.SD .x12 .x0 24)=true := by change accessValid (_+_) 8=true;rw [addr];decide
      simp only [ordinaryStep,ok,↓reduceIte,execInstrBr,addr];rfl
    · change s.pc+4=_;rw [pc];rfl

set_option maxRecDepth 5000
attribute [local irreducible] Runs Normal.Runs

theorem clearGap (o : Oracle) (s : MachineState) (odd : Bool) (pc : s.pc=pcAt 415) (bit : s.getReg .x28=regBit odd) :
    ∃ t n, n≤4 ∧ Normal.Runs o s t n 0 ∧ Gap s t odd := by
  let a:=Test.parity.after s
  have jump:=test_run .parity s pc
  have beginPC : a.pc=pcAt (if odd then 416 else 419) := by
    rw [show a.pc=_ from after_pc .parity s]
    change pcAt (if s.getReg .x28 == (0 : Word) then 419 else 416)=_
    rw [bit];cases odd <;> rfl
  let b : Part := if odd then .oddDest else .evenDest
  have setup := basic b a (by cases odd <;> exact beginPC) (by cases odd <;> rfl)
  let r:=b.after a
  have rp : r.pc=pcAt (if odd then 417 else 420) := by cases odd <;> exact setup.pc
  have rd : r.getReg .x12=W (sa odd) := by rw [setup.regs];cases odd <;> rfl
  let t:=(r.setMem (W (ga odd)) 0).setPC (r.pc+4)
  obtain ⟨storeRun,tp⟩:=clearAt odd r rp rd
  have steps : Runs s t 3 3 := by
    have widths : b.stop-b.start=1 ∧ b.cycles=1 := by dsimp only [b]; split <;> exact ⟨rfl,rfl⟩
    have setupRun := setup.runs
    rw [widths.1,widths.2] at setupRun
    exact jump.trans (setupRun.trans storeRun)
  have rkeep (k : Reg) (ne : k≠.x12) : t.getReg k=s.getReg k := by
    have z (x : MachineState) (a v : Word) : (x.setMem a v).getReg k=x.getReg k := by cases k <;> rfl
    change ((r.setMem _ _).setPC _).getReg k=_
    rw [MachineState.getReg_setPC,z,setup.keep k (by cases odd <;> cases k <;> first | rfl | contradiction),after_regs]
  have dest : t.getReg .x12=W (sa odd) := rd
  have mem : r.mem=s.mem := setup.mem.trans (after_mem ..)
  have altered : t.mem=(s.setMem (W (ga odd)) 0).mem := by
    change (r.setMem _ _).mem=_;simp only [MachineState.setMem,mem]
  obtain ⟨out,zero⟩:=written s (ga odd) 0 t altered (by cases odd <;> decide) (by cases odd <;> decide)
  cases odd with
  | false=> exact ⟨t,3,by decide,Normal.deterministic o steps,⟨tp,dest,rkeep,out,zero⟩⟩
  | true=>
    let u:=Test.skipEven.after t
    have lastRun:=test_run .skipEven t tp
    have endPC : u.pc=pcAt 421 := by change pcAt (if t.getReg .x0 == t.getReg .x0 then 421 else 419)=_;simp
    exact ⟨u,4,by decide,Normal.deterministic o (steps.trans lastRun),⟨endPC,(after_regs ..).trans dest,
      fun k ne=>(after_regs ..).trans (rkeep k ne),out,zero⟩⟩

end CommitGolfCandidate.Late.Check.Micro
