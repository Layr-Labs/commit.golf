import CommitGolfCandidate.LatePacked
import CommitGolfCandidate.LateLinear
import CommitGolfCandidate.MemoryCore

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def rootSource := 5368714336
def rootDestination := 4294971392

def copyWord (s : MachineState) (i : Fin 4) :=
  let off := BitVec.ofNat 12 (8*i.val)
  execInstrBr (execInstrBr s (.LD .x6 .x12 off)) (.SD .x26 .x6 off)

private theorem site (i : Fin 4) :
    AtWord (3251+2*i.val) (.LD .x6 .x12 (BitVec.ofNat 12 (8*i.val))) ∧
    AtWord (3251+2*i.val+1) (.SD .x26 .x6 (BitVec.ofNat 12 (8*i.val))) := by
  constructor <;> apply decoded_word _ (by have := i.isLt; omega) _ <;> fin_cases i <;> rfl

private theorem copy_run (s : MachineState) (i : Fin 4) (fuel : Nat)
    (pc : s.pc = pcAt (3251+2*i.val)) (src : s.getReg .x12 = BitVec.ofNat 64 rootSource)
    (dst : s.getReg .x26 = BitVec.ofNat 64 rootDestination) :
    execute commitImage (fuel+2) s true =
      (do let out ← execute commitImage fuel (copyWord s i) true; pure (out.charge 2 0)) := by
  let off := BitVec.ofNat 12 (8*i.val)
  let t := execInstrBr s (.LD .x6 .x12 off)
  have pc' : t.pc = pcAt (3251+2*i.val+1) := by change s.pc+4 = _; rw [pc,pc_succ]
  have d' : t.getReg .x26 = BitVec.ofNat 64 rootDestination := dst
  have good : ordinaryStep s (.base (.LD .x6 .x12 off)) = some t := by
    have e : memoryArgumentsValid s (.LD .x6 .x12 off) = true := by
      change accessValid (s.getReg .x12+signExtend12 off) 8 = true
      rw [src]; fin_cases i <;> decide
    simp only [ordinaryStep,e,↓reduceIte]; rfl
  have good' : ordinaryStep t (.base (.SD .x26 .x6 off)) = some (copyWord s i) := by
    have e : memoryArgumentsValid t (.SD .x26 .x6 off) = true := by
      change accessValid (t.getReg .x26+signExtend12 off) 8 = true
      rw [d']; fin_cases i <;> decide
    simp only [ordinaryStep,e,↓reduceIte]; rfl
  rw [execute_ordinary_step _ _ _ t _ _ ((site i).1 s pc) good,
    execute_ordinary_step _ _ _ _ _ _ ((site i).2 t pc') good']
  simp [Execution.charge,instructionCycles,←Nat.add_assoc]

private theorem copied_pc (s : MachineState) (i : Fin 4) : (copyWord s i).pc=s.pc+8 := by
  change s.pc+4+4=_;rw [BitVec.add_assoc];rfl

def rootCopy (s : MachineState) := copyWord (copyWord (copyWord (copyWord s 0) 1) 2) 3
def haltState (s : MachineState) := execInstrBr (execInstrBr s (.ADDI .x5 .x0 1)) (.ADDI .x10 .x0 0)

private theorem halt_run (s : MachineState) (pc : s.pc=pcAt 3259) (fuel : Nat) :
    execute commitImage (fuel+3) s true = pure ⟨.success,haltState s,3,0⟩ := by
  let t := execInstrBr s (.ADDI .x5 .x0 1)
  have pt : t.pc=pcAt 3260 := by change s.pc+4=_;rw [pc];rfl
  have pu : (haltState s).pc=pcAt 3261 := by change t.pc+4=_;rw [pt];rfl
  have f := decoded_word 3259 (by decide) (.ADDI .x5 .x0 1) (by rfl) s pc
  have f' := decoded_word 3260 (by decide) (.ADDI .x10 .x0 0) (by rfl) t pt
  have f'' := decoded_word 3261 (by decide) .ECALL (by rfl) (haltState s) pu
  rw [execute_ordinary_step _ _ _ t _ _ f rfl, execute_ordinary_step _ _ _ (haltState s) _ _ f' rfl,
    execute,f'',show (haltState s).getReg .x5=1 by rfl,show (haltState s).getReg .x10=0 by rfl]
  rfl

theorem commit_exit (s : MachineState) (pc : s.pc=pcAt 3251)
    (src : s.getReg .x12 = BitVec.ofNat 64 rootSource) (dst : s.getReg .x26 = BitVec.ofNat 64 rootDestination)
    (fuel : Nat) : execute commitImage (fuel+11) s true = pure ⟨.success,haltState (rootCopy s),11,0⟩ := by
  let t := copyWord s 0; let u := copyWord t 1; let v := copyWord u 2
  have pt : t.pc=pcAt 3253 := by rw [copied_pc,pc];rfl
  have pu : u.pc=pcAt 3255 := by rw [copied_pc,pt];rfl
  have pv : v.pc=pcAt 3257 := by rw [copied_pc,pu];rfl
  have endPc : (rootCopy s).pc=pcAt 3259 := by change (copyWord v 3).pc = _; rw [copied_pc,pv];rfl
  rw [copy_run s 0 (fuel+9) pc src dst, copy_run t 1 (fuel+7) pt src dst,
    copy_run u 2 (fuel+5) pu src dst,copy_run v 3 (fuel+3) pv src dst,halt_run (copyWord v 3) endPc]
  rfl

private theorem copy_effect (s : MachineState) (i : Fin 4) (q : Word)
    (src : s.getReg .x12 = BitVec.ofNat 64 rootSource) (dst : s.getReg .x26 = BitVec.ofNat 64 rootDestination) :
    (copyWord s i).getMem q =
      if q == BitVec.ofNat 64 (rootDestination+8*i.val) then s.getMem (BitVec.ofNat 64 (rootSource+8*i.val))
      else s.getMem q := by
  change (if q == s.getReg .x26 + signExtend12 (BitVec.ofNat 12 (8*i.val)) then
    s.getMem (s.getReg .x12 + signExtend12 (BitVec.ofNat 12 (8*i.val))) else s.getMem q) = _
  rw [src,dst]
  fin_cases i <;> rfl

private theorem halt_get (s : MachineState) (q : Word) : (haltState s).getMem q = s.getMem q := rfl

theorem root_copy_contents (s : MachineState) (src : s.getReg .x12 = BitVec.ofNat 64 rootSource)
    (dst : s.getReg .x26 = BitVec.ofNat 64 rootDestination) :
    readBuffer (haltState (rootCopy s)) rootDestination 32 = readBuffer s rootSource 32 := by
  let a := copyWord s 0
  let b := copyWord a 1
  let c := copyWord b 2
  let d := copyWord c 3
  have ha (q : Word) : a.getMem q = _ := copy_effect s 0 q src dst
  have hb (q : Word) : b.getMem q = _ := copy_effect a 1 q src dst
  have hc (q : Word) : c.getMem q = _ := copy_effect b 2 q src dst
  have hd (q : Word) : d.getMem q = _ := copy_effect c 3 q src dst
  apply (read_digest_eq_iff _ _ _ _ (by decide) (by decide)).mpr
  intro j hj
  rw [halt_get]
  change d.getMem _ = _
  rw [hd]
  simp only [hc,hb,ha]
  interval_cases j <;> rfl

theorem root_copy_away (s : MachineState) (src : s.getReg .x12 = BitVec.ofNat 64 rootSource)
    (dst : s.getReg .x26 = BitVec.ofNat 64 rootDestination) (q : Word)
    (above : rootDestination+32 ≤ q.toNat) : (haltState (rootCopy s)).getMem q = s.getMem q := by
  have one (t : MachineState) (i : Fin 4) (hs : t.getReg .x12 = BitVec.ofNat 64 rootSource)
      (hd : t.getReg .x26 = BitVec.ofNat 64 rootDestination) : (copyWord t i).getMem q = t.getMem q := by
    have hi := i.isLt
    have ne : q ≠ BitVec.ofNat 64 (rootDestination+8*i.val) := by
      intro eq
      have n := congrArg BitVec.toNat eq
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by unfold rootDestination; omega)] at n
      omega
    rw [copy_effect t i q hs hd,if_neg (fun eq => ne (beq_iff_eq.mp eq))]
  let a := copyWord s 0; let b := copyWord a 1; let c := copyWord b 2
  rw [halt_get]
  exact (one c 3 src dst).trans ((one b 2 src dst).trans ((one a 1 src dst).trans (one s 0 src dst)))

end CommitGolfCandidate.Late
