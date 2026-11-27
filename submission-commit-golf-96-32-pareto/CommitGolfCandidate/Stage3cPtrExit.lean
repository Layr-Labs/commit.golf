import CommitGolfCandidate.Stage3cTower
import CommitGolfCandidate.MemoryCore
import CommitGolfCandidate.Stage3cHeaderInterpreter
namespace CommitGolfCandidate.Chained.BinaryMachine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option Elab.async false

/-! Root copy and halt for the pointer image.
The trailer occupies words 11529..11542. `ADDI x6, x6, 4000` is the twelve-bit
encoding whose sign extension is −96, so `x18 + 0x60000000 − 96` is the root. -/

def rootSource := 5905588128
def rootDestination := 4294971392

def rootOps : List Instr := [.LUI .x6 393216, .ADDI .x6 .x6 4000, .ADD .x7 .x18 .x6]
def rootPrepared (s : MachineState) := rootOps.foldl execInstrBr s

def copyWord (s : MachineState) (i : Fin 4) :=
  let off := BitVec.ofNat 12 (8 * i.val)
  execInstrBr (execInstrBr s (.LD .x28 .x7 off)) (.SD .x9 .x28 off)

def rootCopy (s : MachineState) := copyWord (copyWord (copyWord (copyWord s 0) 1) 2) 3
def haltState (s : MachineState) := execInstrBr (execInstrBr s (.ADDI .x5 .x0 1)) (.ADDI .x10 .x0 0)
def exited (s : MachineState) := haltState (rootCopy (rootPrepared s))

private theorem root_table : ∀ i : Fin 3,
    decoded (11529 + i.val) = some (.base (rootOps.get ⟨i.val, i.isLt⟩)) := by decide +kernel

theorem root_registers (s : MachineState) (base : s.getReg .x18 = 4294975488)
    (root : s.getReg .x9 = 4294971392) :
    (rootPrepared s).getReg .x7 = BitVec.ofNat 64 rootSource ∧
      (rootPrepared s).getReg .x9 = BitVec.ofNat 64 rootDestination := by
  refine ⟨?_, root⟩
  change s.getReg .x18 + (((393216 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64 + signExtend12 4000) = _
  rw [base]; decide

private theorem copy_sites (i : Fin 4) :
    Site .commit (11532 + 2 * i.val) (.LD .x28 .x7 (BitVec.ofNat 12 (8 * i.val))) ∧
      Site .commit (11532 + 2 * i.val + 1) (.SD .x9 .x28 (BitVec.ofNat 12 (8 * i.val))) := by
  constructor <;> apply decoded_site (by have := i.isLt; omega) <;> fin_cases i <;> rfl

private theorem copy_run (s : MachineState) (i : Fin 4) (fuel : Nat)
    (pc : s.pc = pcAt (11532 + 2 * i.val)) (src : s.getReg .x7 = BitVec.ofNat 64 rootSource)
    (dst : s.getReg .x9 = BitVec.ofNat 64 rootDestination) :
    execute commitImage (fuel + 2) s true =
      (do let out ← execute commitImage fuel (copyWord s i) true; pure (out.charge 2 0)) := by
  let off := BitVec.ofNat 12 (8 * i.val)
  let t := execInstrBr s (.LD .x28 .x7 off)
  have pc' : t.pc = pcAt (11532 + 2 * i.val + 1) := by change s.pc + 4 = _; rw [pc, pc_succ]
  have d' : t.getReg .x9 = BitVec.ofNat 64 rootDestination := dst
  have good : ordinaryStep s (.base (.LD .x28 .x7 off)) = some t := by
    have e : memoryArgumentsValid s (.LD .x28 .x7 off) = true := by
      change accessValid (s.getReg .x7 + signExtend12 off) 8 = true
      rw [src]; fin_cases i <;> decide
    simp only [ordinaryStep, e, ↓reduceIte]; rfl
  have good' : ordinaryStep t (.base (.SD .x9 .x28 off)) = some (copyWord s i) := by
    have e : memoryArgumentsValid t (.SD .x9 .x28 off) = true := by
      change accessValid (t.getReg .x9 + signExtend12 off) 8 = true
      rw [d']; fin_cases i <;> decide
    simp only [ordinaryStep, e, ↓reduceIte]; rfl
  rw [execute_ordinary_step _ _ _ t _ _ ((copy_sites i).1 s pc) good,
    execute_ordinary_step _ _ _ _ _ _ ((copy_sites i).2 t pc') good']
  simp [Execution.charge, instructionCycles, ←Nat.add_assoc]

private theorem copied_pc (s : MachineState) (i : Fin 4) : (copyWord s i).pc = s.pc + 8 := by
  change s.pc + 4 + 4 = _; rw [BitVec.add_assoc]; rfl

private theorem halt_run (s : MachineState) (pc : s.pc = pcAt 11540) (fuel : Nat) :
    execute commitImage (fuel + 3) s true = pure ⟨.success, haltState s, 3, 0⟩ := by
  let t := execInstrBr s (.ADDI .x5 .x0 1)
  have pt : t.pc = pcAt 11541 := by change s.pc + 4 = _; rw [pc]; rfl
  have pu : (haltState s).pc = pcAt 11542 := by change t.pc + 4 = _; rw [pt]; rfl
  have f := decoded_site (pc := 11540) (op := .ADDI .x5 .x0 1) (by decide) (by rfl) s pc
  have f' := decoded_site (pc := 11541) (op := .ADDI .x10 .x0 0) (by decide) (by rfl) t pt
  have f'' := decoded_site (pc := 11542) (op := .ECALL) (by decide) (by rfl) (haltState s) pu
  rw [execute_ordinary_step _ _ _ t _ _ f rfl, execute_ordinary_step _ _ _ (haltState s) _ _ f' rfl,
    execute, f'', show (haltState s).getReg .x5 = 1 by rfl, show (haltState s).getReg .x10 = 0 by rfl]
  rfl

theorem commit_exit (s : MachineState) (pc : s.pc = pcAt 11532)
    (src : s.getReg .x7 = BitVec.ofNat 64 rootSource)
    (dst : s.getReg .x9 = BitVec.ofNat 64 rootDestination) (fuel : Nat) :
    execute commitImage (fuel + 11) s true = pure ⟨.success, haltState (rootCopy s), 11, 0⟩ := by
  let t := copyWord s 0; let u := copyWord t 1; let v := copyWord u 2
  have pt : t.pc = pcAt 11534 := by rw [copied_pc, pc]; rfl
  have pu : u.pc = pcAt 11536 := by rw [copied_pc, pt]; rfl
  have pv : v.pc = pcAt 11538 := by rw [copied_pc, pu]; rfl
  have endPc : (rootCopy s).pc = pcAt 11540 := by change (copyWord v 3).pc = _; rw [copied_pc, pv]; rfl
  rw [copy_run s 0 (fuel + 9) pc src dst, copy_run t 1 (fuel + 7) pt src dst,
    copy_run u 2 (fuel + 5) pu src dst, copy_run v 3 (fuel + 3) pv src dst, halt_run (copyWord v 3) endPc]
  rfl

theorem root_exit (s : MachineState) (pc : s.pc = pcAt 11529) (cm : Common s) (fuel : Nat) :
    execute commitImage (fuel + 14) s true = pure ⟨.success, exited s, 14, 0⟩ := by
  have run := execute_linear .commit true rootOps 11529 s (fuel + 11) pc
    (fun op m => header_straight op (List.all_eq_true.mp (by decide : rootOps.all setupOp) op m))
    (fun i hi => decoded_site (by change i < 3 at hi; omega) (root_table ⟨i, hi⟩))
  have ip : (rootPrepared s).pc = pcAt 11532 := by change s.pc + 4 + 4 + 4 = _; rw [pc]; rfl
  obtain ⟨from_, to_⟩ := root_registers s cm.base cm.root
  rw [show fuel + 14 = (fuel + 11) + rootOps.length by change fuel + 14 = fuel + 11 + 3; omega, run]
  change (do let r ← execute commitImage (fuel + 11) (rootPrepared s) true; pure (r.charge 3 0)) = _
  rw [commit_exit _ ip from_ to_, pure_bind]; rfl

private theorem copy_effect (s : MachineState) (i : Fin 4) (q : Word)
    (src : s.getReg .x7 = BitVec.ofNat 64 rootSource)
    (dst : s.getReg .x9 = BitVec.ofNat 64 rootDestination) :
    (copyWord s i).getMem q =
      if q == BitVec.ofNat 64 (rootDestination + 8 * i.val) then
        s.getMem (BitVec.ofNat 64 (rootSource + 8 * i.val))
      else s.getMem q := by
  change (if q == s.getReg .x9 + signExtend12 (BitVec.ofNat 12 (8 * i.val)) then
    s.getMem (s.getReg .x7 + signExtend12 (BitVec.ofNat 12 (8 * i.val))) else s.getMem q) = _
  rw [src, dst]
  fin_cases i <;> rfl

private theorem halt_get (s : MachineState) (q : Word) : (haltState s).getMem q = s.getMem q := rfl

theorem root_copy_contents (s : MachineState) (src : s.getReg .x7 = BitVec.ofNat 64 rootSource)
    (dst : s.getReg .x9 = BitVec.ofNat 64 rootDestination) :
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
  simp only [hc, hb, ha]
  interval_cases j <;> rfl

theorem root_copy_away (s : MachineState) (src : s.getReg .x7 = BitVec.ofNat 64 rootSource)
    (dst : s.getReg .x9 = BitVec.ofNat 64 rootDestination) (q : Word)
    (above : rootDestination + 32 ≤ q.toNat) : (haltState (rootCopy s)).getMem q = s.getMem q := by
  have one (t : MachineState) (i : Fin 4) (hs : t.getReg .x7 = BitVec.ofNat 64 rootSource)
      (hd : t.getReg .x9 = BitVec.ofNat 64 rootDestination) : (copyWord t i).getMem q = t.getMem q := by
    have hi := i.isLt
    have ne : q ≠ BitVec.ofNat 64 (rootDestination + 8 * i.val) := by
      intro eq
      have n := congrArg BitVec.toNat eq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold rootDestination; omega)] at n
      omega
    rw [copy_effect t i q hs hd, if_neg (fun eq => ne (beq_iff_eq.mp eq))]
  let a := copyWord s 0; let b := copyWord a 1; let c := copyWord b 2
  rw [halt_get]
  exact (one c 3 src dst).trans ((one b 2 src dst).trans ((one a 1 src dst).trans (one s 0 src dst)))

theorem exited_root (s : MachineState) (cm : Common s) :
    readBuffer (exited s) rootDestination 32 = readBuffer s rootSource 32 := by
  obtain ⟨from_, to_⟩ := root_registers s cm.base cm.root
  exact (root_copy_contents _ from_ to_).trans (read_congr_mem (rootPrepared s) s _ _ rfl)

theorem exited_retains (s : MachineState) (cm : Common s) (a : Nat) (low : tdBase ≤ a)
    (small : a + 32 ≤ MEMORY_BYTES) (aligned : a % 8 = 0) :
    readBuffer (exited s) a 32 = readBuffer s a 32 := by
  obtain ⟨src, dst⟩ := root_registers s cm.base cm.root
  apply (read_digest_eq_iff _ _ _ _ aligned aligned).mpr
  intro j hj
  have bound : a + 8 * j < 2 ^ 64 := by change _ ≤ 2 ^ 36 at small; omega
  exact (root_copy_away (rootPrepared s) src dst (BitVec.ofNat 64 (a + 8 * j))
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]; unfold rootDestination tdBase at *; omega)).trans
      (show (rootPrepared s).getMem (BitVec.ofNat 64 (a + 8 * j)) = s.getMem _ from rfl)
end CommitGolfCandidate.Chained.BinaryMachine
