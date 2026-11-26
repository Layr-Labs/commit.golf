import CommitGolfCandidate.S5CursorRegs
import CommitGolfCandidate.S5LeafContents
namespace CommitGolfCandidate.S5Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def slotIndex (k : Nat) : Fin 256 := ⟨k%256,Nat.mod_lt _ (by decide)⟩
structure AtLeaf (s : MachineState) (k : Nat) : Prop where
  pc : s.pc=pcAt (if k<LENGTH then tileSite (slotIndex k) 0 else 7224)
  message : s.getReg .x21=BitVec.ofNat 64 (4096+msgPos k)+2048
  rows : s.getReg .x22=BitVec.ofNat 64 (rowBase+rowPos k)+2048
  nodes : s.getReg .x23=BitVec.ofNat 64 (4294975488+nodePos k)+2048
  counter : s.getReg .x20=BitVec.ofNat 64 (65536-k/256)
  strideM : s.getReg .x25=4096
  strideR : s.getReg .x26=4032
  strideEnd : s.getReg .x27=384
  base : s.getReg .x18=4294975488
  root : s.getReg .x9=4294971392
  scratch : s.getReg .x24=7113547776
  selector : s.getReg .x5=0
  len : s.getReg .x11=96
  kind : s.getReg .x13=0

theorem toRegs {s k} (a : AtLeaf s k) : LeafRegs s (k/256) (slotIndex k) := by
  refine ⟨?_,?_,?_,a.selector,a.len,a.kind⟩
  · rw [a.message];apply congrArg (fun n=>BitVec.ofNat 64 n+2048)
    change 4096+(65536*(k/256)+4096*((k%256)/16))=4096+256*(256*(k/256)+16*((k%256)/16));omega
  · rw [a.rows];apply congrArg (fun n=>BitVec.ofNat 64 n+2048)
    change rowBase+(24576*(k/256)+4032*((k%256)/42))=rowBase+96*(256*(k/256)+42*((k%256)/42));omega
  · rw [a.nodes];apply congrArg (fun n=>BitVec.ofNat 64 n+2048)
    let j:=256*(k/256)+128*((k%256)/128)
    change 4294975488+(8192*(k/256)+4096*((k%256)/128))=4294975488+levelOffset 0+(32*j)
    rw [show levelOffset 0=0 by decide];dsimp [j];omega

def afterHashes (H : Compression) (s : MachineState) (k : Nat) :=
  finalLeafState H s (k/256) (slotIndex k)
def afterUpdates (H : Compression) (s : MachineState) (k : Nat) :=
  updatesState (afterHashes H s k) (slotIndex k)
def landed (s : MachineState) (k : Nat) := s.setPC (pcAt (if k+1<LENGTH then 4124 else 7224))
def afterLeaf (H : Compression) (s : MachineState) (k : Nat) :=
  let u:=afterUpdates H s k
  if k%256=255 then landed u k else u
def branchSteps (k : Nat) := if k+1<LENGTH then 2 else 1
def tailCount (k : Nat) := (updates (slotIndex k)).length + (if k%256=255 then branchSteps k else 0)

theorem updated_count {s k} (H : Compression) (a : AtLeaf s k) (inside : k<LENGTH) :
    (afterUpdates H s k).getReg .x20=BitVec.ofNat 64 (65536-(k+1)/256) := by
  have eq:=(update_regs (afterHashes H s k) (slotIndex k)).count
  change (afterUpdates H s k).getReg .x20=_ at eq
  rw [eq,show (afterHashes H s k).getReg .x20=s.getReg .x20 from final_keeps H s (k/256) (slotIndex k) .x20 (by decide) (by decide),a.counter]
  change k<16777216 at inside
  by_cases last : k%256=255
  · rw [if_pos (show (slotIndex k).val=255 from last)]
    exact (BitVec.ofNat_sub_ofNat_of_le (w:=64) (65536-k/256) 1 (by decide) (by omega)).trans
      (congrArg (BitVec.ofNat 64) (by omega))
  · rw [if_neg (show (slotIndex k).val≠255 from last),show (k+1)/256=k/256 by omega]

theorem tail_mem (H : Compression) (s : MachineState) (k : Nat) :
    (afterLeaf H s k).mem=(afterHashes H s k).mem := by
  unfold afterLeaf;split <;> exact (update_regs _ _).mem

theorem landed_run (s : MachineState) (k fuel : Nat) (ip : s.pc=pcAt 7222)
    (zero : s.getReg .x20=0 ↔ ¬k+1<LENGTH) :
    execute commitImage (fuel+branchSteps k) s true=
      (do let r←execute commitImage fuel (landed s k) true;return r.charge (branchSteps k) 0) := by
  have f : fetch commitImage s=some (.base (.BEQ .x20 .x0 8)) := site (p:=.commit) (n:=7222) (by decide) (by rfl) s ip
  by_cases more : k+1<LENGTH
  · let t:=s.setPC (pcAt 7223)
    have nz : s.getReg .x20≠0:=fun e=>(zero.mp e) more
    have turn : ordinaryStep s (.base (.BEQ .x20 .x0 8))=some t := by
      change some (if (s.getReg .x20==s.getReg .x0) then _ else s.setPC (s.pc+4))=_
      rw [show s.getReg .x0=0 from rfl,beq_eq_false_iff_ne.mpr nz,if_neg (by decide : ¬false=true),ip];rfl
    have jump : fetch commitImage t=some (.base (.JAL .x0 2084756)) := site (p:=.commit) (n:=7223) (by decide) (by rfl) t rfl
    have back : ordinaryStep t (.base (.JAL .x0 2084756))=some (landed s k) := by
      change some (s.setPC (pcAt 7223+signExtend21 2084756))=_
      rw [show pcAt 7223+signExtend21 2084756=pcAt 4124 by decide,landed,if_pos more]
    rw [branchSteps,if_pos more,execute_ordinary_step _ _ _ _ _ _ f turn,execute_ordinary_step _ _ _ _ _ _ jump back]
    simp [Execution.charge,instructionCycles,bind_assoc,←Nat.add_assoc]
  · have turn : ordinaryStep s (.base (.BEQ .x20 .x0 8))=some (landed s k) := by
      change some (if (s.getReg .x20==s.getReg .x0) then s.setPC (s.pc+signExtend13 8) else _)=_
      rw [show s.getReg .x0=0 from rfl,zero.mpr more,beq_self_eq_true,if_pos (rfl : true=true),ip,landed,if_neg more];rfl
    rw [branchSteps,if_neg more,execute_ordinary_step _ _ _ _ _ _ f turn];rfl

end CommitGolfCandidate.S5Machine
