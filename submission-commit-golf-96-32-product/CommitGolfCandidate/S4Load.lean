import CommitGolfCandidate.S4LoadPrep
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt pc_succ Digest)

def loadEnd (n : Nat) := Instr.ADDI .x18 .x18 (BitVec.ofNat 12 n)
def loadCode (dst n : Nat) := loadPrefix dst n++moveCode .x18 .x14 0 0 (countBytes n)++[loadEnd n]
def fieldSteps (n : Nat) := 1+clearCount n+2*n+1
def loaded (s : MachineState) (dst n : Nat) :=
  let t:=prepState s dst n
  let u:=copyBlock .x18 .x14 0 0 (countBytes n) t
  execInstrBr u (loadEnd n)

structure Loaded (s t : MachineState) (site src dst n : Nat) : Prop where
  run : Runs .check s t (fieldSteps n) (fieldSteps n)
  pc : t.pc=pcAt (site+fieldSteps n)
  cursor : t.getReg .x18=W (src+n)
  keep : ∀ r,r≠.x6 → r≠.x14 → r≠.x18 → t.getReg r=s.getReg r
  outside : SameOutside s t dst 32
  low : readBuffer t dst n=readBuffer s src n
  digest : n=30 ∨ n=32 → readBuffer t dst 32=(readBuffer s src n).setWidth 256

private theorem prefixLength (dst n : Nat) : (loadPrefix dst n).length=1+clearCount n := by
  unfold loadPrefix clearCount;split <;> rfl
theorem codeLength (dst n : Nat) : (loadCode dst n).length=fieldSteps n := by
  simp only [loadCode,List.length_append,prefixLength,moveCodeLen,countBytes,List.length_replicate,List.length_cons,List.length_nil,fieldSteps]

theorem loadField (s : MachineState) (site src dst n : Nat) (size : n=24 ∨ n=30 ∨ n=32)
    (code : Matches .check site (loadCode dst n)) (room : site+fieldSteps n≤Code.check.count) (pc : s.pc=pcAt site)
    (ptr : s.getReg .x18=W src) (imm : signExtend12 (BitVec.ofNat 12 dst)=W dst)
    (pos : Safe (dst+24) 8) (sb : src+n≤MEMORY_BYTES) (away : dst+32≤src) :
    Loaded s (loaded s dst n) site src dst n := by
  let t:=prepState s dst n
  let u:=copyBlock .x18 .x14 0 0 (countBytes n) t
  let head:=1+clearCount n
  have nle : n≤32:=by omega
  have db : dst+32≤MEMORY_BYTES:=pos.1
  have room' : site+head+2*n+1≤Code.check.count:=by simpa only [head,fieldSteps,Nat.add_assoc] using room
  obtain ⟨first,pt,dest,keepA,outA,zeros⟩:=loadPrep s site dst n pc (by omega) imm pos (Matches.left (Matches.left code))
  have copyEnc : Matches .check (site+head) (moveCode .x18 .x14 0 0 (countBytes n)):=by
    simpa only [prefixLength,head] using (Matches.right (Matches.left code))
  have incEnc : decodeInstruction (Code.check.word (site+head+2*n))=some (.base (loadEnd n)):=by
    have endC :=Matches.head (Matches.right code)
    simpa only [List.length_append,prefixLength,moveCodeLen,countBytes,List.length_replicate,head,Nat.add_assoc] using endC
  have copy :=copyBlockRun .check .x18 .x14 src dst 0 0 (site+head) (countBytes n) t (by decide) (by decide)
    ((keepA _ (by decide)).trans ptr) dest pt (by simp only [countBytes,List.length_replicate];omega)
    (validBytes src dst 0 n (by omega) (by omega) (by omega)) (by rw [countSize,Nat.add_zero];exact sb)
    (Or.inr (by rw [countSize,Nat.add_zero,Nat.add_zero];omega)) copyEnc
  have atEnd : u.pc=pcAt (site+head+2*n):=by have h:=copy.endPC;change u.pc=pcAt (site+head+2*(countBytes n).length) at h;simpa only [countBytes,List.length_replicate] using h
  have inc:=stepAdd .check u _ .x18 .x18 (BitVec.ofNat 12 n) (by omega) atEnd incEnc
  have moved : Moved t u src dst n:=by
    have h:=copy.bytes
    simp only [Nat.add_zero,countSize] at h
    exact h
  have prev : readBuffer t src n=readBuffer s src n:=outA.read (sb.trans (by decide)) (Or.inr away)
  have lastMem : (loaded s dst n).mem=u.mem:=rfl
  have totalSteps : head+2*(countBytes n).length+1=fieldSteps n:=by simp [head,countBytes,fieldSteps]
  have incNat : signExtend12 (BitVec.ofNat 12 n)=W n:=by rcases size with rfl|rfl|rfl <;> rfl
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · rw [←totalSteps];exact (first.trans copy.run).trans inc
  · apply (addPC .x18 .x18 (BitVec.ofNat 12 n) atEnd).trans;exact congrArg pcAt (by dsimp [head,fieldSteps];omega)
  · change u.getReg .x18+signExtend12 _=_
    rw [show u.getReg .x18=t.getReg .x18 from copy.regs _ (by decide),keepA _ (by decide),ptr,incNat];exact (BitVec.ofNat_add ..).symm
  · intro r a b c;exact (keepAdd u .x18 .x18 r _ (Ne.symm c)).trans ((copy.regs r (Ne.symm a)).trans (keepA r (Ne.symm b)))
  · have all : SameOutside s u dst 32:=outA.combined moved.frame (by omega)
    intro q b sep;simpa only [byte,MachineState.getByte,MachineState.getMem,lastMem] using all q b sep
  · exact (read_buffer_memory_congr _ _ lastMem _ _).trans ((moved.read (by have:=pos.1;unfold MEMORY_BYTES at this;omega)).trans prev)
  · intro nw
    have high (j : Nat) (lo : n≤j) (hi : j<32) : byte t (dst+j)=0:=by
      rcases nw with h|h
      · exact zeros h j (by omega) hi
      · omega
    exact (read_buffer_memory_congr _ _ lastMem _ _).trans ((readPadded nle (db.trans (by decide)) moved high).trans (congrArg (BitVec.setWidth 256) prev))
end CommitGolfCandidate.S4.Machine
