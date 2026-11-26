import CommitGolfCandidate.S4Transfer
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt)
def bytesOf (ws : List Width) := (ws.map Width.size).sum

def copyBlock (sr dr : Reg) (a b : Nat) (ws : List Width) (s : MachineState) : MachineState :=
  match ws with
  | []=>s
  | w::xs=>copyBlock sr dr (a+w.size) (b+w.size) xs (transfer w sr dr (BitVec.ofNat 12 a) (BitVec.ofNat 12 b) s)

def moveCode (sr dr : Reg) (a b : Nat) : List Width → List Instr
  | []=>[]
  | w::xs=>w.ld sr (BitVec.ofNat 12 a)::w.st dr (BitVec.ofNat 12 b)::moveCode sr dr (a+w.size) (b+w.size) xs

def Matches (c : Code) (pc : Nat) (xs : List Instr) :=
  ∀ j (bj : j<xs.length),decodeInstruction (c.word (pc+j))=some (.base xs[j])

def validOffsets (src dst a b : Nat) : List Width→Prop
  | []=>True
  | w::xs=>Safe (src+a) w.size ∧ Safe (dst+b) w.size ∧
    signExtend12 (BitVec.ofNat 12 a)=W a ∧ signExtend12 (BitVec.ofNat 12 b)=W b ∧
    validOffsets src dst (a+w.size) (b+w.size) xs

theorem moveCodeLen (sr dr : Reg) (a b : Nat) (ws : List Width) : (moveCode sr dr a b ws).length=2*ws.length := by
  induction ws generalizing a b with
  | nil=>rfl
  | cons w ws ih=>simp only [moveCode,List.length_cons,ih,Nat.mul_succ] <;> omega

structure AfterCopy (c : Code) (pc : Nat) (s t : MachineState) (src dst len steps : Nat) : Prop where
  run : Runs c s t steps steps
  endPC : t.pc=pcAt (pc+steps)
  regs : ∀ r,Reg.x6≠r → t.getReg r=s.getReg r
  bytes : Moved s t src dst len

theorem copyBlockRun (c : Code) (sr dr : Reg) (src dst a b pc : Nat) (ws : List Width) (s : MachineState)
    (nr : Reg.x6≠sr) (nw : Reg.x6≠dr) (fromPtr : s.getReg sr=W src) (toPtr : s.getReg dr=W dst)
    (start : s.pc=pcAt pc) (room : pc+2*ws.length≤c.count)
    (valid : validOffsets src dst a b ws) (bounded : src+a+bytesOf ws≤MEMORY_BYTES)
    (apart : src+a+bytesOf ws≤dst+b ∨ dst+b+bytesOf ws≤src+a)
    (code : Matches c pc (moveCode sr dr a b ws)) :
    AfterCopy c pc s (copyBlock sr dr a b ws s) (src+a) (dst+b) (bytesOf ws) (2*ws.length) := by
  induction ws generalizing s a b pc with
  | nil=>exact ⟨Runs.refl c s,start,fun _ _=>rfl,Moved.empty s _ _⟩
  | cons w xs ih=>
    obtain ⟨sa,da,ia,ib,tailValid⟩:=valid
    have price : bytesOf (w::xs)=w.size+bytesOf xs:=rfl
    rw [price] at bounded apart
    let t:=transfer w sr dr (BitVec.ofNat 12 a) (BitVec.ofNat 12 b) s
    have addr1 : s.getReg sr+signExtend12 (BitVec.ofNat 12 a)=W (src+a):=by rw [fromPtr,ia];exact (BitVec.ofNat_add ..).symm
    have addr2 : s.getReg dr+signExtend12 (BitVec.ofNat 12 b)=W (dst+b):=by rw [toPtr,ib];exact (BitVec.ofNat_add ..).symm
    have words : pc+2+2*xs.length≤c.count:=by simp only [List.length_cons,Nat.mul_succ] at room;omega
    have first : Runs c s t 2 2:=transferRun c w sr dr _ _ s pc _ _ nw start (by omega)
      (code 0 (by simp [moveCode])) (code 1 (by simp [moveCode])) addr1 addr2 sa da
    have keep (r : Reg) (ne : Reg.x6≠r) : t.getReg r=s.getReg r:=transferRegs w sr dr _ _ s r ne
    have more : Matches c (pc+2) (moveCode sr dr (a+w.size) (b+w.size) xs):=by
      intro j bj
      rw [show pc+2+j=pc+(j+2) by omega]
      exact code (j+2) (by simp only [moveCode,List.length_cons];omega)
    have next:=ih (a+w.size) (b+w.size) (pc+2) t ((keep _ nr).trans fromPtr) ((keep _ nw).trans toPtr)
      (transferPC w sr dr _ _ s pc start) words tailValid (by omega) (by omega) more
    have head : Moved s t (src+a) (dst+b) w.size :=
      (w.moved s (src+a) (dst+b) sa da).congr rfl (transferMem w sr dr _ _ s _ _ nw addr1 addr2)
    have all : Moved s (copyBlock sr dr a b (w::xs) s) (src+a) (dst+b) (w.size+bytesOf xs):=
      head.append (by rw [Nat.add_assoc,Nat.add_assoc];exact next.bytes) (by unfold MEMORY_BYTES at bounded;omega) apart
    have steps : 2*(w::xs).length=2+2*xs.length:=by simp [Nat.mul_succ,Nat.add_comm]
    rw [steps,price]
    exact ⟨first.trans next.run,next.endPC.trans (congrArg pcAt (by omega)),fun r ne=>(next.regs r ne).trans (keep r ne),all⟩
end CommitGolfCandidate.S4.Machine
