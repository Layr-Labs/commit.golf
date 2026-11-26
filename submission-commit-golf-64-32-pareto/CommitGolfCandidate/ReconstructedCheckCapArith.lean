import CommitGolfCandidate.ReconstructedCheckMemoryOps

namespace CommitGolfCandidate.Reconstruction.CheckCapArith
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningOps CheckRecorded CommitBlocks
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
attribute [local irreducible] execute ArtifactEncoding.decode

inductive E where
  | op (e : Expr)
  | addiw (a : Reg) (i : BitVec 12)
  | srliw (a : Reg) (i : BitVec 5)
  | sllw (a b : Reg)

def E.ins (rd : Reg) : E → Instruction
  | .op e => OpeningStraight.actualForm (e.instr rd)
  | .addiw a i => .base (.ADDIW rd a i)
  | .srliw a i => .base (.SRLIW rd a i)
  | .sllw a b => .word .sll rd a b

def E.value (r : Reg→Word) : E→Word
  | .op e => e.eval r
  | .addiw a i => ((r a).truncate 32+(signExtend12 i).truncate 32).signExtend 64
  | .srliw a i => (((r a).truncate 32) >>> i.toNat).signExtend 64
  | .sllw a b => (wordResult .sll ((r a).truncate 32) ((r b).truncate 32)).signExtend 64

abbrev Line := Reg × E
def point (s : MachineState) (line : Line) := (s.setReg line.1 (line.2.value s.getReg)).setPC (s.pc+4)
def effect (s : MachineState) : List Line → MachineState
  | []=>s
  | x::xs=>effect (point s x) xs
def listed (pc : Nat) : List Line → Bool
  | []=>true
  | (r,e)::rest=>CheckMemoryOps.word pc (e.ins r) && listed (pc+1) rest
def update (old : Reg→Word) (line : Line) (r : Reg) :=
  if r=line.1 ∧ r≠.x0 then line.2.value old else old r
def regs (old : Reg→Word) : List Line → Reg→Word
  | []=>old
  | op::xs => regs (update old op) xs

private theorem plain_step (s : MachineState) (rd : Reg) (e : E) :
    ordinaryStep s (e.ins rd)=some (point s (rd,e)) := by
  cases e with
  | op e=>cases e <;> rfl
  | addiw|srliw|sllw=>rfl

theorem positive (o : Oracle) (s : MachineState) (pc : Nat) (ops : List Line)
    (pos : s.pc=addr pc) (table : listed pc ops=true) :
    Segment o ops.length s (effect s ops) [] := by
  induction ops generalizing s pc with
  | nil=>exact CheckRecorded.empty _ _
  | cons x rest ih=>
    obtain ⟨rd,e⟩:=x
    simp only [listed,Bool.and_eq_true] at table
    have one:=plain o s _ _ (CheckMemoryOps.parsed table.1 s pos) (plain_step s rd e)
    have next : (point s (rd,e)).pc=addr (pc+1) := by change s.pc+4=_;rw [pos,addr_next]
    simpa only [effect,List.length_cons,Nat.add_comm 1,List.nil_append] using
      compose one (ih _ _ next table.2)

theorem location (s : MachineState) (pc : Nat) (ops : List Line) (pos : s.pc=addr pc) :
    (effect s ops).pc=addr (pc+ops.length) := by
  induction ops generalizing s pc with
  | nil=>simpa only [effect,List.length_nil,Nat.add_zero] using pos
  | cons op xs ih=>
    have next : (point s op).pc=addr (pc+1) := by change s.pc+4=_;rw [pos,addr_next]
    simpa only [effect,List.length_cons,show pc+(xs.length+1)=pc+1+xs.length by omega] using ih _ _ next

theorem memory (s : MachineState) (ops : List Line) : (effect s ops).mem=s.mem := by
  induction ops generalizing s with
  | nil=>rfl
  | cons op xs ih=>rw [effect,ih];rcases op with ⟨r,e⟩;cases r <;> rfl

theorem register (s : MachineState) (ops : List Line) (r : Reg) :
    (effect s ops).getReg r=regs s.getReg ops r := by
  induction ops generalizing s with
  | nil=>rfl
  | cons op xs ih=>
    rw [effect,ih,regs]
    have reg : (point s op).getReg=update s.getReg op := by
      funext t
      simp only [point,MachineState.getReg_setPC,TwoPermutationPrototype.Opening.getReg_setReg,update]
      split_ifs <;> simp_all
    rw [reg]

theorem outside (s : MachineState) (ops : List Line) (r : Reg) (fresh : r∉ops.map Prod.fst) :
    (effect s ops).getReg r=s.getReg r := by
  induction ops generalizing s with
  | nil=>rfl
  | cons op ops ih=>
    simp only [List.map_cons,List.mem_cons,not_or] at fresh
    rw [effect,ih _ fresh.2]
    simp only [point,MachineState.getReg_setPC,TwoPermutationPrototype.Opening.getReg_setReg]
    split_ifs <;> simp_all

end CommitGolfCandidate.Reconstruction.CheckCapArith
