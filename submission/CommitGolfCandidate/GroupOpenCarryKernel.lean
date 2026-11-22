import CommitGolfCandidate.GroupOpenCarryMemory
namespace TwoPermutationPrototype.GroupedOpening.Carry
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 PackedOpening Wide Shifted30
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192

inductive Temp where | a | b | c deriving DecidableEq
def Temp.reg : Temp → Reg | .a => .x31 | .b => .x29 | .c => .x11
def Free (r : Reg) := r≠.x31 ∧ r≠.x29 ∧ r≠.x11
instance (r : Reg) : Decidable (Free r) := by unfold Free; infer_instance
theorem temp_other (t : Temp) (r : Reg) (f : Free r) : t.reg≠r := by
  rcases f with ⟨a,b,c⟩; cases t <;> first | exact Ne.symm a | exact Ne.symm b | exact Ne.symm c
theorem temp_inj (t u : Temp) (neq : t≠u) : t.reg≠u.reg := by
  cases t <;> cases u <;> simp_all [Temp.reg]

inductive Op where
  | ld (dst : Temp) (index : Nat)
  | shr (dst src : Temp) (shift : BitVec 6)
  | shl (dst src : Temp) (shift : BitVec 6)
  | bor (dst left right : Temp)
  | put (size : Width) (src : Temp)

def ins (base : Reg) (off k : Nat) : Op → Instr
  | .ld t j => .LD t.reg base (BitVec.ofNat 12 (8*j))
  | .shr t u d => .SRLI t.reg u.reg d
  | .shl t u d => .SLLI t.reg u.reg d
  | .bor t u v => .OR t.reg u.reg v.reg
  | .put .half t => .SH .x21 t.reg (BitVec.ofNat 12 (off+k))
  | .put .word t => .SW .x21 t.reg (BitVec.ofNat 12 (off+k))
  | .put .dword t => .SD .x21 t.reg (BitVec.ofNat 12 (off+k))

def amount : Op → Nat | .put z _ => z.n | _ => 0
def rows (base : Reg) (off : Nat) : Nat → List Op → List Instr
  | _, [] => []
  | k, op::ops => ins base off k op :: rows base off (k+amount op) ops
abbrev Values := Temp → Word
def assign (a : Values) (t : Temp) (v : Word) : Values := fun q => if q=t then v else a q
def update (D : Nat → Word) (a : Values) : Op → Values
  | .ld t j => assign a t (D j)
  | .shr t u d => assign a t (a u >>> d.toNat)
  | .shl t u d => assign a t (a u <<< d.toNat)
  | .bor t u v => assign a t (a u ||| a v)
  | .put _ _ => a

def validOp (D : Nat → Word) (r n k : Nat) (v : Values) : Op → Prop
  | .ld _ j => j<4
  | .put z t => k+z.n≤n ∧ (r+k)%z.n=0 ∧ ∀ i : Fin z.n,
      extractByte (v t) i.val=extractByte (D ((k+i.val)/8)) ((k+i.val)%8)
  | _ => True
def Valid (D : Nat → Word) (r n : Nat) : Nat → Values → List Op → Prop
  | k, _, [] => k=n
  | k, v, op::ops => validOp D r n k v op ∧ Valid D r n (k+amount op) (update D v op) ops

def cell (s : MachineState) (S j : Nat) := s.getMem (BitVec.ofNat 64 (S+8*j))
structure Track (s m : MachineState) (S T k : Nat) (v : Values) : Prop where
  temp : ∀ t : Temp, m.getReg t.reg = v t
  fixed : ∀ r, Free r → m.getReg r = s.getReg r
  copy : ByteCopy s m S T k
  below : ∀ q : Word, q.toNat<T-T%8 → m.getMem q=s.getMem q

theorem Track.modified {s m S T k v} (h : Track s m S T k v) (t : Temp) (x pc : Word) :
    Track s ((m.setReg t.reg x).setPC pc) S T k (assign v t x) := by
  have same : ((m.setReg t.reg x).setPC pc).mem=m.mem := mem_setReg' m _ _
  refine ⟨?_,?_,copy_congr_mem same h.copy,fun q lo => (getMem_congr same q).trans (h.below q lo)⟩
  · intro u
    by_cases e : u=t
    · subst u
      simpa [assign] using (MachineState.getReg_setReg_eq (s:=m) (v:=x) (show t.reg≠.x0 by cases t <;> decide))
    · simp [assign,e, MachineState.getReg_setReg_ne m _ _ x (temp_inj t u (Ne.symm e)), h.temp]
  · intro r f
    simp [MachineState.getReg_setReg_ne m _ _ x (temp_other t r f),h.fixed r f]

structure Bounds (s : MachineState) (S T n : Nat) (base : Reg) (off : Nat) : Prop where
  source : s.getReg base=BitVec.ofNat 64 S
  destination : s.getReg .x21+BitVec.ofNat 64 off=BitVec.ofNat 64 T
  baseFree : Free base
  aligned : S%8=0
  distinct : S+32≤T
  room : T+n≤MEMORY_BYTES
  width : n≤32
  imm : off+32≤2048

theorem current_cell {s m S T n base off k v} (cfg : Bounds s S T n base off)
    (h : Track s m S T k v) (j : Nat) (small : j<4) :
    cell m S j=cell s S j := by
  apply h.below
  have := cfg.distinct; have := cfg.aligned; have room:=cfg.room
  unfold MEMORY_BYTES at room
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  omega

theorem source_byte_eq {s m S T n base off k v} (cfg : Bounds s S T n base off)
    (h : Track s m S T k v) (j : Nat) (small : j<32) :
    m.getByte (BitVec.ofNat 64 (S+j))=extractByte (cell s S (j/8)) (j%8) := by
  have sa:=cfg.aligned;have apart:=cfg.distinct;have room:=cfg.room;unfold MEMORY_BYTES at room
  have a:=byte_at m (S+8*(j/8)) (j%8) (by omega) (by omega) (by omega)
  rw [show S+8*(j/8)+j%8=S+j by omega] at a
  exact a.trans (congrArg (fun w => extractByte w (j%8)) (current_cell cfg h (j/8) (by omega)))

theorem stored {s m S T n base off k v} (cfg : Bounds s S T n base off)
    (h : Track s m S T k v) (z : Width) (t : Temp)
    (ok : validOp (cell s S) (T%8) n k v (.put z t)) :
    Track s ((write z m (T+k) (v t)).setPC (m.pc+4)) S T (k+z.n) v := by
  obtain ⟨lim,alg,bytes⟩:=ok
  have room:=cfg.room;have apart:=cfg.distinct;have wid:=cfg.width
  have tf : T+n≤2^64 := by unfold MEMORY_BYTES at room;omega
  have alg' : (T+k)%z.n=0 := by cases z <;> simp [Width.n] at * <;> omega
  have copied:=write_copy z m (S+k) (T+k) (v t) alg' (by omega) (by
    intro i hi
    have e:=bytes ⟨i,hi⟩
    exact e.trans (by simpa only [Nat.add_assoc] using (source_byte_eq cfg h (k+i) (by omega)).symm))
  have c:=copy_extend h.copy copied (by omega) (by omega)
  refine ⟨?_,?_,copy_congr_mem (u:=write z m (T+k) (v t)) rfl c,?_⟩
  · intro u; exact (write_regs z m _ _ u.reg).trans (h.temp u)
  · intro r f; exact (write_regs z m _ _ r).trans (h.fixed r f)
  · intro q lo
    exact (write_below z m (T+k) (v t) q (by have := cfg.room; unfold MEMORY_BYTES at this;omega) (by omega)).trans (h.below q lo)

theorem step {s m S T n base off k v} (cfg : Bounds s S T n base off) (h : Track s m S T k v)
    (op : Op) (ok : validOp (cell s S) (T%8) n k v op) :
    memoryArgumentsValid m (ins base off k op)=true ∧
    Track s (execInstrBr m (ins base off k op)) S T (k+amount op) (update (cell s S) v op) := by
  cases op with
  | ld t j =>
    change j<4 at ok
    have addr : m.getReg base+signExtend12 (BitVec.ofNat 12 (8*j))=BitVec.ofNat 64 (S+8*j) := by
      rw [h.fixed base cfg.baseFree,cfg.source,sign12 _ (by omega),←BitVec.ofNat_add]
    have sa:=cfg.aligned;have apart:=cfg.distinct;have room:=cfg.room
    refine ⟨?_,?_⟩
    · change accessValid _ 8=true
      rw [addr];exact access_ok _ _ (by omega) (by omega)
    · simp only [ins,execInstrBr,addr,amount,Nat.add_zero,update]
      exact (current_cell cfg h j ok) ▸ h.modified t (cell m S j) (m.pc+4)
  | shr t u d =>
    exact ⟨rfl,by simpa only [ins,execInstrBr,amount,Nat.add_zero,update,h.temp] using h.modified t (v u >>> d.toNat) (m.pc+4)⟩
  | shl t u d =>
    exact ⟨rfl,by simpa only [ins,execInstrBr,amount,Nat.add_zero,update,h.temp] using h.modified t (v u <<< d.toNat) (m.pc+4)⟩
  | bor t u w =>
    exact ⟨rfl,by simpa only [ins,execInstrBr,amount,Nat.add_zero,update,h.temp] using h.modified t (v u ||| v w) (m.pc+4)⟩
  | put z t =>
    have ⟨lim,alg,_⟩:=ok
    have width:=cfg.width;have imm:=cfg.imm;have room:=cfg.room
    have positive : 0<z.n := by cases z <;> decide
    have addr : m.getReg .x21+signExtend12 (BitVec.ofNat 12 (off+k))=BitVec.ofNat 64 (T+k) := by
      rw [h.fixed .x21 (by decide),sign12 _ (by omega),BitVec.ofNat_add,←BitVec.add_assoc,cfg.destination,←BitVec.ofNat_add]
    have alg' : (T+k)%z.n=0 := by cases z <;> simp [Width.n] at * <;> omega
    have good:=access_ok (T+k) z.n alg' (by omega)
    have st:=stored cfg h z t ok
    cases z <;> exact ⟨by simpa only [ins,memoryArgumentsValid,memAccess,addr,Width.n] using good,
      by simpa only [ins,execInstrBr,amount,update,addr,h.temp,write] using st⟩

theorem rows_simple (base : Reg) (off k : Nat) (ops : List Op) :
    ∀ i ∈ rows base off k ops, stepKind i=true ∧ ∀ m, (execInstrBr m i).pc=m.pc+4 := by
  induction ops generalizing k with
  | nil => simp [rows]
  | cons op ops ih =>
    intro i hi
    rcases List.mem_cons.mp hi with eq|tail
    · subst i;cases op with
      | put z t => cases z <;> exact ⟨rfl,fun _=>rfl⟩
      | _ => exact ⟨rfl,fun _=>rfl⟩
    · exact ih _ i tail

theorem block {s S T n base off} (cfg : Bounds s S T n base off) (ops : List Op)
    (m k v) (h : Track s m S T k v)
    (ok : Valid (cell s S) (T%8) n k v ops) :
    let xs:=rows base off k ops
    Ready m xs ∧ ∃ u, Track s (execCode m xs) S T n u ∧
      (execCode m xs).pc=m.pc+BitVec.ofNat 64 (4*xs.length) := by
  induction ops generalizing m k v with
  | nil => change k=n at ok;subst n;exact ⟨trivial,v,h,by simp [rows,execCode]⟩
  | cons op ops ih =>
    have ⟨valid,next⟩:=step cfg h op ok.1
    have ⟨ready,u,done,pc⟩:=ih _ _ _ next ok.2
    let i:=ins base off k op
    have nextPC:=(rows_simple base off k (op::ops) i (by simp [rows,i])).2 m
    refine ⟨⟨valid,ready⟩,u,done,?_⟩
    change (execCode (execInstrBr m i) _).pc=_
    have len : 4+4*(rows base off (k+amount op) ops).length=4*((rows base off (k+amount op) ops).length+1) := by omega
    rw [pc,nextPC,BitVec.add_assoc,←show BitVec.ofNat 64 4=(4:Word) from rfl,←BitVec.ofNat_add,len]
    rfl

end TwoPermutationPrototype.GroupedOpening.Carry
