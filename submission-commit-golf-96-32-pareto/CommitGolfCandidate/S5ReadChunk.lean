import CommitGolfCandidate.S5ReadTake
import CommitGolfCandidate.S5ReadSelect
namespace CommitGolfCandidate.S5Machine.Reader
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W)
open Check (Flow)
def readKeep (q : Reg) := q∉([.x6,.x7,.x19,.x21,.x22,.x28,.x29,.x30,.x31] : List Reg)
def ReaderKeeps (s t : MachineState) := ∀ q,readKeep q→t.getReg q=s.getReg q
theorem ReaderKeeps.trans {s t u} (a : ReaderKeeps s t) (b : ReaderKeeps t u) : ReaderKeeps s u := fun q h=>(b q h).trans (a q h)
structure Chunk (o : Oracle) (s t : MachineState) (base bytes v bit off left width steps k : Nat) : Prop where
  run : Flow o s t steps 0
  pc : t.pc=pcAt 34
  cursor : Cursor t base bytes v (bit+off+width) k
  pending : (t.getReg .x30).toNat=window v bit (off+width)
  offset : t.getReg .x29=W (off+width)
  rest : t.getReg .x31=W (left-width)
  mem : t.mem=s.mem
  keep : ReaderKeeps s t

attribute [local irreducible] pathEnd
theorem read_chunk (o : Oracle) (s : MachineState) (base bytes v bit k off left : Nat) (pos : 0<left) (kmax : k<8)
    (inside : off+left≤64) (space : bit+off+left≤8*bytes) (room : base+bytes≤MEMORY_BYTES) (pc : s.pc=pcAt 34)
    (c : Cursor s base bytes v (bit+off) k) (used : s.getReg .x29=W off) (count : s.getReg .x31=W left)
    (low : (s.getReg .x30).toNat=window v bit off) :
    ∃ t steps rest,steps≤48 ∧ rest<8 ∧ Chunk o s t base bytes v bit off left (min left 32) steps rest := by
  let width:=min left 32
  let short:=decide (left<32)
  let u:=pathEnd s (Select.code .chunk short)
  obtain ⟨choose,next,w,mem,keep⟩:=select_size o .chunk s left pos (by omega) pc count
  have cu:=c.same mem (keep _ (by decide)) (keep _ (by decide)) (keep _ (by decide)) (keep _ (by decide))
  obtain ⟨z,n,haveBits,nmax,enough,extra,load,ip,cz,zm,stable⟩:=filled o u base bytes v (bit+off) k width
    (Nat.min_le_right ..) kmax (by dsimp [width];omega) room next w cu
  have save (q : Reg) (h : q∉([.x6,.x7,.x19,.x21,.x22] : List Reg)) : z.getReg q=s.getReg q := by
    apply (stable q (by intro mem;apply h;simp_all)).trans
    apply keep;intro eq;subst q;exact h (by decide)
  obtain ⟨t,got⟩:=extract o z base bytes v bit haveBits off width left (by dsimp [width];omega) (Nat.min_le_right ..)
    enough extra (by dsimp [width];omega) (Nat.min_le_left ..) ip cz ((stable _ (by decide)).trans w)
    ((save _ (by decide)).trans used) ((save _ (by decide)).trans count) ((congrArg BitVec.toNat (save _ (by decide))).trans low)
  let m:=if short then 4 else 3
  have hlen : m≤4:=by dsimp [m];split <;> decide
  refine ⟨t,m+n+11,haveBits-width,by omega,by omega,⟨(choose.trans load).trans got.run,got.pc,got.cursor,got.pending,
    got.offset,got.left,got.mem.trans (zm.trans mem),?_⟩⟩
  intro q h
  apply (got.keep q (by cases q <;> simp_all [readKeep])).trans
  apply save;cases q <;> simp_all [readKeep]
end CommitGolfCandidate.S5Machine.Reader
