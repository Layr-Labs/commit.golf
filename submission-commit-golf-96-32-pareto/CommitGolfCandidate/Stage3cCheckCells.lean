import CommitGolfCandidate.Stage3cCheckLeafData
import CommitGolfCandidate.Stage3cCheckNode
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (Digest)
open Open (W Outside)
def rowCell (k : Nat):=rowBuf+32*k
def CellData (s : MachineState) (values : Nat→Digest) := ∀ k<3,readBuffer s (rowCell k) 32=values k
def setCell (v : Nat→Digest) (k : Nat) (value : Digest) := fun j=>if j=k then value else v j
def cell0 (j h : Nat) := j%Geo.radix h
def cellPeer (j h k : Nat) := (cell0 j h+k+1)%Geo.radix h
def pickedCells (h j : Nat) (val : Digest) (p : Pw.Peers) :=
  let first:=setCell (fun _=>0) (cell0 j h) val
  setCell first (cellPeer j h 0) p.1

theorem CellData.same {s t values} (c : CellData s values) (mem : t.mem=s.mem) : CellData t values :=
  fun k h=>(read_buffer_memory_congr t s mem _ _).trans (c k h)
theorem put_cell {s t values} (c : CellData s values) (k : Nat) (hk : k<3) (v : Digest)
    (read : readBuffer t (rowCell k) 32=v) (frame : Outside s t (rowCell k) 32) : CellData t (setCell values k v) := by
  intro j small
  by_cases eq : j=k
  · subst j;rw [setCell,if_pos rfl];exact read
  · rw [setCell,if_neg eq];apply (Open.outside_read frame (by dsimp [rowCell,rowBuf];omega) (by decide) _ 32
      (by dsimp [rowCell,rowBuf,MEMORY_BYTES];omega) (by dsimp [rowCell];omega)).trans (c j small)

theorem blank_cells (s : MachineState) (zero : ∀ i<12,Open.wordAt s (rowBuf+8*i)=0) : CellData s (fun _=>0) := by
  intro k hk
  let t:=writeBits s (W (rowCell k)) (0#256)
  have room : rowCell k%8=0:=by dsimp [rowCell,rowBuf];omega
  have eq:=read_digest_congr s t (rowCell k) room (fun j bj=>by
    have w:=output_word s (rowCell k) j 0 room bj
    have z:=zero (4*k+j) (by omega)
    have addr : rowBuf+8*(4*k+j)=rowCell k+8*j:=by dsimp [rowCell];omega
    rw [addr] at z
    change Open.wordAt s (rowCell k+8*j)=Open.wordAt t (rowCell k+8*j)
    apply z.trans;apply Eq.trans _ w.symm;simp [BitVec.extractLsb'])
  exact eq.trans (store_read s (rowCell k) 0)

theorem cells_row (s : MachineState) (values : Nat→Digest) (c : CellData s values) :
    readBuffer s rowBuf 96=values 2++values 1++values 0 := by
  have high:=read_join s (rowBuf+32) 32 32
  have total:=read_join s rowBuf 32 64
  change readBuffer s (rowCell 2) 32++readBuffer s (rowCell 1) 32=(readBuffer s (rowBuf+32) 64).extractLsb' 0 512 at high
  change readBuffer s (rowBuf+32) 64++readBuffer s (rowCell 0) 32=(readBuffer s rowBuf 96).extractLsb' 0 768 at total
  rw [BitVec.extractLsb'_eq_self,c 1 (by decide),c 2 (by decide)] at high
  rw [BitVec.extractLsb'_eq_self,c 0 (by decide),←high] at total;exact total.symm

private theorem ordering (h j : Nat) (v : Digest) (p : Pw.Peers) :
    let g:=pickedCells h j v p
    g 2++g 1++g 0=Pw.payload (Pw.lane h j) v p ∧ g 2=0 := by
  have cases2 : j%2=0 ∨ j%2=1:=by omega
  rcases cases2 with a|a <;> simp [pickedCells,cell0,cellPeer,Geo.radix,setCell,Pw.lane,Pw.payload, Late.parentBlock,a]

theorem assembled_row (s : MachineState) (h j : Nat) (v : Digest) (p : Pw.Peers) (data : CellData s (pickedCells h j v p)) :
    let g:=pickedCells h j v p
    readBuffer s rowBuf 96=Pw.Auth.row h (g 0) (g 1) (g 2) ∧ Pw.Auth.row h (g 0) (g 1) (g 2)=Pw.payload (Pw.lane h j) v p := by
  let g:=pickedCells h j v p
  obtain ⟨order,missing⟩:=ordering h j v p
  have repr : Pw.Auth.row h (g 0) (g 1) (g 2)=g 2++g 1++g 0 :=by
    unfold Pw.Auth.row;rw [show g 2=0 from missing]
  exact ⟨(cells_row s g data).trans repr.symm,repr.trans order⟩
end CommitGolfCandidate.Chained.BinaryMachine.Check
