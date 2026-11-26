import CommitGolf.Artifact
namespace CommitGolfCandidate.S5Machine
open CommitGolf CommitGolf.Riscv

def tileSite (j : Fin 256) (call : Fin 4) : Nat :=
  4124+12*j.val+j.val/16+j.val/42+j.val/128+3*call.val

def gap (n : Nat) := 32*n
def msgDisp (j : Fin 256) (offset : Nat) := j.val%16*256+offset
def rowDisp (j : Fin 256) (offset : Nat) := j.val%42*96+offset
def addiWord (rd base coordinate : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (((coordinate+2048)%4096)*2^20+base*2^15+rd*128+19)

def readWord (j : Fin 256) (call : Fin 4) :=
  match call.val with
  | 0=>addiWord 10 21 (msgDisp j 0)
  | 1=>addiWord 10 21 (msgDisp j 64)
  | 2=>addiWord 10 21 (msgDisp j 160)
  | _=>addiWord 10 22 (rowDisp j 0)

def writeWord (j : Fin 256) (call : Fin 4) :=
  match call.val with
  | 0=>addiWord 12 21 (msgDisp j 64)
  | 1=>addiWord 12 22 (rowDisp j (32*(j.val%2)))
  | 2=>addiWord 12 22 (rowDisp j (32*(j.val%2)+32))
  | _=>addiWord 12 23 (gap (j.val%128))

def commitWord (i : Nat) : BitVec 32 :=
  if h : i<18492 then Artifact.commitCode.get 32 ⟨i,h⟩ else 0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 25000000 in
theorem all_tile_sites : ∀ (j : Fin 256) (c : Fin 4),
    commitWord (tileSite j c)=readWord j c ∧
    commitWord (tileSite j c+1)=writeWord j c ∧ commitWord (tileSite j c+2)=0x73 := by
  decide +kernel

theorem msg_position (t : Nat) (j : Fin 256) :
    65536*t+4096*(j.val/16)+msgDisp j 0=256*(256*t+j.val) := by
  unfold msgDisp;omega
theorem row_position (t : Nat) (j : Fin 256) : 24576*t+4032*(j.val/42)+rowDisp j 0=96*(256*t+j.val) := by
  unfold rowDisp;omega
theorem output_position (t : Nat) (j : Fin 256) :
    8192*t+4096*(j.val/128)+gap (j.val%128)=gap (256*t+j.val) := by
  unfold gap;omega
end CommitGolfCandidate.S5Machine
