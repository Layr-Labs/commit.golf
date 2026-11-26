import CommitGolfCandidate.ReconstructedHonestCapStages

namespace CommitGolfCandidate.Reconstruction.HonestCapTables
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 HonestCapStages

set_option maxHeartbeats 50000000
set_option maxRecDepth 32768

abbrev w (n : Nat) := BitVec.ofNat 64 n
abbrev sp : Word := 68719476336
abbrev scratch : Nat := 68719474176

def level (d : Nat) : Facts := [(.x0,0),(.x10,w d),(.x11,1),(.x26,2)]

theorem init : checked 1429 [(.x0,0)] [.x0,.x10,.x11,.x26] [(1451,level 9)] 19 = true := by decide +kernel

def first_pair (d : Nat) : Facts := [(.x20,0),(.x21,w (2^d)),(.x22,w (2^(d+1)))]
theorem start (q : Fin 9) : checked 1451 (level (q.val+1)) [.x0,.x10,.x11,.x20,.x21,.x22,.x26]
    [(1470,first_pair (q.val+1))] 14 = true := by
  exact (by decide +kernel : ∀ i : Fin 9, checked 1451 (level (i.val+1))
    [.x0,.x10,.x11,.x20,.x21,.x22,.x26] [(1470,first_pair (i.val+1))] 14 = true) q

/-- The pair index is incremented by two independently of whether either flag was set. -/
theorem pair_advance (k : Fin 512) : checked 1470 [(.x21,w (2*k.val))] [.x21]
    [(1469,[(.x21,w (2*k.val+2))])] 17 = true := by
  exact (by decide +kernel : ∀ i : Fin 512, checked 1470 [(.x21,w (2*i.val))] [.x21]
    [(1469,[(.x21,w (2*i.val+2))])] 17 = true) k

def emitInput (n : Nat) : Facts := [(.x0,0),(.x20,w n),(.x8,sp)]
def emitOutput (n : Nat) : Choice := if n=0 then (1449,[]) else
  (1512,[(.x24,w scratch),(.x25,w (scratch+4*n))])
theorem emit_setup (n : Fin 257) : checked 1483 (emitInput n.val)
    [.x0,.x20,.x8,.x14,.x24,.x25] [emitOutput n.val] 26 = true := by
  exact (by decide +kernel : ∀ i : Fin 257, checked 1483 (emitInput i.val)
    [.x0,.x20,.x8,.x14,.x24,.x25] [emitOutput i.val] 26 = true) n

def addrSlot (j : Nat) := w (scratch+4*j)
theorem emit_advance (j : Fin 256) : checked 1512 [(.x24,addrSlot j.val)] [.x24]
    [(1511,[(.x24,addrSlot (j.val+1))])] 59 = true := by
  exact (by decide +kernel : ∀ i : Fin 256, checked 1512 [(.x24,addrSlot i.val)] [.x24]
    [(1511,[(.x24,addrSlot (i.val+1))])] 59 = true) j

def ungroupedInput (d : Nat) : Facts := [(.x0,0),(.x10,w d)]
theorem ungrouped (d : Fin 7) : checked 1581 (ungroupedInput (d.val+1)) [.x0,.x10,.x12,.x26]
    [(1449,[(.x26,2)])] 16 = true := by
  exact (by decide +kernel : ∀ i : Fin 7, checked 1581 (ungroupedInput (i.val+1)) [.x0,.x10,.x12,.x26]
    [(1449,[(.x26,2)])] 16 = true) d

def groupedInput (d n : Nat) : Facts := [(.x0,0),(.x10,w d),(.x20,w n)]
def groupedOutput (n : Nat) : Facts := [(.x26,2),(.x21,0),(.x24,w n)]
theorem grouped (d : Fin 2) (n : Fin 257) : checked 1581 (groupedInput (d.val+8) n.val)
    [.x0,.x10,.x12,.x20,.x21,.x24,.x26] [(1603,groupedOutput n.val)] 16 = true := by
  exact (by decide +kernel : ∀ i : Fin 2, ∀ j : Fin 257, checked 1581 (groupedInput (i.val+8) j.val)
    [.x0,.x10,.x12,.x20,.x21,.x24,.x26] [(1603,groupedOutput j.val)] 16 = true) d n

/-- Each paid header takes the smaller of four and the remaining sibling count. -/
theorem group_size (n : Fin 257) : checked 1603 [(.x0,0),(.x24,w n.val)] [.x0,.x12,.x24,.x25,.x30]
    [(1610,[(.x30,0-w (min 4 n.val))])] 7 = true := by
  exact (by decide +kernel : ∀ i : Fin 257, checked 1603 [(.x0,0),(.x24,w i.val)] [.x0,.x12,.x24,.x25,.x30]
    [(1610,[(.x30,0-w (min 4 i.val))])] 7 = true) n

theorem take_digit (n : Fin 4) : checked 1610 [(.x30,0-w (n.val+1))] [.x30]
    [(1625,[(.x30,0-w n.val)])] 18 = true := by
  exact (by decide +kernel : ∀ i : Fin 4, checked 1610 [(.x30,0-w (i.val+1))] [.x30]
    [(1625,[(.x30,0-w i.val)])] 18 = true) n

def nextDigit (r : Nat) := if r=0 then 1626 else 1610
theorem digit_guard (n : Fin 4) : checked 1625 [(.x0,0),(.x30,0-w n.val)] [] [(nextDigit n.val,[])] 1 = true := by
  exact (by decide +kernel : ∀ i : Fin 4, checked 1625 [(.x0,0),(.x30,0-w i.val)] [] [(nextDigit i.val,[])] 1 = true) n

theorem flush_index (k : Fin 64) : checked 1626 [(.x21,w (4*k.val))] [.x21]
    [(1602,[(.x21,w (4*(k.val+1)))])] 19 = true := by
  exact (by decide +kernel : ∀ i : Fin 64, checked 1626 [(.x21,w (4*i.val))] [.x21]
    [(1602,[(.x21,w (4*(i.val+1)))])] 19 = true) k

theorem flush_remaining (k : Fin 253) : checked 1626 [(.x24,w (k.val+4))] [.x24]
    [(1602,[(.x24,w k.val)])] 19 = true := by
  exact (by decide +kernel : ∀ i : Fin 253, checked 1626 [(.x24,w (i.val+4))] [.x24]
    [(1602,[(.x24,w i.val)])] 19 = true) k

def below (d : Nat) := if d=0 then 1641 else 1451
theorem next_level (d : Fin 9) : checked 1449 [(.x0,0),(.x10,w (d.val+1))] [.x0,.x10]
    [(below d.val,[(.x10,w d.val)])] 2 = true := by
  exact (by decide +kernel : ∀ i : Fin 9, checked 1449 [(.x0,0),(.x10,w (i.val+1))] [.x0,.x10]
    [(below i.val,[(.x10,w i.val)])] 2 = true) d

end CommitGolfCandidate.Reconstruction.HonestCapTables
