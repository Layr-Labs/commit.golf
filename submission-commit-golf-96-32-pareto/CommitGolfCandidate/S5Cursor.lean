import CommitGolfCandidate.S5LeafSites
namespace CommitGolfCandidate.S5Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 16000

def updates (i : Fin 256) : List Instr :=
  (if i.val%16=15 then [.ADD .x21 .x21 .x25] else [])++
  (if i.val%42=41 then [.ADD .x22 .x22 .x26] else if i.val=255 then [.ADD .x22 .x22 .x27] else [])++
  (if i.val%128=127 then [.ADD .x23 .x23 .x25] else [])++
  (if i.val=255 then [.ADDI .x20 .x20 4095] else [])
def updateStart (i : Fin 256) := tileSite i 0+12

private theorem table_bound (i : Fin 256) (j : Fin 4) : updateStart i+j.val<words .commit := by
  change tileSite i 0+12+j.val<18492;have :=i.isLt;have :=j.isLt;unfold tileSite;omega

set_option maxHeartbeats 12000000 in
private theorem update_table : ∀ i : Fin 256,∀ j : Fin 4,j.val<(updates i).length →
    decodeInstruction (atWord .commit ⟨updateStart i+j.val,table_bound i j⟩)=
      some (.base ((updates i)[j.val]?.getD .EBREAK)) := by decide +kernel

theorem updates_run (i : Fin 256) (s : MachineState) (pc : s.pc=pcAt (updateStart i)) (fuel : Nat) :
    execute commitImage (fuel+(updates i).length) s true=
      (do let r←execute commitImage fuel ((updates i).foldl execInstrBr s) true
          return r.charge (updates i).length 0) := by
  apply execute_linear .commit true (updates i) _ _ _ pc
  · intro op member
    have choices : op=.ADD .x21 .x21 .x25 ∨ op=.ADD .x22 .x22 .x26 ∨ op=.ADD .x22 .x22 .x27 ∨
        op=.ADD .x23 .x23 .x25 ∨ op=.ADDI .x23 .x23 192 ∨ op=.ADDI .x20 .x20 4095 := by
      unfold updates at member;split_ifs at member <;> simp_all <;> tauto
    rcases choices with rfl|rfl|rfl|rfl|rfl|rfl <;> intro s <;> exact ⟨rfl,rfl,rfl⟩
  · intro j inside
    have cap := (by decide +kernel : ∀ i : Fin 256,(updates i).length≤4) i
    let k : Fin 4 := ⟨j,by omega⟩
    apply site (table_bound i k)
    have eq:=update_table i k inside
    simpa only [k,List.getElem?_eq_getElem inside,Option.getD_some] using eq

theorem updates_next : ∀ i : Fin 255,
    updateStart ⟨i.val,by omega⟩+(updates ⟨i.val,by omega⟩).length=tileSite ⟨i.val+1,by omega⟩ 0 := by decide +kernel

theorem last_branch_pc : updateStart 255+(updates 255).length=7222 := by decide

def msgPos (k : Nat) := 65536*(k/256)+4096*((k%256)/16)
def rowPos (k : Nat) := 24576*(k/256)+4032*((k%256)/42)
def nodePos (k : Nat) := 8192*(k/256)+4096*((k%256)/128)

def msgInc (j : Nat) := if j%16=15 then 4096 else 0
def rowInc (j : Nat) := if j%42=41 then 4032 else if j=255 then 384 else 0
def nodeInc (j : Nat) := if j%128=127 then 4096 else 0

theorem cursor_step (k : Nat) :
    msgPos (k+1)=msgPos k+msgInc (k%256) ∧ rowPos (k+1)=rowPos k+rowInc (k%256) ∧
    nodePos (k+1)=nodePos k+nodeInc (k%256) := by
  by_cases last : k%256=255
  · simp only [msgPos,rowPos,nodePos,last,show (k+1)%256=0 by omega,show (k+1)/256=k/256+1 by omega]
    simp [msgInc,rowInc,nodeInc,Nat.mul_add] <;> omega
  · have small : k%256<255 := by omega
    let i : Fin 255 := ⟨k%256,small⟩
    have step : ∀ j : Fin 255,
        4096*((j.val+1)/16)=4096*(j.val/16)+msgInc j.val ∧
        4032*((j.val+1)/42)=4032*(j.val/42)+rowInc j.val ∧
        4096*((j.val+1)/128)=4096*(j.val/128)+nodeInc j.val := by decide +kernel
    have h := step i
    dsimp only [i] at h
    unfold msgPos rowPos nodePos
    rw [show (k+1)%256=k%256+1 by omega,show (k+1)/256=k/256 by omega,h.1,h.2.1,h.2.2]
    simp only [Nat.add_assoc,true_and]
end CommitGolfCandidate.S5Machine
