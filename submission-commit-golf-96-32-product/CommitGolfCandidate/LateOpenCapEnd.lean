import CommitGolfCandidate.LateOpenCapFill
import CommitGolfCandidate.LateOpenOverride

namespace CommitGolfCandidate.Late.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def reversePass : Nat → MachineState → MachineState
  | 0,s => s | n+1,s => reversePass n (overrideOne s)

structure ReverseResult (s : MachineState) (xs : List Index) (tree : Levels) (n : Nat) : Prop where
  run : Runs s (reversePass n s) (21*n) (21*n)
  pc : (reversePass n s).pc=pcAt 129
  outside : Outside s (reversePass n s) capBase 4096
  table : Slots (reversePass n s) tree xs

theorem reverse_run (s : MachineState) {xs tree salts} (input : Sources s xs tree salts) (card : xs.length=128)
    (n : Nat) (le : n≤128) (pc : s.pc=pcAt (if n=0 then 129 else 108)) (fr : ReverseFrame s n)
    (table : Slots s tree (xs.drop n)) : ReverseResult s xs tree n := by
  induction n generalizing s with
  | zero => exact ⟨Runs.refl _,pc,fun _ _ _ _ => rfl,table⟩
  | succ n ih =>
    have one := override_run s input card n (by omega) (by simpa only [Nat.succ_ne_zero,if_false] using pc) fr table
    have nextInput := input.after (by rw [card]; decide) capBase 4096 one.outside
      (by decide) (by decide) (by decide)
    have rem := ih (overrideOne s) nextInput (by omega) one.pc one.frame one.slots
    refine ⟨?_,rem.pc,one.outside.chain rem.outside,rem.table⟩
    simpa only [reversePass,Nat.mul_succ,Nat.add_comm 21 (21*n)] using one.run.trans rem.run

private theorem slots_bytes (s : MachineState) (tree : Levels) (xs : List Index) (slots : Slots s tree xs)
    (n j : Nat) (bound : j+n≤128) :
    HasBytes s (slotAddr j) ((List.range' j n).flatMap fun p => bytes (n:=32) (capSlot tree xs p)) := by
  induction n generalizing j with
  | zero => intro k hk;simp at hk
  | succ n ih =>
    rw [List.range'_succ,List.flatMap_cons]
    apply (slots j (by omega)).append
    have next : slotAddr j+(bytes (n:=32) (capSlot tree xs j)).length=slotAddr (j+1) := by simp [slotAddr,bytes];omega
    rw [next];exact ih (j+1) (by omega)

def capBytes (tree : Levels) (xs : List Index) := (List.range 128).flatMap fun p => bytes (n:=32) (capSlot tree xs p)

theorem slots_payload (s : MachineState) (tree : Levels) (xs : List Index) (h : Slots s tree xs) :
    HasBytes s capBase (capBytes tree xs) := by
  simpa only [slotAddr,Nat.mul_zero,Nat.add_zero,capBytes,List.range_eq_range'] using slots_bytes s tree xs h 128 0 (by decide)

def finalCap (s : MachineState) :=
  let a := fillCap 64 (Part.capStart.after s)
  reversePass 128 (Part.reverseStart.after a)

structure CapResult (s : MachineState) (xs : List Index) (tree : Levels) : Prop where
  run : Runs s (finalCap s) 4120 4120
  pc : (finalCap s).pc=pcAt 129
  bytes : Written s (finalCap s) capBase (capBytes tree xs)

theorem cap_run (s : MachineState) {xs tree salts} (src : Sources s xs tree salts) (card : xs.length=128)
    (pc : s.pc=pcAt 62) (dst : s.getReg .x25=W capBase) : CapResult s xs tree := by
  let a := Part.capStart.after s
  let b := fillCap 64 a
  let c := Part.reverseStart.after b
  have ha := no_load .capStart s pc rfl
  have inputA := src.same_mem ha.mem
  have start : PairFrame a 0 := ⟨ha.regs .x23,(ha.keep .x25 rfl).trans dst,ha.regs .x28⟩
  have size : xs.length≤LENGTH := by rw [card];decide
  have fill := fill_run a inputA size 64 0 (by decide) ha.pc start
  have hb : b.pc=pcAt 90 := fill.pc
  have out : Outside s b capBase 4096 := by
    have before : Outside s a capBase 4096 := fun q _ _ _ => congrFun ha.mem (BitVec.ofNat 64 q)
    exact before.chain fill.outside
  have inputB := src.after size capBase 4096 out (by decide) (by decide) (by decide)
  have setup := no_load .reverseStart b hb rfl
  have inputC := inputB.same_mem setup.mem
  have fr : ReverseFrame c 128 := ⟨setup.regs .x18,setup.regs .x19,setup.regs .x24,setup.regs .x28⟩
  have initialSlots : Slots c tree (xs.drop 128) := by
    rw [←card,List.drop_length]
    intro p hp
    have f := fill.slots p (by omega) hp
    change HasBytes c (slotAddr p) (bytes (n:=32) (node tree 17 p))
    intro j hj
    have mem : c.mem=(fillCap 64 a).mem := setup.mem
    simpa only [byteAt,MachineState.getByte,MachineState.getMem,mem] using f j hj
  have rev := reverse_run c inputC card 128 le_rfl setup.pc fr initialSlots
  refine ⟨((ha.runs.trans fill.run).trans setup.runs).trans rev.run,rev.pc,⟨?_,slots_payload _ tree xs rev.table⟩⟩
  have middle : Outside b c capBase 4096 := fun q _ _ _ => congrFun setup.mem _
  have len : (capBytes tree xs).length=4096 := by simp [capBytes,List.length_flatMap,bytes,List.sum_replicate]
  rw [len]
  exact (out.chain middle).chain rev.outside

end CommitGolfCandidate.Late.Open
