import CommitGolfCandidate.ReconstructedCommitWrite
import CommitGolfCandidate.ReconstructedCommitTileEntry
import CommitGolfCandidate.HidingSalts

namespace CommitGolfCandidate.Reconstruction.CommitKey
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64
open TwoPermutationPrototype (window writeWindow writeWord)
open Generator CommitSetup CommitBlocks CommitWindows

local instance discrete {α : Type} : MeasurableSpace α := ⊤

def key (r : BitVec 192) : Key := splitBlocks 64 3 r

def afterDraw (s : MachineState) (r : BitVec 192) := writeBits (seedState s 6) 5637148560 r
def tileStart (s : MachineState) (r : BitVec 192) := CommitTile.before (afterDraw s r) 12

attribute [local irreducible] execute writeBits
theorem draw (s : MachineState) (pc : s.pc = 4096) (fuel : Nat) :
    execute im (7+fuel) s true =
      (do let r ← liftM ($ᵗ BitVec 192 : ProbComp _)
          let e ← execute im fuel (afterDraw s r) true
          return e.charge 10 0) := by
  exact actual_seed_prefix s pc fuel

theorem key_distribution {α : Type} (next : Key → ProbComp α) :
    𝒟[($ᵗ BitVec 192) >>= fun r => next (key r)] = 𝒟[($ᵗ Key) >>= next] :=
  split_blocks_uniform_bind 64 3 (by decide) next

private theorem memory_view (s t : MachineState) (same : s.mem = t.mem) (w : Nat) :
    memoryView s w = memoryView t w := congrFun same _

theorem base (s : MachineState) (r : BitVec 192) :
    (afterDraw s r).getReg .x8 = 5637148528 :=
  (writeBits_register ..).trans (generator_register s)

theorem setup (o : Oracle) (s : MachineState) (pc : s.pc = 4096) (r : BitVec 192) :
    CommitExact.Segment o im 12 (afterDraw s r) (tileStart s r) := by
  have loc : (afterDraw s r).pc = addr 7 := by
    unfold afterDraw writeBits
    change (seedState s 6).pc + 4 = _
    rw [seed_syscall_pc,pc]; rfl
  exact CommitTile.setup o _ loc (base s r)

theorem start_memory (s : MachineState) (r : BitVec 192) (w : Nat) (room : w < 2^33) :
    memoryView (tileStart s r) w =
      writeWord (writeWindow (memoryView s) (generatorBase+4) (key r)) generatorBase (-1) w := by
  rw [tileStart,memory_view _ _ (CommitTile.memory (afterDraw s r) (base s r))]
  change memoryView ((afterDraw s r).setMem (wordAddress generatorBase) (-1)) w = _
  rw [memory_at_store (by decide) (by omega)]
  have val := CommitWrite.words (seedState s 6) 3 (generatorBase+4) w r (by decide) room
  have original : memoryView (seedState s 6) = memoryView s :=
    funext (memory_view _ _ (seed_register_setup_memory s))
  rw [original] at val
  change memoryView (afterDraw s r) w = writeWindow (memoryView s) (generatorBase+4) (key r) w at val
  unfold writeWord
  split
  · rfl
  · exact val

end CommitGolfCandidate.Reconstruction.CommitKey
