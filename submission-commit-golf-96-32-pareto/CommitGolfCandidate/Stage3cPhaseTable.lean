import CommitGolfCandidate.Stage3cCode
import CommitGolfCandidate.Stage3cCachedTree
namespace CommitGolfCandidate.Chained.BinaryMachine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option Elab.async false
def passHeader (h : Height) : Nat := ([5678, 6069, 6588, 7107, 7626, 8145, 8665, 9184, 9703, 9751, 9810, 9881, 9965, 10072, 10203, 10334, 10464, 10983, 11244, 11378, 11448, 11486, 11508, 11522] : List Nat)[h.val]?.getD 0
def mainPC (h : Height) : Nat := ([5683, 6074, 6593, 7112, 7631, 8151, 8670, 9189, 9723, 9770, 9829, 9901, 9984, 10091, 10222, 10352, 10469, 10988, 11250, 11384, 11454, 11492, 11514, 11528] : List Nat)[h.val]?.getD 0
def passEnd (h : Height) : Nat := ([6069, 6588, 7107, 7626, 8145, 8665, 9184, 9703, 9751, 9810, 9881, 9965, 10072, 10203, 10334, 10464, 10983, 11244, 11378, 11448, 11486, 11508, 11522, 11529] : List Nat)[h.val]?.getD 0
def passSteps (h : Height) : Nat := ([25296901, 16842757, 8421381, 4210693, 2105349, 1052678, 526341, 263173, 458772, 327699, 213011, 131092, 90131, 57363, 28691, 14354, 519, 261, 134, 70, 38, 22, 14, 7] : List Nat)[h.val]?.getD 0
def passCycles (h : Height) : Nat := ([84017157, 46202885, 23101445, 11550725, 5775365, 2887686, 1443845, 721925, 917524, 786451, 557075, 360468, 262163, 172051, 86035, 43026, 1415, 709, 358, 182, 94, 50, 28, 14] : List Nat)[h.val]?.getD 0
def tailPC (h : Height) : Nat := ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10988, 11250, 11384, 11454, 11492, 11514, 11528] : List Nat)[h.val]?.getD 0
def mainExit (h : Height) : Nat := passEnd h

def count (h : Height) :=levelCount (h.val+1)
def chained (h : Height) := 8≤h.val ∧ h.val<16
instance (h : Height) : Decidable (chained h) := inferInstanceAs (Decidable (8≤h.val ∧ h.val<16))
/-- Unchained parents run in groups of 128. The chain still runs in pairs. -/
def tileSize (h : Height) := if chained h then 2 else if 128≤count h then 128 else 0
def tiles (h : Height) :=count h/tileSize h
def remainder (h : Height) :=count h%tileSize h
def mask240 (h : Height) := decide (wireWidth h=240)
def laneWords (h : Height) := if wireWidth h=256 then 3 else if wireWidth h=240 then 4 else 6
def mainLane (h : Height) (j : Nat) := mainPC h+laneWords h*j
def tailWords (h : Height) := laneWords h

theorem phase_counts : ∀ h : Height,passCycles h=passSteps h+7*count h*calls h := by decide +kernel
theorem spend : ((List.finRange 24).map passSteps).sum =60041451 := by decide +kernel
theorem price : ((List.finRange 24).map passCycles).sum =178888676 := by decide +kernel
end CommitGolfCandidate.Chained.BinaryMachine
