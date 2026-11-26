import CommitGolfCandidate.S5Code
import CommitGolfCandidate.S5Layout
import CommitGolfCandidate.Stage3cParent
namespace CommitGolfCandidate.S5Machine
open CommitGolfCandidate.Chained
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
def passHeader (h : Height) : Nat := ([7230, 8020, 9063, 10106, 11149, 12191, 13741, 15291, 16841, 16892, 16972, 17046, 17161, 17270, 17457, 17590, 17776, 18059, 18342, 18367, 18392, 18417, 18442, 18467] : List Nat)[h.val]?.getD 0
def mainPC (h : Height) : Nat := ([7238, 8028, 9071, 10114, 11156, 12200, 13750, 15300, 16864, 16914, 16994, 17067, 17182, 17291, 17478, 17610, 17785, 18068, 0, 0, 0, 0, 0, 0] : List Nat)[h.val]?.getD 0
def passEnd (h : Height) : Nat := ([8020, 9063, 10106, 11149, 12191, 13741, 15291, 16841, 16892, 16972, 17046, 17161, 17270, 17457, 17590, 17776, 18059, 18342, 18367, 18392, 18417, 18442, 18467, 18478] : List Nat)[h.val]?.getD 0
def passSteps (h : Height) : Nat := ([17043676, 11318046, 5659034, 2829522, 1414771, 1057731, 529691, 264851, 305867, 218480, 142034, 87411, 60125, 38267, 19173, 9594, 552, 282, 287, 149, 87, 49, 37, 11] : List Nat)[h.val]?.getD 0
def passCycles (h : Height) : Nat := ([56190518, 30891467, 15445748, 7722879, 3861453, 2281072, 1141365, 570688, 611711, 524324, 371438, 240347, 174869, 114763, 57477, 28746, 1154, 583, 441, 226, 129, 70, 51, 18] : List Nat)[h.val]?.getD 0
def tailPC (h : Height) : Nat := ([8010, 9052, 10095, 11138, 12180, 13728, 15278, 16828, 0, 0, 0, 0, 0, 0, 0, 0, 18046, 18329, 18354, 18379, 18404, 18429, 18454, 18475] : List Nat)[h.val]?.getD 0
def mainExit (h : Height) : Nat := ([8006, 9048, 10091, 11134, 12176, 13724, 15274, 16824, 16892, 16954, 17046, 17131, 17270, 17403, 17590, 17722, 18042, 18325, 18367, 18392, 18417, 18442, 18467, 18478] : List Nat)[h.val]?.getD 0

def count (h : Height) :=levelCount (h.val+1)
def chained (h : Height) := 8≤h.val ∧ h.val<16
instance (h : Height) : Decidable (chained h) := inferInstanceAs (Decidable (8≤h.val ∧ h.val<16))
def tileSize (h : Height) := if chained h then 2 else if 252≤count h then 252 else if 42≤count h then 42 else 0
def tiles (h : Height) :=count h/tileSize h
def remainder (h : Height) :=count h%tileSize h
def mask240 (h : Height) := decide (wireWidth h=240)
def laneWords (h : Height) := if mask240 h then 4 else if wireWidth h=238 then 6 else 3
def mainLane (h : Height) (j : Nat) := mainPC h+laneWords h*j+j/42+j/84
def tailWords (h : Height) := if h.val=23 then 3 else laneWords h+7

theorem phase_counts : ∀ h : Height,passCycles h=passSteps h+7*count h*calls h := by decide +kernel
theorem spend : ((List.finRange 24).map passSteps).sum =40999727 := by decide +kernel
theorem price : ((List.finRange 24).map passCycles).sum =120231537 := by decide +kernel
end CommitGolfCandidate.S5Machine
