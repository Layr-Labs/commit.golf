import CommitGolfCandidate.K1Manifest
import CommitGolfCandidate.TwoPermutationOpeningImage

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192

/-- The final opener (896 words, no image data): K3-lite + L21 + chain + T238 (programs-final-v2 opening).
Words 0..712 are the record writer (records, cap frontier, size, halt); 713..812 the prefix pass;
813..895 the T238 writer blocks (`a1Start`, `foldStart`, `wiStart`, `wkStart`, `wsStart`). -/
def openingImage : Image := ⟨[
  0x00078a13, 0x00078a93, 0x300806e3, 0x3190006f, 0x00060493, 0x00080913, 0x004009b7, 0x20000337,
  0x00648c33, 0x00331313, 0x006c0b33, 0x00100b93, 0x00048c93, 0x00001d37, 0x10000d93, 0x00043303,
  0x00431393, 0x007b03b3, 0x0003df83, 0x01fa9023, 0x0023df83, 0x01fa9123, 0x0043df83, 0x01fa9223,
  0x0063df83, 0x01fa9323, 0x0083df83, 0x01fa9423, 0x00a3df83, 0x01fa9523, 0x00c3df83, 0x01fa9623,
  0x00e3df83, 0x01fa9723, 0x010a8a93, 0x00831393, 0xc003f393, 0x018383b3, 0x00337513, 0x00154e13,
  0x005e1e13, 0x007e0e33, 0x248e0e13, 0x000e5f83, 0x01fa9023, 0x002e5f83, 0x01fa9123, 0x004e5f83,
  0x01fa9223, 0x006e5f83, 0x01fa9323, 0x008e5f83, 0x01fa9423, 0x00ae5f83, 0x01fa9523, 0x00ce5f83,
  0x01fa9623, 0x00ee5f83, 0x01fa9723, 0x010e5f83, 0x01fa9823, 0x012e5f83, 0x01fa9923, 0x014e5f83,
  0x01fa9a23, 0x016e5f83, 0x01fa9b23, 0x018e5f83, 0x01fa9c23, 0x01ae5f83, 0x01fa9d23, 0x01ce5f83,
  0x01fa9e23, 0x01ee5f83, 0x01fa9f23, 0x00254e13, 0x005e1e13, 0x007e0e33, 0x248e0e13, 0x000e5f83,
  0x03fa9023, 0x002e5f83, 0x03fa9123, 0x004e5f83, 0x03fa9223, 0x006e5f83, 0x03fa9323, 0x008e5f83,
  0x03fa9423, 0x00ae5f83, 0x03fa9523, 0x00ce5f83, 0x03fa9623, 0x00ee5f83, 0x03fa9723, 0x010e5f83,
  0x03fa9823, 0x012e5f83, 0x03fa9923, 0x014e5f83, 0x03fa9a23, 0x016e5f83, 0x03fa9b23, 0x018e5f83,
  0x03fa9c23, 0x01ae5f83, 0x03fa9d23, 0x01ce5f83, 0x03fa9e23, 0x01ee5f83, 0x03fa9f23, 0x00354e13,
  0x005e1e13, 0x007e0e33, 0x248e0e13, 0x000e5f83, 0x05fa9023, 0x002e5f83, 0x05fa9123, 0x004e5f83,
  0x05fa9223, 0x006e5f83, 0x05fa9323, 0x008e5f83, 0x05fa9423, 0x00ae5f83, 0x05fa9523, 0x00ce5f83,
  0x05fa9623, 0x00ee5f83, 0x05fa9723, 0x010e5f83, 0x05fa9823, 0x012e5f83, 0x05fa9923, 0x014e5f83,
  0x05fa9a23, 0x016e5f83, 0x05fa9b23, 0x018e5f83, 0x05fa9c23, 0x01ae5f83, 0x05fa9d23, 0x01ce5f83,
  0x05fa9e23, 0x01ee5f83, 0x05fa9f23, 0x060a8a93, 0x00235313, 0x01330333, 0x00134393, 0x00539393,
  0x007483b3, 0x0003df83, 0x01fa9023, 0x0023df83, 0x01fa9123, 0x0043df83, 0x01fa9223, 0x0063df83,
  0x01fa9323, 0x0083df83, 0x01fa9423, 0x00a3df83, 0x01fa9523, 0x00c3df83, 0x01fa9623, 0x00e3df83,
  0x01fa9723, 0x0103df83, 0x01fa9823, 0x0123df83, 0x01fa9923, 0x0143df83, 0x01fa9a23, 0x0163df83,
  0x01fa9b23, 0x0183df83, 0x01fa9c23, 0x01a3df83, 0x01fa9d23, 0x01c3df83, 0x01fa9e23, 0x01e3df83,
  0x01fa9f23, 0x020a8a93, 0x00135313, 0x00134393, 0x00539393, 0x007483b3, 0x0003df83, 0x01fa9023,
  0x0023df83, 0x01fa9123, 0x0043df83, 0x01fa9223, 0x0063df83, 0x01fa9323, 0x0083df83, 0x01fa9423,
  0x00a3df83, 0x01fa9523, 0x00c3df83, 0x01fa9623, 0x00e3df83, 0x01fa9723, 0x0103df83, 0x01fa9823,
  0x0123df83, 0x01fa9923, 0x0143df83, 0x01fa9a23, 0x0163df83, 0x01fa9b23, 0x0183df83, 0x01fa9c23,
  0x01a3df83, 0x01fa9d23, 0x01c3df83, 0x01fa9e23, 0x1450006f, 0x00135313, 0x00134393, 0x00539393,
  0x007483b3, 0x0003df83, 0x01fa9023, 0x0023df83, 0x01fa9123, 0x0043df83, 0x01fa9223, 0x0063df83,
  0x01fa9323, 0x0083df83, 0x01fa9423, 0x00a3df83, 0x01fa9523, 0x00c3df83, 0x01fa9623, 0x00e3df83,
  0x01fa9723, 0x0103df83, 0x01fa9823, 0x0123df83, 0x01fa9923, 0x0143df83, 0x01fa9a23, 0x0163df83,
  0x01fa9b23, 0x0183df83, 0x01fa9c23, 0x01a3df83, 0x01fa9d23, 0x01c3df83, 0x01fa9e23, 0x01ea8a93,
  0x00135313, 0x00134393, 0x00539393, 0x007483b3, 0x0003df83, 0x01fa9023, 0x0023df83, 0x01fa9123,
  0x0043df83, 0x01fa9223, 0x0063df83, 0x01fa9323, 0x0083df83, 0x01fa9423, 0x00a3df83, 0x01fa9523,
  0x00c3df83, 0x01fa9623, 0x00e3df83, 0x01fa9723, 0x0103df83, 0x01fa9823, 0x0123df83, 0x01fa9923,
  0x0143df83, 0x01fa9a23, 0x0163df83, 0x01fa9b23, 0x0183df83, 0x01fa9c23, 0x01a3df83, 0x01fa9d23,
  0x01c3df83, 0x01fa9e23, 0x01ea8a93, 0x00135313, 0x00134393, 0x00539393, 0x007483b3, 0x0003df83,
  0x01fa9023, 0x0023df83, 0x01fa9123, 0x0043df83, 0x01fa9223, 0x0063df83, 0x01fa9323, 0x0083df83,
  0x01fa9423, 0x00a3df83, 0x01fa9523, 0x00c3df83, 0x01fa9623, 0x00e3df83, 0x01fa9723, 0x0103df83,
  0x01fa9823, 0x0123df83, 0x01fa9923, 0x0143df83, 0x01fa9a23, 0x0163df83, 0x01fa9b23, 0x0183df83,
  0x01fa9c23, 0x01a3df83, 0x01fa9d23, 0x01c3df83, 0x01fa9e23, 0x01ea8a93, 0x00135313, 0x00134393,
  0x00539393, 0x007483b3, 0x0003df83, 0x01fa9023, 0x0023df83, 0x01fa9123, 0x0043df83, 0x01fa9223,
  0x0063df83, 0x01fa9323, 0x0083df83, 0x01fa9423, 0x00a3df83, 0x01fa9523, 0x00c3df83, 0x01fa9623,
  0x00e3df83, 0x01fa9723, 0x0103df83, 0x01fa9823, 0x0123df83, 0x01fa9923, 0x0143df83, 0x01fa9a23,
  0x0163df83, 0x01fa9b23, 0x0183df83, 0x01fa9c23, 0x01a3df83, 0x01fa9d23, 0x01c3df83, 0x01fa9e23,
  0x01ea8a93, 0x00135313, 0x00134393, 0x00539393, 0x007483b3, 0x0003df83, 0x01fa9023, 0x0023df83,
  0x01fa9123, 0x0043df83, 0x01fa9223, 0x0063df83, 0x01fa9323, 0x0083df83, 0x01fa9423, 0x00a3df83,
  0x01fa9523, 0x00c3df83, 0x01fa9623, 0x00e3df83, 0x01fa9723, 0x0103df83, 0x01fa9823, 0x0123df83,
  0x01fa9923, 0x0143df83, 0x01fa9a23, 0x0163df83, 0x01fa9b23, 0x0183df83, 0x01fa9c23, 0x01a3df83,
  0x01fa9d23, 0x01c3df83, 0x01fa9e23, 0x01ea8a93, 0x00135313, 0x00134393, 0x00539393, 0x007483b3,
  0x0003df83, 0x01fa9023, 0x0023df83, 0x01fa9123, 0x0043df83, 0x01fa9223, 0x0063df83, 0x01fa9323,
  0x0083df83, 0x01fa9423, 0x00a3df83, 0x01fa9523, 0x00c3df83, 0x01fa9623, 0x00e3df83, 0x01fa9723,
  0x0103df83, 0x01fa9823, 0x0123df83, 0x01fa9923, 0x0143df83, 0x01fa9a23, 0x0163df83, 0x01fa9b23,
  0x0183df83, 0x01fa9c23, 0x01a3df83, 0x01fa9d23, 0x01c3df83, 0x01fa9e23, 0x01ea8a93, 0x00135313,
  0x00134393, 0x00539393, 0x007483b3, 0x0003df83, 0x01fa9023, 0x0023df83, 0x01fa9123, 0x0043df83,
  0x01fa9223, 0x0063df83, 0x01fa9323, 0x0083df83, 0x01fa9423, 0x00a3df83, 0x01fa9523, 0x00c3df83,
  0x01fa9623, 0x00e3df83, 0x01fa9723, 0x0103df83, 0x01fa9823, 0x0123df83, 0x01fa9923, 0x0143df83,
  0x01fa9a23, 0x0163df83, 0x01fa9b23, 0x0183df83, 0x01fa9c23, 0x01a3df83, 0x01fa9d23, 0x01c3df83,
  0x01fa9e23, 0x01ea8a93, 0x00135313, 0x00134393, 0x00539393, 0x007483b3, 0x0003df83, 0x01fa9023,
  0x0023df83, 0x01fa9123, 0x0043df83, 0x01fa9223, 0x0063df83, 0x01fa9323, 0x0083df83, 0x01fa9423,
  0x00a3df83, 0x01fa9523, 0x00c3df83, 0x01fa9623, 0x00e3df83, 0x01fa9723, 0x0103df83, 0x01fa9823,
  0x0123df83, 0x01fa9923, 0x0143df83, 0x01fa9a23, 0x0163df83, 0x01fa9b23, 0x0183df83, 0x01fa9c23,
  0x01a3df83, 0x01fa9d23, 0x01c3df83, 0x01fa9e23, 0x01ea8a93, 0x00135313, 0x00134393, 0x00539393,
  0x007483b3, 0x0003df83, 0x01fa9023, 0x0023df83, 0x01fa9123, 0x0043df83, 0x01fa9223, 0x0063df83,
  0x01fa9323, 0x0083df83, 0x01fa9423, 0x00a3df83, 0x01fa9523, 0x00c3df83, 0x01fa9623, 0x00e3df83,
  0x01fa9723, 0x0103df83, 0x01fa9823, 0x0123df83, 0x01fa9923, 0x0143df83, 0x01fa9a23, 0x0163df83,
  0x01fa9b23, 0x0183df83, 0x01fa9c23, 0x01a3df83, 0x01fa9d23, 0x01c3df83, 0x01fa9e23, 0x01ea8a93,
  0x00135313, 0x00134393, 0x00539393, 0x007483b3, 0x0003df83, 0x01fa9023, 0x0023df83, 0x01fa9123,
  0x0043df83, 0x01fa9223, 0x0063df83, 0x01fa9323, 0x0083df83, 0x01fa9423, 0x00a3df83, 0x01fa9523,
  0x00c3df83, 0x01fa9623, 0x00e3df83, 0x01fa9723, 0x0103df83, 0x01fa9823, 0x0123df83, 0x01fa9923,
  0x0143df83, 0x01fa9a23, 0x0163df83, 0x01fa9b23, 0x0183df83, 0x01fa9c23, 0x01a3df83, 0x01fa9d23,
  0x01c3df83, 0x01fa9e23, 0x01ea8a93, 0x00135313, 0x00134393, 0x00539393, 0x007483b3, 0x0003df83,
  0x01fa9023, 0x0023df83, 0x01fa9123, 0x0043df83, 0x01fa9223, 0x0063df83, 0x01fa9323, 0x0083df83,
  0x01fa9423, 0x00a3df83, 0x01fa9523, 0x00c3df83, 0x01fa9623, 0x00e3df83, 0x01fa9723, 0x0103df83,
  0x01fa9823, 0x0123df83, 0x01fa9923, 0x0143df83, 0x01fa9a23, 0x0163df83, 0x01fa9b23, 0x0183df83,
  0x01fa9c23, 0x01a3df83, 0x01fa9d23, 0x01c3df83, 0x01fa9e23, 0x01ea8a93, 0x00135313, 0x00134393,
  0x00539393, 0x007483b3, 0x0003df83, 0x01fa9023, 0x0023df83, 0x01fa9123, 0x0043df83, 0x01fa9223,
  0x0063df83, 0x01fa9323, 0x0083df83, 0x01fa9423, 0x00a3df83, 0x01fa9523, 0x00c3df83, 0x01fa9623,
  0x00e3df83, 0x01fa9723, 0x0103df83, 0x01fa9823, 0x0123df83, 0x01fa9923, 0x0143df83, 0x01fa9a23,
  0x0163df83, 0x01fa9b23, 0x0183df83, 0x01fa9c23, 0x01a3df83, 0x01fa9d23, 0x01c3df83, 0x2c80006f,
  0x01ca8a93, 0x00135313, 0x00331393, 0x007d03b3, 0x0173b023, 0x00840413, 0xfff90913, 0x00090463,
  0xe1cff06f, 0x0ff00313, 0x00431393, 0x007d03b3, 0x0003be03, 0x0083be83, 0x01de6e33, 0x00331393,
  0x007d03b3, 0x01c3b023, 0xfff30313, 0xfc031ee3, 0x3000006f, 0x00331393, 0x007d03b3, 0x0003be03,
  0x000e0863, 0x09b37863, 0x00131313, 0xfe9ff06f, 0x00531393, 0x007c83b3, 0x0003df83, 0x01fa9023,
  0x0023df83, 0x01fa9123, 0x0043df83, 0x01fa9223, 0x0063df83, 0x01fa9323, 0x0083df83, 0x01fa9423,
  0x00a3df83, 0x01fa9523, 0x00c3df83, 0x01fa9623, 0x00e3df83, 0x01fa9723, 0x0103df83, 0x01fa9823,
  0x0123df83, 0x01fa9923, 0x0143df83, 0x01fa9a23, 0x0163df83, 0x01fa9b23, 0x0183df83, 0x01fa9c23,
  0x01a3df83, 0x01fa9d23, 0x01c3df83, 0x2700006f, 0x01ea8a93, 0x00100393, 0x00730e63, 0x00137393,
  0x00038663, 0x00135313, 0xfedff06f, 0x00130313, 0xf45ff06f, 0x414a85b3, 0x00100293, 0x00000513,
  0x00000073, 0x00068413, 0x00060493, 0x00080913, 0x004009b7, 0x20000337, 0x00648c33, 0x00331313,
  0x006c0b33, 0x00100b93, 0x00048c93, 0x00001d37, 0x10000d93, 0x40000513, 0x60000613, 0x0c800593,
  0x00100693, 0x00000293, 0x00040713, 0x00090893, 0x00b00e93, 0x008b3f83, 0x01f53423, 0x010b3f83,
  0x01f53823, 0x018b3f83, 0x01f53c23, 0xfff00213, 0x00073303, 0x00235e13, 0x084e0663, 0x000e0213,
  0x00335393, 0x00b39393, 0x018383b3, 0x00437f13, 0x020f1263, 0x0a838513, 0x20038613, 0x08838f13,
  0x0200006f, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0xfe038513, 0x60038613, 0x0a838f13,
  0x00200693, 0x00000073, 0x00100693, 0x60000613, 0x40000513, 0x001e4e13, 0x013e0e33, 0x005e1e13,
  0x009e0e33, 0x000f3f83, 0x01fe3023, 0x008f3f83, 0x01fe3423, 0x010f3f83, 0x01fe3823, 0x018f3f83,
  0x01fe3c23, 0x03a37e33, 0x03de5f33, 0x03de7e33, 0x02200f93, 0x03ff7f33, 0x03df0fb3, 0x41c303b3,
  0x41f383b3, 0x00138393, 0x00839393, 0x01a383b3, 0x00753023, 0x00000073, 0x000f0c63, 0x00060513,
  0x00000073, 0xffff0f13, 0xfe0f1ce3, 0x40000513, 0xfffe0393, 0x00439393, 0x01cbe863, 0x00000393,
  0x017e1463, 0x0b800393, 0x00c383b3, 0x00431f13, 0x016f0f33, 0x0003bf83, 0x01ff3023, 0x0083bf83,
  0x01ff3423, 0x00870713, 0xfff88893, 0xee0892e3, 0xb8cff06f, 0x01e3df83, 0x01fa9f23, 0x020a8a93,
  0xeb4ff06f, 0xf4aade03, 0x00ef9e93, 0x01de6e33, 0xf5ca9523, 0x002fdf93, 0xf68ade03, 0x00ef9e93,
  0x01de6e33, 0xf7ca9423, 0x002fdf93, 0xf86ade03, 0x00ef9e93, 0x01de6e33, 0xf9ca9323, 0x002fdf93,
  0xfa4ade03, 0x00ef9e93, 0x01de6e33, 0xfbca9223, 0x002fdf93, 0xfc2ade03, 0x00ef9e93, 0x01de6e33,
  0xfdca9123, 0x002fdf93, 0xfe0ade03, 0x00ef9e93, 0x01de6e33, 0xffca9023, 0x002fdf93, 0xffeade03,
  0x00ef9e93, 0x01de6e33, 0xffca9f23, 0xcb5ff06f, 0x00100313, 0x00700f13, 0xcfdff06f, 0x000f0863,
  0xffff0f13, 0x01fa9e23, 0xd89ff06f, 0x00700f13, 0xf4aade03, 0x00ef9e93, 0x01de6e33, 0xf5ca9523,
  0x002fdf93, 0xf68ade03, 0x00ef9e93, 0x01de6e33, 0xf7ca9423, 0x002fdf93, 0xf86ade03, 0x00ef9e93,
  0x01de6e33, 0xf9ca9323, 0x002fdf93, 0xfa4ade03, 0x00ef9e93, 0x01de6e33, 0xfbca9223, 0x002fdf93,
  0xfc2ade03, 0x00ef9e93, 0x01de6e33, 0xfdca9123, 0x002fdf93, 0xfe0ade03, 0x00ef9e93, 0x01de6e33,
  0xffca9023, 0x002fdf93, 0xffeade03, 0x00ef9e93, 0x01de6e33, 0xffca9f23, 0xffea8a93, 0xcf5ff06f], []⟩

/-- Number of words in the opener image. -/
abbrev openingWords : Nat := 896

/-! T238 writer blocks appended after the prefix pass (all writer code addresses live here). -/
/-- A1: the 16th halfword of the level-1 sibling, then `addi x21,x21,32; jal <221>`. -/
def a1Start : Nat := 813
/-- F: the record fold (34 words) and `jal <640>`. -/
def foldStart : Nat := 817
/-- WI: `addi x6,x0,1; addi x30,x0,7; jal <661>`. -/
def wiStart : Nat := 852
/-- WK: `beq x30,x0,<WS>; addi x30,x30,-1; sh x31,28(x21); jal <700>`. -/
def wkStart : Nat := 855
/-- WS: `addi x30,x0,7`, the fold (34 words), `addi x21,x21,-2; jal <700>`. -/
def wsStart : Nat := 859

theorem packed_fetch_base (state : MachineState) (index : Nat) (instruction : Instr)
    (bounded : index < 896) (pc : state.pc = BitVec.ofNat 64 (4096+4*index))
    (decoded : (openingImage.code[index]?).bind Opening.decodeBase = some instruction) :
    fetch openingImage state = some (.base instruction) := by
  have current : state.pc.toNat = 4096+4*index := by
    rw [pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  rw [fetch, current, ite_eq_left (by omega), show (4096+4*index-4096)/4=index by omega]
  cases code : openingImage.code[index]? with
  | none => simp [code] at decoded
  | some word =>
    simp [code, Opening.decodeBase] at decoded
    cases dec : decodeInstruction word with
    | none => simp [dec] at decoded
    | some result =>
      cases result with
      | base inst =>
        simp [dec] at decoded
        simpa [decoded] using dec
      | word op rd rs₁ rs₂ => simp [dec] at decoded
      | sraiw rd rs sh => simp [dec] at decoded

set_option maxHeartbeats 1600000 in
/-- All decoded instruction literals and all data bytes match the submitted JSON image. -/
private theorem image_word_match : ∀ k : Fin 896,
    (K1Artifact.submission.image .opening).code.getD k.val 0 = openingImage.code.getD k.val 0 := by
  intro k
  simp only [K1Artifact.submission]
  rw [ArtifactEncoding.getD_decode 32 _ _ k.isLt]
  revert k
  decide

theorem image_actual : (K1Artifact.submission.image .opening) = openingImage := by
  have words : (K1Artifact.submission.image .opening).code = openingImage.code := by
    apply List.ext_getElem
    · simp only [K1Artifact.submission,ArtifactEncoding.length_decode];rfl
    · intro n hn hn'
      have h := image_word_match ⟨n,hn'⟩
      change (K1Artifact.submission.image .opening).code[n]?.getD 0 = openingImage.code[n]?.getD 0 at h
      rw [List.getElem?_eq_getElem hn, List.getElem?_eq_getElem hn'] at h
      exact h
  exact congrArg₂ Image.mk words rfl

/-- The straight-line `lhu x31,2k(src); sh x31,dest+2k(x21)` copy sites of the writer. `sibling l` is the
copy of writer level `l+1`; the level-13 site (`l = 12`) and the cap copy only the first 14 halfwords, the
15th halfword going through the T238 fold (record) or WK/WS (cap). -/
inductive CopySite where
  | nonce
  | quartet (ordinal : Fin 3)
  | firstSibling
  | sibling (level : Fin 13)
  | cap

def CopySite.start : CopySite → Nat
  | .nonce => 18
  | .quartet ordinal => 43 + 36*ordinal.val
  | .firstSibling => 153
  | .sibling level => 190+35*level.val
  | .cap => 670

def CopySite.halfwords : CopySite → Nat
  | .nonce => 8
  | .quartet _ | .firstSibling => 16
  | .sibling level => if level.val = 12 then 14 else 15
  | .cap => 14

def CopySite.source : CopySite → Reg
  | .quartet _ => .x28
  | _ => .x7

def CopySite.destOffset : CopySite → Nat
  | .quartet ordinal => 32*ordinal.val
  | _ => 0

def copyLoad (offset : Nat) : Instr := .LHU .x31 .x7 (BitVec.ofNat 12 (2*offset))
def copyStore (offset : Nat) : Instr := .SH .x21 .x31 (BitVec.ofNat 12 (2*offset))

def PairDecodes (site : CopySite) (offset : Nat) : Prop :=
    (openingImage.code[site.start+2*offset]?).bind Opening.decodeBase =
      some (.LHU .x31 site.source (BitVec.ofNat 12 (2*offset))) ∧
    (openingImage.code[site.start+2*offset+1]?).bind Opening.decodeBase =
      some (.SH .x21 .x31 (BitVec.ofNat 12 (site.destOffset+2*offset)))

private instance (site : CopySite) (offset : Nat) : Decidable (PairDecodes site offset) := by
  unfold PairDecodes
  infer_instance

set_option maxHeartbeats 2500000 in
theorem copy_sites_decoded (site : CopySite) (offset : Fin site.halfwords) :
    PairDecodes site offset.val := by
  cases site with
  | nonce => exact (show ∀ i : Fin 8, PairDecodes .nonce i.val by decide) offset
  | quartet j => exact (show ∀ j : Fin 3, ∀ i : Fin 16, PairDecodes (.quartet j) i.val by decide) j offset
  | firstSibling => exact (show ∀ i : Fin 16, PairDecodes .firstSibling i.val by decide) offset
  | sibling level =>
    have all : ∀ j : Fin 13, ∀ i : Fin 15, i.val < (CopySite.sibling j).halfwords →
        PairDecodes (.sibling j) i.val := by decide
    exact all level ⟨offset.val, by have := offset.isLt; simp only [CopySite.halfwords] at this; split at this <;> omega⟩
      offset.isLt
  | cap => exact (show ∀ i : Fin 14, PairDecodes .cap i.val by decide) offset

theorem copy_site_halfwords (site : CopySite) : site.halfwords ≤ 16 := by
  cases site with
  | sibling l => simp only [CopySite.halfwords]; split <;> omega
  | _ => simp [CopySite.halfwords]

theorem copy_site_start (site : CopySite) : site.start ≤ 670 := by
  cases site with
  | quartet j => have := j.isLt; simp only [CopySite.start]; omega
  | sibling l => have := l.isLt; simp only [CopySite.start]; omega
  | _ => simp [CopySite.start]

theorem copy_site_inside (site : CopySite) (offset : Fin site.halfwords) :
    site.start+2*offset.val+1 < 896 := by
  have h := offset.isLt
  have a := copy_site_halfwords site
  have b := copy_site_start site
  omega

theorem fetch_copy_load (site : CopySite) (offset : Fin site.halfwords) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (4096+4*(site.start+2*offset.val))) :
    fetch openingImage state = some (.base (.LHU .x31 site.source (BitVec.ofNat 12 (2*offset.val)))) :=
  packed_fetch_base _ _ _ (by have := copy_site_inside site offset; omega) pc
    (copy_sites_decoded site offset).1

theorem fetch_copy_store (site : CopySite) (offset : Fin site.halfwords) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (4096+4*(site.start+2*offset.val+1))) :
    fetch openingImage state = some (.base (.SH .x21 .x31 (BitVec.ofNat 12 (site.destOffset+2*offset.val)))) :=
  packed_fetch_base _ _ _ (copy_site_inside site offset) pc
    (copy_sites_decoded site offset).2

/-! ### T238 code -/

/-- `-182+30j` as a 12-bit immediate: the halfword at byte 28 of slot `j` of a packed group, relative
to the base of its eighth slot. -/
def foldOffset (j : Nat) : BitVec 12 := BitVec.ofNat 12 (3914+30*j)

/-- One fold step: OR bits `2j, 2j+1` of the eighth node's top halfword (in `x31`) into bits 14, 15 of
slot `j`'s halfword at byte 28. -/
def foldStep (j : Nat) : List Instr :=
  [.LHU .x28 .x21 (foldOffset j), .SLLI .x29 .x31 14, .OR .x28 .x28 .x29, .SH .x21 .x28 (foldOffset j)]

/-- The 34-word fold shared by the record (F) and the cap (WS). -/
def foldCode : List Instr :=
  foldStep 0 ++ [.SRLI .x31 .x31 2] ++ foldStep 1 ++ [.SRLI .x31 .x31 2] ++ foldStep 2 ++
    [.SRLI .x31 .x31 2] ++ foldStep 3 ++ [.SRLI .x31 .x31 2] ++ foldStep 4 ++ [.SRLI .x31 .x31 2] ++
    foldStep 5 ++ [.SRLI .x31 .x31 2] ++ foldStep 6

theorem fold_code_length : foldCode.length = 34 := rfl

/-- The fold at `foldStart` (F) and at `wsStart+1` (WS). -/
theorem fold_decoded : ∀ i : Fin 34,
    (openingImage.code[foldStart+i.val]?).bind Opening.decodeBase = some (foldCode[i.val]?.getD .EBREAK) ∧
    (openingImage.code[wsStart+1+i.val]?).bind Opening.decodeBase = some (foldCode[i.val]?.getD .EBREAK) := by
  decide

/-- The T238 rows outside the fold, as (word, instruction). -/
def t238Rows : List (Nat × Instr) :=
  [(220, .JAL .x0 (BitVec.ofNat 21 (4*(a1Start-220)))),
   (a1Start, .LHU .x31 .x7 30), (a1Start+1, .SH .x21 .x31 30), (a1Start+2, .ADDI .x21 .x21 32),
   (a1Start+3, .JAL .x0 (BitVec.ofNat 21 (2^21-4*(a1Start+3-221)))),
   (638, .LHU .x31 .x7 28), (639, .JAL .x0 (BitVec.ofNat 21 (4*(foldStart-639)))),
   (foldStart+34, .JAL .x0 (BitVec.ofNat 21 (2^21-4*(foldStart+34-640)))),
   (640, .ADDI .x21 .x21 28), (641, .SRLI .x6 .x6 1),
   (660, .JAL .x0 (BitVec.ofNat 21 (4*(wiStart-660)))),
   (wiStart, .ADDI .x6 .x0 1), (wiStart+1, .ADDI .x30 .x0 7),
   (wiStart+2, .JAL .x0 (BitVec.ofNat 21 (2^21-4*(wiStart+2-661)))),
   (698, .LHU .x31 .x7 28), (699, .JAL .x0 (BitVec.ofNat 21 (4*(wkStart-699)))),
   (wkStart, .BEQ .x30 .x0 (BitVec.ofNat 13 (4*(wsStart-wkStart)))), (wkStart+1, .ADDI .x30 .x30 4095),
   (wkStart+2, .SH .x21 .x31 28), (wkStart+3, .JAL .x0 (BitVec.ofNat 21 (2^21-4*(wkStart+3-700)))),
   (wsStart, .ADDI .x30 .x0 7), (wsStart+35, .ADDI .x21 .x21 4094),
   (wsStart+36, .JAL .x0 (BitVec.ofNat 21 (2^21-4*(wsStart+36-700)))),
   (700, .ADDI .x21 .x21 30)]

theorem t238_rows_decoded : ∀ r ∈ t238Rows,
    r.1 < 896 ∧ (openingImage.code[r.1]?).bind Opening.decodeBase = some r.2 := by
  decide

theorem t238_fetch (state : MachineState) (row : Nat) (instruction : Instr) (member : (row, instruction) ∈ t238Rows)
    (pc : state.pc = BitVec.ofNat 64 (4096+4*row)) :
    fetch openingImage state = some (.base instruction) :=
  packed_fetch_base state row instruction (t238_rows_decoded _ member).1 pc (t238_rows_decoded _ member).2

end TwoPermutationPrototype.GroupedOpening
