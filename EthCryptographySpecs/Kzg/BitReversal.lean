/-!
# `BitReversal`

`bitReversalPermutation` and friends. Operate on any `Array α`.
-/

namespace EthCryptographySpecs.Kzg.BitReversal

/-- Reverse the lower `bits` bits of `n`. -/
def reverseBitsAux (n : Nat) (bits : Nat) : Nat := Id.run do
  let mut x := n
  let mut r := 0
  for _ in [:bits] do
    r := (r <<< 1) ||| (x &&& 1)
    x := x >>> 1
  return r

/-- Reverse the bit order of `n` over `log2 order` bits. Requires
`order` to be a positive power of two. -/
def reverseBits (n order : Nat) : Nat :=
  reverseBitsAux n order.log2

/-- Bit-reversed permutation of `seq`: `out[i] = seq[reverseBits i (size seq)]`.
The permutation is an involution. -/
def bitReversalPermutation {α : Type _} [Inhabited α]
    (seq : Array α) : Array α :=
  Array.ofFn (n := seq.size) fun i =>
    seq[reverseBits i.val seq.size]!

end EthCryptographySpecs.Kzg.BitReversal
