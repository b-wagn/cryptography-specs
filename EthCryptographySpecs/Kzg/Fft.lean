import EthCryptographySpecs.Bls
import EthCryptographySpecs.Kzg.Polynomials
import EthCryptographySpecs.Kzg.Constants

/-!
# `Fft`

Number-theoretic transforms over `Fr`, including a coset variant.
-/

namespace EthCryptographySpecs.Kzg

open EthCryptographySpecs.Bls (Fr)

open EthCryptographySpecs.Kzg.Constants

/-- Cooley-Tukey radix-2 forward FFT. `rootsOfUnity` must have the same
length as `vals`. -/
private partial def _fftField
    (vals : Array Fr) (rootsOfUnity : Array Fr)
    : Array Fr :=
  if vals.size ≤ 1 then
    vals
  else
    let halve (xs : Array Fr) (start : Nat) :=
      Array.ofFn (n := xs.size / 2) fun i => xs[start + 2 * i.val]!
    let evens := halve vals 0
    let odds  := halve vals 1
    let halfRoots := halve rootsOfUnity 0
    let l := _fftField evens halfRoots
    let r := _fftField odds  halfRoots
    let n := vals.size
    let halfL := l.size  -- = n / 2
    -- Butterfly: for each `i ∈ [0, n/2)` let `t = r[i] * rootsOfUnity[i]`,
    -- then write `l[i] + t` to `o[i]` and `l[i] - t` to `o[i + n/2]`.
    -- The same root index `i` (not `i + n/2`) is used for both halves.
    Array.ofFn (n := n) fun i =>
      let baseIdx     := if i.val < halfL then i.val else i.val - halfL
      let lAt         := l[baseIdx]!
      let rAt         := r[baseIdx]!
      let yTimesRoot  := rAt * rootsOfUnity[baseIdx]!
      if i.val < halfL then lAt + yTimesRoot
      else                  lAt - yTimesRoot

/-- Forward (`inv = false`) or inverse FFT (`inv = true`) over `vals`.
The inverse reverses the roots of unity and divides each output by
`len(vals)`. -/
def fftField
    (vals : Array Fr) (rootsOfUnity : Array Fr)
    (inv : Bool := false) : Array Fr :=
  if inv then
    let invlen := (Fr.ofNat vals.size).inverse
    -- Reverse: keep roots[0] then reverse roots[1..]
    let reversed := Array.ofFn (n := rootsOfUnity.size) fun i =>
      if i.val = 0 then rootsOfUnity[0]!
      else rootsOfUnity[rootsOfUnity.size - i.val]!
    (_fftField vals reversed).map (· * invlen)
  else
    _fftField vals rootsOfUnity

private def shiftVals
    (vals : Array Fr) (factor : Fr)
    : Array Fr := Id.run do
  let mut shift : Fr := Fr.one
  let mut out : Array Fr := Array.mkEmpty vals.size
  for v in vals do
    out := out.push (v * shift)
    shift := shift * factor
  return out

/-- FFT/IFFT over a coset of the roots of unity. Useful for dividing by
a polynomial that vanishes on the unshifted domain. -/
def cosetFftField
    (vals : Array Fr) (rootsOfUnity : Array Fr)
    (inv : Bool := false) : Array Fr :=
  let shiftFactor : Fr := Fr.ofNat PRIMITIVE_ROOT_OF_UNITY
  if inv then
    let post := fftField vals rootsOfUnity inv
    shiftVals post shiftFactor.inverse
  else
    let pre := shiftVals vals shiftFactor
    fftField pre rootsOfUnity inv

end EthCryptographySpecs.Kzg
