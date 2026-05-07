/-!
# `Fp`

The BLS12-381 base field. `Fp` elements live in `[0, p)` where

  p = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f624
      1eabfffeb153ffffb9feffffffffaaab

We represent elements with bare `Nat`, reducing modulo `p` after every
operation. Inversion uses Fermat's little theorem (`x^(p-2)`); square root
uses the fact that `p ≡ 3 (mod 4)` so `sqrt(x) = x^((p+1)/4)`.

There's no Montgomery form, Barrett reduction, or other optimization
here: the goal is clarity, not speed.
-/

namespace EthCryptographySpecs.Bls

/-- BLS12-381 base field modulus. -/
def Fp.modulus : Nat :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

/-- An element of the BLS12-381 base field. -/
structure Fp where
  val : Nat
deriving Inhabited, BEq, Repr

namespace Fp

@[inline] def ofNat (n : Nat) : Fp := ⟨n % modulus⟩
instance : OfNat Fp n := ⟨ofNat n⟩

@[inline] def zero : Fp := ⟨0⟩
@[inline] def one  : Fp := ⟨1⟩

@[inline] def add (a b : Fp) : Fp := ⟨(a.val + b.val) % modulus⟩
@[inline] def sub (a b : Fp) : Fp := ⟨(a.val + modulus - b.val) % modulus⟩
@[inline] def neg (a : Fp)   : Fp := ⟨(modulus - a.val) % modulus⟩
@[inline] def mul (a b : Fp) : Fp := ⟨(a.val * b.val) % modulus⟩

instance : Add Fp := ⟨add⟩
instance : Sub Fp := ⟨sub⟩
instance : Mul Fp := ⟨mul⟩
instance : Neg Fp := ⟨neg⟩

@[inline] def beq (a b : Fp) : Bool := a.val == b.val
@[inline] def isZero (a : Fp) : Bool := a.val == 0

/-- Square-and-multiply modular exponentiation. -/
partial def powNat (base : Fp) (e : Nat) : Fp :=
  if e = 0 then one
  else
    let half := powNat (base * base) (e / 2)
    if e % 2 = 1 then base * half else half

/-- Multiplicative inverse via Fermat's little theorem. -/
@[inline] def inverse (a : Fp) : Fp := powNat a (modulus - 2)

instance : Div Fp := ⟨fun a b => a * b.inverse⟩

/-- Square root, valid for `p ≡ 3 (mod 4)`. Returns `none` if `a` is not
a square. -/
def sqrt (a : Fp) : Option Fp :=
  let cand := powNat a ((modulus + 1) / 4)
  if (cand * cand).beq a then some cand else none

/-- Legendre symbol: `1` for nonzero squares, `p−1` for non-squares,
`0` for zero. -/
def legendre (a : Fp) : Fp := powNat a ((modulus - 1) / 2)

/-- Decode big-endian bytes as a `Nat`. -/
def bytesBEToNat (b : ByteArray) : Nat := Id.run do
  let mut acc : Nat := 0
  for i in [:b.size] do
    acc := (acc <<< 8) ||| b[i]!.toNat
  return acc

/-- Decode a 48-byte big-endian integer as an `Fp`. Returns `none` if
the integer is `≥ p`. -/
def fromBytesBE (b : ByteArray) : Option Fp :=
  if b.size ≠ 48 then none
  else
    let n := bytesBEToNat b
    if n < modulus then some ⟨n⟩ else none

/-- Encode as 48 big-endian bytes. -/
def toBytesBE (a : Fp) : ByteArray :=
  ByteArray.mk <| Array.ofFn (n := 48) fun i =>
    UInt8.ofNat ((a.val >>> ((47 - i.val) * 8)) &&& 0xff)

end Fp

end EthCryptographySpecs.Bls
