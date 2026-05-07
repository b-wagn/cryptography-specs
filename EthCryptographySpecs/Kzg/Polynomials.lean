import EthCryptographySpecs.Bls
import EthCryptographySpecs.Kzg.Constants
import EthCryptographySpecs.Kzg.BitReversal

/-!
# `Polynomials`

Polynomial helpers used by the blob-commitment surface of KZG. These
are field-element manipulations independent of the trusted setup.

`Polynomial` is a fixed-length sequence of `Fr`s
(conceptually `Vector[Fr, FIELD_ELEMENTS_PER_BLOB]`). We
represent it as `Array Fr` and rely on length checks at
the boundaries.

`PolynomialCoeff` is the same shape but for coefficient form, used by
the cell-proof surface. Function names are picked to avoid collision
(`evaluatePolynomialcoeff` vs `evaluatePolynomialInEvaluationForm`).
-/

namespace EthCryptographySpecs.Kzg

open EthCryptographySpecs.Bls (Fr)

open EthCryptographySpecs.Kzg.Constants
open EthCryptographySpecs.Kzg.BitReversal

/-! ## Type aliases -/

abbrev Polynomial      := Array Fr
abbrev PolynomialCoeff := Array Fr
abbrev Blob            := ByteArray
abbrev Bytes32         := ByteArray
abbrev Bytes48         := ByteArray

/-! ## Bytes <-> field element helpers -/

/-- SHA-256 over the input bytes. -/
@[inline] def hash (data : ByteArray) : ByteArray := Bls.sha256 data

/-- Encode `n` as `len` big-endian bytes. -/
def intToBytesBE (n : Nat) (len : Nat) : ByteArray :=
  ByteArray.mk <| Array.ofFn (n := len) fun i =>
    UInt8.ofNat ((n >>> ((len - 1 - i.val) * 8)) &&& 0xff)

/-- Decode big-endian bytes as a `Nat`. -/
def bytesBEToNat (b : ByteArray) : Nat := Id.run do
  let mut acc : Nat := 0
  for i in [:b.size] do
    acc := (acc <<< 8) ||| b[i]!.toNat
  return acc

/-- Hash `data` and reduce the SHA-256 output modulo the BLS modulus
into an `Fr`. The output is not uniform over the field. -/
def hashToBlsField (data : ByteArray) : Fr :=
  let h := hash data
  -- Reduce the 256-bit hash modulo BLS_MODULUS, then construct the field element.
  Fr.ofNat (bytesBEToNat h)

/-- Decode a 32-byte big-endian integer as an `Fr`. Returns `none` if
the integer is `≥ BLS_MODULUS` or the input has the wrong size. -/
def bytesToBlsField (b : Bytes32) : Option Fr :=
  if b.size = BYTES_PER_FIELD_ELEMENT then
    Fr.fromBytesBE b
  else
    none

/-- `bytesToBlsField` that panics on invalid input. -/
@[inline] def bytesToBlsField! (b : Bytes32) : Fr :=
  match bytesToBlsField b with
  | some f => f
  | none   => panic! "bytesToBlsField: bytes do not represent a valid field element"

/-- Encode `x` as 32 big-endian bytes. -/
@[inline] def blsFieldToBytes (x : Fr) : Bytes32 := x.toBytesBE

/-- Return `[x^0, x^1, ..., x^(n-1)]`. -/
def computePowers (x : Fr) (n : Nat) : Array Fr := Id.run do
  let mut current := Fr.one
  let mut out : Array Fr := Array.mkEmpty n
  for _ in [:n] do
    out := out.push current
    current := current * x
  return out

/-- Return the `order`-th roots of unity in `Fr`. Requires `order` to
divide `BLS_MODULUS - 1`. -/
def computeRootsOfUnity (order : Nat) : Array Fr :=
  let exponent := (BLS_MODULUS - 1) / order
  let root :=
    (Fr.ofNat PRIMITIVE_ROOT_OF_UNITY) ^ (Fr.ofNat exponent)
  computePowers root order

/-! ## Blob <-> Polynomial -/

/-- Convert a blob to a sequence of `Fr` field elements. Returns `none`
if any 32-byte chunk represents a value `≥ BLS_MODULUS`. -/
private def blobToPolynomial (blob : Blob) : Option Polynomial := Id.run do
  if blob.size ≠ BYTES_PER_BLOB then return none
  let mut poly : Array Fr := Array.mkEmpty FIELD_ELEMENTS_PER_BLOB
  for i in [:FIELD_ELEMENTS_PER_BLOB] do
    let start := i * BYTES_PER_FIELD_ELEMENT
    let stop  := (i + 1) * BYTES_PER_FIELD_ELEMENT
    match bytesToBlsField (blob.extract start stop) with
    | some f => poly := poly.push f
    | none   => return none
  return some poly

/-- `IO`-friendly `blobToPolynomial` that throws on invalid input. -/
def blobToPolynomialIO (blob : Blob) : IO Polynomial := do
  match blobToPolynomial blob with
  | some p => pure p
  | none   => throw <| IO.userError "blob contains a non-canonical field element"

/-! ## Evaluating a polynomial in evaluation form -/

/-- The bit-reversed `size`-th roots of unity. Recomputed on every call. -/
def rootsOfUnityBrp (size : Nat) : Array Fr :=
  bitReversalPermutation (computeRootsOfUnity size)

/-- Evaluate an evaluation-form polynomial at `z`. Indexes directly when
`z` is in the domain; otherwise uses the barycentric formula
`f(z) = (z^WIDTH − 1) / WIDTH · Σ_i (f(D[i]) · D[i]) / (z − D[i])`. -/
def evaluatePolynomialInEvaluationForm
    (polynomial : Polynomial) (z : Fr) : Fr := Id.run do
  let width := polynomial.size
  -- Caller must pass `width == FIELD_ELEMENTS_PER_BLOB`; the public
  -- entry points enforce this, so we don't re-check here.
  let inverseWidth := (Fr.ofNat width).inverse
  let domain := rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB
  -- Fast path: z is in the domain.
  for i in [:domain.size] do
    if domain[i]! == z then
      return polynomial[i]!
  -- Barycentric formula.
  let mut acc : Fr := Fr.zero
  for i in [:width] do
    let a := polynomial[i]! * domain[i]!
    let b := z - domain[i]!
    acc := acc + (a / b)
  let r := z ^ (Fr.ofNat width) - Fr.one
  return acc * r * inverseWidth

end EthCryptographySpecs.Kzg
