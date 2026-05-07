import EthCryptographySpecs.Bls
import EthCryptographySpecs.Kzg.Constants
import EthCryptographySpecs.Kzg.TrustedSetupData

/-!
# `TrustedSetup`

Holder for the KZG trusted setup (Lagrange-basis G1, monomial-basis
G1, monomial-basis G2).

The compressed bytes are embedded directly in `TrustedSetupData` as
hex strings. At module-init we decode them, decompress to projective
points, and stash both forms in a global ref accessed via
`TrustedSetup.get!`.
-/

namespace EthCryptographySpecs.Kzg

/-- The KZG trusted setup. Each entry is stored as both the projective
G1/G2 point and its compressed-byte form; a few callers consume the
bytes directly. -/
structure TrustedSetup where
  g1Lagrange       : Array Bls.G1
  g1LagrangeBytes  : Array ByteArray
  g1Monomial       : Array Bls.G1
  g1MonomialBytes  : Array ByteArray
  g2Monomial       : Array Bls.G2
  g2MonomialBytes  : Array ByteArray
deriving Inhabited

namespace TrustedSetup

private def nibble (c : Char) : Option UInt8 :=
  let n := c.toNat
  if 0x30 ≤ n ∧ n ≤ 0x39 then some (UInt8.ofNat (n - 0x30))
  else if 0x61 ≤ n ∧ n ≤ 0x66 then some (UInt8.ofNat (n - 0x57))
  else if 0x41 ≤ n ∧ n ≤ 0x46 then some (UInt8.ofNat (n - 0x37))
  else none

private def hexToBytesAux : List Char → ByteArray → Option ByteArray
  | [], acc => some acc
  | [_], _ => none
  | hi :: lo :: rest, acc =>
    match nibble hi, nibble lo with
    | some h, some l => hexToBytesAux rest (acc.push ((h <<< 4) ||| l))
    | _, _ => none

private def hexToByteArray (s : String) : IO ByteArray := do
  match hexToBytesAux s.toList ByteArray.empty with
  | some b => pure b
  | none   => throw <| IO.userError s!"invalid hex in embedded trusted setup: {s}"

private def buildEmbedded : IO TrustedSetup := do
  let toG1 (b : ByteArray) : IO Bls.G1 := do
    match Bls.G1.uncompress b with
    | some p => pure p
    | none   => throw <| IO.userError "trusted setup contains invalid G1 point"
  let toG2 (b : ByteArray) : IO Bls.G2 := do
    match Bls.G2.uncompress b with
    | some p => pure p
    | none   => throw <| IO.userError "trusted setup contains invalid G2 point"
  let g1LagrangeBytes ← TrustedSetupData.g1LagrangeHex.mapM hexToByteArray
  let g1MonomialBytes ← TrustedSetupData.g1MonomialHex.mapM hexToByteArray
  let g2MonomialBytes ← TrustedSetupData.g2MonomialHex.mapM hexToByteArray
  let g1Lagrange ← g1LagrangeBytes.mapM toG1
  let g1Monomial ← g1MonomialBytes.mapM toG1
  let g2Monomial ← g2MonomialBytes.mapM toG2
  pure {
    g1Lagrange, g1LagrangeBytes,
    g1Monomial, g1MonomialBytes,
    g2Monomial, g2MonomialBytes,
  }

/-! ## Global slot

Seeded eagerly at module-init from the embedded bytes; callers never
have to check whether the setup is loaded. -/

initialize globalRef : IO.Ref TrustedSetup ← do
  IO.mkRef (← buildEmbedded)

/-- Retrieve the loaded setup. -/
@[inline] def get! : IO TrustedSetup := globalRef.get

end TrustedSetup

end EthCryptographySpecs.Kzg
