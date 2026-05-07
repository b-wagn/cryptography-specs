import EthCryptographySpecs.Bls.HashToCurve
import EthCryptographySpecs.Bls.Pairing

/-!
# `Signatures`

BLS signature verification per IRTF draft-irtf-cfrg-bls-signature, plus
the Ethereum wrappers `eth_aggregate_pubkeys` and `eth_fast_aggregate_verify`.

The Ethereum consensus uses the proof-of-possession (POP) scheme with
G1 pubkeys / G2 signatures; the DST is fixed as
`BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_`.
-/

namespace EthCryptographySpecs.Bls.Signatures

open EthCryptographySpecs.Bls

/-- DST for the POP-scheme G2 hash-to-curve. -/
def DST : ByteArray :=
  String.toUTF8 "BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_"

/-- Compressed-G2 encoding of the point at infinity (96 bytes; high
bits of byte 0 set to compressed+infinity). -/
def G2_POINT_AT_INFINITY : ByteArray := G2.infinityBytes

/-- IRTF `signature_subgroup_check`. Slow but correct. -/
private def signatureSubgroupCheck (sig : G2) : Bool := G2.inSubgroup sig

/-- IRTF `CoreVerify`: pairing-equation check `e(P, R) · e(-PK, Q) == 1`. -/
private def coreVerify
    (pkBytes : ByteArray) (msg : ByteArray) (sigBytes : ByteArray) : Bool :=
  -- Validate pubkey (subgroup, on-curve, not infinity).
  if pkBytes.size ≠ 48 || !G1.keyValidate pkBytes then false
  else match G1.uncompress pkBytes with
  | none => false
  | some pk =>
    -- Validate signature: decompress, on-curve (implicit), in subgroup.
    if sigBytes.size ≠ 96 then false
    else match G2.uncompress sigBytes with
    | none => false
    | some sig =>
      if !signatureSubgroupCheck sig then false
      else
        let q := HashToCurve.hashToG2 msg DST
        Bls.pairingCheck #[
          (G1.generator, sig),
          (G1.neg pk, q)
        ]

/-- IRTF `FastAggregateVerify` for a single message: aggregate pubkeys
then verify. Returns `false` on invalid encodings. -/
def fastAggregateVerify
    (pubkeys : Array ByteArray) (msg : ByteArray) (sigBytes : ByteArray) : Bool := Id.run do
  if pubkeys.isEmpty then return false
  let mut agg : G1 := G1.zero
  for pk in pubkeys do
    if pk.size ≠ 48 || !G1.keyValidate pk then return false
    match G1.uncompress pk with
    | none => return false
    | some p => agg := G1.add agg p
  let aggBytes := G1.compress agg
  return coreVerify aggBytes msg sigBytes

/-! ## Ethereum wrappers -/

/-- `eth_aggregate_pubkeys` — sum compressed G1 pubkeys after `KeyValidate`.
Throws on an empty list or any invalid pubkey. -/
def ethAggregatePubkeys (pubkeys : Array ByteArray) : IO ByteArray := do
  if pubkeys.isEmpty then
    throw <| IO.userError "eth_aggregate_pubkeys: empty pubkey list"
  let mut agg : G1 := G1.zero
  for pk in pubkeys do
    if pk.size ≠ 48 then
      throw <| IO.userError "eth_aggregate_pubkeys: bad pubkey size"
    if !G1.keyValidate pk then
      throw <| IO.userError "eth_aggregate_pubkeys: invalid pubkey"
    match G1.uncompress pk with
    | none => throw <| IO.userError "eth_aggregate_pubkeys: pubkey decompression failed"
    | some p => agg := G1.add agg p
  return G1.compress agg

/-- `eth_fast_aggregate_verify` — Ethereum's special-cased FastAggregateVerify.
Returns `true` for empty pubkeys iff the signature is the G2 point at
infinity; otherwise delegates to `FastAggregateVerify`. -/
def ethFastAggregateVerify
    (pubkeys : Array ByteArray) (msg : ByteArray) (sigBytes : ByteArray) : Bool :=
  if pubkeys.isEmpty then
    sigBytes = G2_POINT_AT_INFINITY
  else
    fastAggregateVerify pubkeys msg sigBytes

end EthCryptographySpecs.Bls.Signatures
