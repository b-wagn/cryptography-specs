import EthCryptographySpecs.Bls.Signatures
import EthCryptographySpecs.Bls.Errors

/-!
# `Bls.Exports`

C-ABI exports for the BLS spec functions, callable from the Python C
extension. Same conventions as the KZG exports: inputs are `ByteArray`
or `Array ByteArray`; booleans come back as `UInt8`.
-/

namespace EthCryptographySpecs.Bls.Exports

open EthCryptographySpecs.Bls.Signatures

@[export eth_bls_aggregate_pubkeys]
def ethAggregatePubkeysExport
    (pubkeys : @& Array ByteArray) : IO ByteArray :=
  runBls (ethAggregatePubkeys pubkeys)

@[export eth_bls_fast_aggregate_verify]
def ethFastAggregateVerifyExport
    (pubkeys : @& Array ByteArray) (msg : @& ByteArray) (sig : @& ByteArray)
    : IO UInt8 := do
  return if ethFastAggregateVerify pubkeys msg sig then 1 else 0

end EthCryptographySpecs.Bls.Exports
