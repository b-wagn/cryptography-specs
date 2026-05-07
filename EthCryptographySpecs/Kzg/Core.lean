import EthCryptographySpecs.Bls
import EthCryptographySpecs.Kzg.Constants
import EthCryptographySpecs.Kzg.BitReversal
import EthCryptographySpecs.Kzg.Polynomials
import EthCryptographySpecs.Kzg.TrustedSetup

/-!
# `Kzg.Core`

The blob-commitment surface of KZG. Public methods live in `IO`
because they read the loaded trusted setup; internal helpers that
only manipulate field elements remain pure.
-/

namespace EthCryptographySpecs.Kzg

open EthCryptographySpecs.Kzg.Constants
open EthCryptographySpecs.Kzg.BitReversal
open EthCryptographySpecs.Bls (G1 G2 Fr)

/-! ## Type aliases

`KZGCommitment` and `KZGProof` are `Bytes48` aliases, kept as
`ByteArray` for direct interop with public method signatures. -/

abbrev G1Point       := ByteArray
abbrev G2Point       := ByteArray
abbrev KZGCommitment := ByteArray
abbrev KZGProof      := ByteArray

/-! ## Validation -/

/-- BLS validation, allowing the point at infinity. -/
private def validateKzgG1 (b : Bytes48) : Bool :=
  if b == G1_POINT_AT_INFINITY then true
  else Bls.G1.keyValidate b

/-- Validate untrusted bytes as a `KZGCommitment`. -/
def bytesToKzgCommitment (b : Bytes48) : Option KZGCommitment :=
  if validateKzgG1 b then some b else none

/-- Validate untrusted bytes as a `KZGProof`. -/
def bytesToKzgProof (b : Bytes48) : Option KZGProof :=
  if validateKzgG1 b then some b else none

/-- Fiat-Shamir challenge for a (blob, commitment) pair. -/
def computeChallenge (blob : Blob) (commitment : KZGCommitment) : Fr :=
  let degreePoly := intToBytesBE FIELD_ELEMENTS_PER_BLOB 16
  let data := FIAT_SHAMIR_PROTOCOL_DOMAIN ++ degreePoly ++ blob ++ commitment
  hashToBlsField data

/-- BLS multi-scalar multiplication in G1, on compressed-point inputs. -/
def g1Lincomb
    (points : Array KZGCommitment) (scalars : Array Fr) : KZGCommitment :=
  if points.size = 0 then
    Bls.G1.compress Bls.G1.zero
  else
    let pointsG1 := points.map (Bls.G1.uncompress · |>.get!)
    Bls.G1.compress (Bls.G1.msm pointsG1 scalars)

/-- Given `y == p(z)`, compute `q(z)` for the KZG quotient polynomial,
handling the special case where `z` is in the roots of unity. -/
private def computeQuotientEvalWithinDomain
    (z : Fr) (polynomial : Polynomial) (y : Fr)
    : Fr := Id.run do
  let domain := rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB
  let mut result : Fr := Fr.zero
  for i in [:domain.size] do
    let omega_i := domain[i]!
    if omega_i == z then
      continue
    let f_i := polynomial[i]! - y
    let numerator := f_i * omega_i
    let denominator := z * (z - omega_i)
    result := result + (numerator / denominator)
  return result

/-- Returns the KZG proof at `z` and the evaluation `y = p(z)`. -/
private def computeKzgProofImpl
    (polynomial : Polynomial) (z : Fr) : IO (KZGProof × Fr) := do
  let setup ← TrustedSetup.get!
  let g1LagrangeBrp := bitReversalPermutation setup.g1LagrangeBytes
  let domain := rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB

  -- For all x_i, compute p(x_i) - p(z).
  let y := evaluatePolynomialInEvaluationForm polynomial z
  let polynomialShifted := polynomial.map (· - y)

  -- For all x_i, compute (x_i - z).
  let denominatorPoly := domain.map (· - z)

  -- Quotient polynomial directly in evaluation form.
  let quotient : Array Fr := Id.run do
    let mut q : Array Fr := Array.mkEmpty FIELD_ELEMENTS_PER_BLOB
    for i in [:FIELD_ELEMENTS_PER_BLOB] do
      let a := polynomialShifted[i]!
      let b := denominatorPoly[i]!
      if b.isZero then
        -- z lands on a root of unity; use the special-case formula.
        q := q.push (computeQuotientEvalWithinDomain domain[i]! polynomial y)
      else
        q := q.push (a / b)
    return q

  let proof := g1Lincomb g1LagrangeBrp quotient
  return (proof, y)

/-- Compute a KZG proof at `z` for the polynomial represented by `blob`.
Returns `(proof, y_bytes)`, where `y_bytes` is the 32-byte big-endian
encoding of `p(z)`. -/
def computeKzgProof (blob : Blob) (zBytes : Bytes32) : IO (KZGProof × Bytes32) := do
  if blob.size ≠ BYTES_PER_BLOB then
    throw <| IO.userError s!"compute_kzg_proof: bad blob size {blob.size}"
  if zBytes.size ≠ BYTES_PER_FIELD_ELEMENT then
    throw <| IO.userError s!"compute_kzg_proof: bad z size {zBytes.size}"
  let polynomial ← blobToPolynomialIO blob
  let z ← match bytesToBlsField zBytes with
          | some f => pure f
          | none   => throw <| IO.userError "compute_kzg_proof: invalid z"
  let (proof, y) ← computeKzgProofImpl polynomial z
  return (proof, blsFieldToBytes y)

/-- Verify a KZG proof that `p(z) == y`, where `p(x)` is the polynomial
committed to in `commitment`. Checks the pairing equation
`e(P - [y], -[1]) * e(proof, [s] - [z]) == 1`. -/
private def verifyKzgProofImpl
    (commitment : KZGCommitment) (z y : Fr) (proof : KZGProof)
    : IO Bool := do
  let setup ← TrustedSetup.get!
  let s := setup.g2Monomial[1]!
  let X_minus_z : G2 := Bls.G2.add s (Bls.G2.mul Bls.G2.generator (-z))
  let P_minus_y : G1 := Bls.G1.add ((Bls.G1.uncompress commitment).get!)
                                   (Bls.G1.mul Bls.G1.generator (-y))
  let pairs : Array (G1 × G2) := #[
    (P_minus_y, Bls.G2.neg Bls.G2.generator),
    ((Bls.G1.uncompress proof).get!, X_minus_z)
  ]
  return Bls.pairingCheck pairs

/-- Verify a KZG proof, taking inputs as raw bytes. -/
def verifyKzgProof
    (commitmentBytes : Bytes48) (zBytes yBytes : Bytes32) (proofBytes : Bytes48)
    : IO Bool := do
  if commitmentBytes.size ≠ BYTES_PER_COMMITMENT then
    throw <| IO.userError "verify_kzg_proof: bad commitment size"
  if zBytes.size ≠ BYTES_PER_FIELD_ELEMENT then
    throw <| IO.userError "verify_kzg_proof: bad z size"
  if yBytes.size ≠ BYTES_PER_FIELD_ELEMENT then
    throw <| IO.userError "verify_kzg_proof: bad y size"
  if proofBytes.size ≠ BYTES_PER_PROOF then
    throw <| IO.userError "verify_kzg_proof: bad proof size"
  let commitment ← match bytesToKzgCommitment commitmentBytes with
                   | some c => pure c
                   | none   => throw <| IO.userError "verify_kzg_proof: invalid commitment"
  let proof ← match bytesToKzgProof proofBytes with
              | some p => pure p
              | none   => throw <| IO.userError "verify_kzg_proof: invalid proof"
  let z ← match bytesToBlsField zBytes with
          | some f => pure f
          | none   => throw <| IO.userError "verify_kzg_proof: invalid z"
  let y ← match bytesToBlsField yBytes with
          | some f => pure f
          | none   => throw <| IO.userError "verify_kzg_proof: invalid y"
  verifyKzgProofImpl commitment z y proof

/-- Verify multiple KZG proofs efficiently using a random linear combination. -/
private def verifyKzgProofBatch
    (commitments : Array KZGCommitment)
    (zs ys : Array Fr)
    (proofs : Array KZGProof) : IO Bool := do
  if !(commitments.size = zs.size && zs.size = ys.size && ys.size = proofs.size) then
    throw <| IO.userError "verify_kzg_proof_batch: input size mismatch"
  let setup ← TrustedSetup.get!

  -- Random challenge: deterministic via Fiat-Shamir.
  let degreePoly := intToBytesBE FIELD_ELEMENTS_PER_BLOB 8
  let numCommitments := intToBytesBE commitments.size 8
  let mut data := RANDOM_CHALLENGE_KZG_BATCH_DOMAIN ++ degreePoly ++ numCommitments
  for i in [:commitments.size] do
    data := data ++ commitments[i]! ++ blsFieldToBytes zs[i]! ++ blsFieldToBytes ys[i]! ++ proofs[i]!
  let r := hashToBlsField data
  let rPowers := computePowers r commitments.size

  -- proof_lincomb = Σ_i r^i · proof_i
  let proofLincomb := g1Lincomb proofs rPowers
  -- proof_z_lincomb = Σ_i (z_i · r^i) · proof_i
  let zRPowers := Array.ofFn (n := zs.size) fun i => zs[i.val]! * rPowers[i.val]!
  let proofZLincomb := g1Lincomb proofs zRPowers

  -- C_minus_ys[i] = commitment_i - [y_i]
  let cMinusYs : Array G1 := Array.ofFn (n := commitments.size) fun i =>
    Bls.G1.add ((Bls.G1.uncompress commitments[i.val]!).get!)
               (Bls.G1.mul Bls.G1.generator (-ys[i.val]!))
  let cMinusYBytes := cMinusYs.map Bls.G1.compress
  let cMinusYLincomb := g1Lincomb cMinusYBytes rPowers

  let s := setup.g2Monomial[1]!
  let pairs : Array (G1 × G2) := #[
    ( (Bls.G1.uncompress proofLincomb).get!, Bls.G2.neg s ),
    ( Bls.G1.add ((Bls.G1.uncompress cMinusYLincomb).get!)
                 ((Bls.G1.uncompress proofZLincomb).get!)
    , Bls.G2.generator )
  ]
  return Bls.pairingCheck pairs

/-- Compute a KZG commitment from a blob. -/
def blobToKzgCommitment (blob : Blob) : IO KZGCommitment := do
  if blob.size ≠ BYTES_PER_BLOB then
    throw <| IO.userError s!"blob_to_kzg_commitment: bad blob size {blob.size}"
  let setup ← TrustedSetup.get!
  let polynomial ← blobToPolynomialIO blob
  let lagrangeBrp := bitReversalPermutation setup.g1LagrangeBytes
  return g1Lincomb lagrangeBrp polynomial

/-- Compute the KZG proof verifying `blob` against `commitment`. Does
not check that `commitment` is correct for `blob`. -/
def computeBlobKzgProof (blob : Blob) (commitmentBytes : Bytes48) : IO KZGProof := do
  if blob.size ≠ BYTES_PER_BLOB then
    throw <| IO.userError "compute_blob_kzg_proof: bad blob size"
  if commitmentBytes.size ≠ BYTES_PER_COMMITMENT then
    throw <| IO.userError "compute_blob_kzg_proof: bad commitment size"
  let commitment ← match bytesToKzgCommitment commitmentBytes with
                   | some c => pure c
                   | none   => throw <| IO.userError "compute_blob_kzg_proof: invalid commitment"
  let polynomial ← blobToPolynomialIO blob
  let evaluationChallenge := computeChallenge blob commitment
  let (proof, _) ← computeKzgProofImpl polynomial evaluationChallenge
  return proof

/-- Verify that `blob` corresponds to `commitment` via `proof`. -/
def verifyBlobKzgProof
    (blob : Blob) (commitmentBytes : Bytes48) (proofBytes : Bytes48)
    : IO Bool := do
  if blob.size ≠ BYTES_PER_BLOB then
    throw <| IO.userError "verify_blob_kzg_proof: bad blob size"
  if commitmentBytes.size ≠ BYTES_PER_COMMITMENT then
    throw <| IO.userError "verify_blob_kzg_proof: bad commitment size"
  if proofBytes.size ≠ BYTES_PER_PROOF then
    throw <| IO.userError "verify_blob_kzg_proof: bad proof size"
  let commitment ← match bytesToKzgCommitment commitmentBytes with
                   | some c => pure c
                   | none   => throw <| IO.userError "verify_blob_kzg_proof: invalid commitment"
  let polynomial ← blobToPolynomialIO blob
  let evaluationChallenge := computeChallenge blob commitment
  let y := evaluatePolynomialInEvaluationForm polynomial evaluationChallenge
  let proof ← match bytesToKzgProof proofBytes with
              | some p => pure p
              | none   => throw <| IO.userError "verify_blob_kzg_proof: invalid proof"
  verifyKzgProofImpl commitment evaluationChallenge y proof

/-- Verify a batch of (blob, commitment, proof) triples. Returns `true`
for the empty input. -/
def verifyBlobKzgProofBatch
    (blobs : Array Blob)
    (commitmentsBytes : Array Bytes48)
    (proofsBytes : Array Bytes48) : IO Bool := do
  if !(blobs.size = commitmentsBytes.size && commitmentsBytes.size = proofsBytes.size) then
    throw <| IO.userError "verify_blob_kzg_proof_batch: input size mismatch"

  let mut commitments    : Array KZGCommitment   := Array.mkEmpty blobs.size
  let mut challenges     : Array Fr := Array.mkEmpty blobs.size
  let mut ys             : Array Fr := Array.mkEmpty blobs.size
  let mut proofs         : Array KZGProof        := Array.mkEmpty blobs.size

  for i in [:blobs.size] do
    let blob := blobs[i]!
    let cb := commitmentsBytes[i]!
    let pb := proofsBytes[i]!
    if blob.size ≠ BYTES_PER_BLOB then
      throw <| IO.userError "verify_blob_kzg_proof_batch: bad blob size"
    if cb.size ≠ BYTES_PER_COMMITMENT then
      throw <| IO.userError "verify_blob_kzg_proof_batch: bad commitment size"
    if pb.size ≠ BYTES_PER_PROOF then
      throw <| IO.userError "verify_blob_kzg_proof_batch: bad proof size"

    let commitment ← match bytesToKzgCommitment cb with
                     | some c => pure c
                     | none   => throw <| IO.userError "verify_blob_kzg_proof_batch: invalid commitment"
    let proof ← match bytesToKzgProof pb with
                | some p => pure p
                | none   => throw <| IO.userError "verify_blob_kzg_proof_batch: invalid proof"

    let polynomial ← blobToPolynomialIO blob
    let challenge := computeChallenge blob commitment
    let y := evaluatePolynomialInEvaluationForm polynomial challenge

    commitments := commitments.push commitment
    challenges  := challenges.push challenge
    ys          := ys.push y
    proofs      := proofs.push proof

  verifyKzgProofBatch commitments challenges ys proofs

end EthCryptographySpecs.Kzg
