import EthCryptographySpecs.Bls
import EthCryptographySpecs.Kzg.Constants
import EthCryptographySpecs.Kzg.BitReversal
import EthCryptographySpecs.Kzg.Polynomials
import EthCryptographySpecs.Kzg.Fft
import EthCryptographySpecs.Kzg.Cells
import EthCryptographySpecs.Kzg.TrustedSetup

/-!
# `Recovery`

The Reed-Solomon recovery routine for cell proofs.
-/

namespace EthCryptographySpecs.Kzg

open EthCryptographySpecs.Bls (Fr)

open EthCryptographySpecs.Kzg.Constants
open EthCryptographySpecs.Kzg.BitReversal

/-- Polynomial that vanishes at every point of every missing cell.
Assumes at least one cell is present. -/
private def constructVanishingPolynomial
    (missingCellIndices : Array CellIndex) : PolynomialCoeff := Id.run do
  -- Small domain: roots of unity of order CELLS_PER_EXT_BLOB.
  let rouReduced := computeRootsOfUnity CELLS_PER_EXT_BLOB

  -- Vanishing polynomial over the small domain (roots in BRP order).
  let xs : Array Fr := missingCellIndices.map fun mci =>
    rouReduced[reverseBits mci CELLS_PER_EXT_BLOB]!
  let shortZeroPoly := vanishingPolynomialcoeff xs

  -- Extend to the full domain using the closed form of the vanishing
  -- polynomial over a coset.
  let mut zeroPoly : PolynomialCoeff :=
    Array.replicate FIELD_ELEMENTS_PER_EXT_BLOB Fr.zero
  for i in [:shortZeroPoly.size] do
    zeroPoly := zeroPoly.set! (i * FIELD_ELEMENTS_PER_CELL) shortZeroPoly[i]!
  return zeroPoly

/-- Recover the coefficient-form polynomial whose evaluations on the
roots of unity reproduce the extended blob. -/
private def recoverPolynomialcoeff
    (cellIndices : Array CellIndex) (cosetsEvals : Array CosetEvals)
    : PolynomialCoeff := Id.run do
  let rouExt := computeRootsOfUnity FIELD_ELEMENTS_PER_EXT_BLOB

  -- Flatten coset evaluations; missing cells contribute zeros.
  let mut extendedRbo : Array Fr :=
    Array.replicate FIELD_ELEMENTS_PER_EXT_BLOB Fr.zero
  for k in [:cellIndices.size] do
    let cellIndex := cellIndices[k]!
    let cell := cosetsEvals[k]!
    let start := cellIndex * FIELD_ELEMENTS_PER_CELL
    for j in [:FIELD_ELEMENTS_PER_CELL] do
      extendedRbo := extendedRbo.set! (start + j) cell[j]!

  let extended := bitReversalPermutation extendedRbo

  -- Vanishing polynomial Z(x) over the missing cells.
  -- CELLS_PER_EXT_BLOB = 128; an Array.contains lookup is plenty fast.
  let mut missing : Array CellIndex := Array.empty
  for ci in [:CELLS_PER_EXT_BLOB] do
    if !cellIndices.contains ci then
      missing := missing.push ci
  let zeroPolyCoeff := constructVanishingPolynomial missing

  -- Z(x) in evaluation form over the FFT domain.
  let zeroPolyEval := fftField zeroPolyCoeff rouExt

  -- (E*Z)(x) in evaluation form over the FFT domain.
  let extTimesZero : Array Fr :=
    Array.ofFn (n := FIELD_ELEMENTS_PER_EXT_BLOB) fun i =>
      zeroPolyEval[i.val]! * extended[i.val]!

  -- Inverse FFT yields the coefficient form of (P*Z)(x).
  let extTimesZeroCoeffs := fftField extTimesZero rouExt (inv := true)

  -- Switch to a coset of the FFT domain so we can divide pointwise without
  -- hitting zeros.
  let pzOverCoset := cosetFftField extTimesZeroCoeffs rouExt
  let zOverCoset  := cosetFftField zeroPolyCoeff       rouExt
  let pOverCoset : Array Fr :=
    Array.ofFn (n := FIELD_ELEMENTS_PER_EXT_BLOB) fun i =>
      pzOverCoset[i.val]! / zOverCoset[i.val]!
  let pCoeff := cosetFftField pOverCoset rouExt (inv := true)

  return pCoeff.extract 0 FIELD_ELEMENTS_PER_BLOB

/-- Recover all cells and proofs from any 50%+ subset of a blob's cells. -/
def recoverCellsAndKzgProofs
    (cellIndices : Array CellIndex) (cells : Array Cell)
    : IO (Array Cell × Array KZGProof) := do
  if cellIndices.size ≠ cells.size then
    throw <| IO.userError "recover_cells_and_kzg_proofs: cell_indices/cells length mismatch"
  if !(CELLS_PER_EXT_BLOB / 2 ≤ cellIndices.size && cellIndices.size ≤ CELLS_PER_EXT_BLOB) then
    throw <| IO.userError "recover_cells_and_kzg_proofs: need 50%-100% of cells"

  -- Strictly ascending (which also implies uniqueness).
  let mut prev : Option CellIndex := none
  for ci in cellIndices do
    match prev with
    | some p => if ci ≤ p then
                  throw <| IO.userError "recover_cells_and_kzg_proofs: indices not strictly ascending"
    | none   => pure ()
    prev := some ci
    if ci ≥ CELLS_PER_EXT_BLOB then
      throw <| IO.userError "recover_cells_and_kzg_proofs: cell index out of bounds"

  for c in cells do
    if c.size ≠ BYTES_PER_CELL then
      throw <| IO.userError "recover_cells_and_kzg_proofs: bad cell size"

  -- Convert cells to coset evaluations.
  let mut cosetsEvals : Array CosetEvals := Array.mkEmpty cells.size
  for c in cells do
    match cellToCosetEvals c with
    | some evals => cosetsEvals := cosetsEvals.push evals
    | none       => throw <| IO.userError "recover_cells_and_kzg_proofs: invalid field element in cell"

  let polyCoeff := recoverPolynomialcoeff cellIndices cosetsEvals
  computeCellsAndKzgProofsPolynomialcoeff polyCoeff

end EthCryptographySpecs.Kzg
