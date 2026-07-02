import EthCryptographySpecs.Bls
import EthCryptographySpecs.Kzg.Constants
import EthCryptographySpecs.Kzg.BitReversal
import EthCryptographySpecs.Kzg.Polynomials
import EthCryptographySpecs.Kzg.Fft
import EthCryptographySpecs.Kzg.Cells
import EthCryptographySpecs.Kzg.TrustedSetup
import EthCryptographySpecs.Kzg.Errors

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
def constructVanishingPolynomial
    (missingCellIndices : Array CellIndex) : PolynomialCoeff :=
  -- Small domain: roots of unity of order CELLS_PER_EXT_BLOB.
  let rouReduced := computeRootsOfUnity CELLS_PER_EXT_BLOB

  -- Vanishing polynomial over the small domain (roots in BRP order).
  let xs : Array Fr := missingCellIndices.map fun mci =>
    rouReduced[reverseBits mci CELLS_PER_EXT_BLOB]!
  let shortZeroPoly := vanishingPolynomialcoeff xs

  -- Extend to the full domain using the closed form of the vanishing
  -- polynomial over a coset.
  (Array.range shortZeroPoly.size).foldl
    (init := Array.replicate FIELD_ELEMENTS_PER_EXT_BLOB Fr.zero)
    fun zeroPoly i =>
      zeroPoly.set! (i * FIELD_ELEMENTS_PER_CELL) shortZeroPoly[i]!

/-- Recover the coefficient-form polynomial whose evaluations on the
roots of unity reproduce the extended blob. -/
def recoverPolynomialcoeff
    (cellIndices : Array CellIndex) (cosetsEvals : Array CosetEvals)
    : PolynomialCoeff :=
  let rouExt := computeRootsOfUnity FIELD_ELEMENTS_PER_EXT_BLOB

  -- Flatten coset evaluations; missing cells contribute zeros.
  let extendedRbo : Array Fr := (Array.range cellIndices.size).foldl
    (init := Array.replicate FIELD_ELEMENTS_PER_EXT_BLOB Fr.zero)
    fun acc k =>
      let cell := cosetsEvals[k]!
      let start := cellIndices[k]! * FIELD_ELEMENTS_PER_CELL
      (Array.range FIELD_ELEMENTS_PER_CELL).foldl
        (fun acc j => acc.set! (start + j) cell[j]!) acc

  let extended := bitReversalPermutation extendedRbo

  -- Vanishing polynomial Z(x) over the missing cells.
  -- CELLS_PER_EXT_BLOB = 128; an Array.contains lookup is plenty fast.
  let missing : Array CellIndex :=
    (Array.range CELLS_PER_EXT_BLOB).filter fun ci => !cellIndices.contains ci
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

  pCoeff.extract 0 FIELD_ELEMENTS_PER_BLOB

/-- Recover all cells and proofs from any 50%+ subset of a blob's cells. -/
def recoverCellsAndKzgProofs
    (cellIndices : Array CellIndex) (cells : Array Cell)
    : KzgM (Array Cell × Array KZGProof) := do

  -- There must be an equal number of cells and indices.
  if cells.size ≠ cellIndices.size then
    throw (.inputLengthMismatch "cells" cellIndices.size cells.size)

  -- At least 50% of cells must be provided.
  if cellIndices.size < CELLS_PER_EXT_BLOB / 2 then
    throw .notEnoughCells

  -- There must not be more cells than can exist in a single blob.
  if cellIndices.size > CELLS_PER_EXT_BLOB then
    throw .tooManyCells

  -- Cell indices must be within bounds.
  if cellIndices.any (· ≥ CELLS_PER_EXT_BLOB) then
    throw .cellIndexOutOfBounds

  -- Cell indices must be strictly ascending.
  if (Array.range (cellIndices.size - 1)).any
      (fun i => cellIndices[i + 1]! ≤ cellIndices[i]!) then
    throw .indicesNotAscending

  -- Cells must be the correct size.
  if let some c := cells.find? (fun c => c.size != BYTES_PER_CELL) then
    throw (.badCellSize c.size)

  -- Convert cells to coset evaluations.
  let cosetsEvals : Array CosetEvals ← cells.mapM fun c =>
    cellToCosetEvals c

  let polyCoeff := recoverPolynomialcoeff cellIndices cosetsEvals
  computeCellsAndKzgProofsPolynomialcoeff polyCoeff

end EthCryptographySpecs.Kzg
