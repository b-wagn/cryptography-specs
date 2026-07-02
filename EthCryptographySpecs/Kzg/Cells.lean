import EthCryptographySpecs.Bls
import EthCryptographySpecs.Kzg.Constants
import EthCryptographySpecs.Kzg.BitReversal
import EthCryptographySpecs.Kzg.Polynomials
import EthCryptographySpecs.Kzg.Fft
import EthCryptographySpecs.Kzg.Core
import EthCryptographySpecs.Kzg.TrustedSetup
import EthCryptographySpecs.Kzg.Errors

/-!
# `Cells`

Cell proofs over a Reed-Solomon-extended blob. The extended
polynomial is split into `CELLS_PER_EXT_BLOB` cosets of
`FIELD_ELEMENTS_PER_CELL` evaluations each; each cell carries an
independent KZG multi-evaluation proof, so verifiers can sample any
subset of cells without downloading the full blob.
-/

namespace EthCryptographySpecs.Kzg

open EthCryptographySpecs.Kzg.Constants
open EthCryptographySpecs.Kzg.BitReversal
open EthCryptographySpecs.Bls (G1 G2 Fr)

/-! ## Type aliases -/

abbrev Cell             := ByteArray
abbrev CellIndex        := Nat
abbrev CommitmentIndex  := Nat
abbrev Coset            := Array Fr
abbrev CosetEvals       := Array Fr

/-- Convert an untrusted `Cell` into a trusted `CosetEvals`. -/
def cellToCosetEvals (cell : Cell) : Except KzgError CosetEvals := do
  if cell.size ≠ BYTES_PER_CELL then
    throw (.badCellSize cell.size)
  let mut evals : Array Fr := Array.mkEmpty FIELD_ELEMENTS_PER_CELL
  for i in [:FIELD_ELEMENTS_PER_CELL] do
    let s := i * BYTES_PER_FIELD_ELEMENT
    let e := (i + 1) * BYTES_PER_FIELD_ELEMENT
    match bytesToBlsField (cell.extract s e) with
    | .ok f    => evals := evals.push f
    | .error _ => throw (.invalidFieldElement (some i))
  return evals

/-- Convert a trusted `CosetEvals` back into an untrusted `Cell`. -/
private def cosetEvalsToCell (cosetEvals : CosetEvals) : Cell := Id.run do
  let mut bytes : ByteArray := ByteArray.empty
  for i in [:FIELD_ELEMENTS_PER_CELL] do
    bytes := bytes ++ blsFieldToBytes cosetEvals[i]!
  return bytes

/-! ## Polynomials in coefficient form -/

/-- Sum the coefficient-form polynomials `a` and `b`. -/
private def addPolynomialcoeff (a b : PolynomialCoeff) : PolynomialCoeff :=
  let (a, b) := if a.size ≥ b.size then (a, b) else (b, a)
  Array.ofFn (n := a.size) fun i =>
    let bi := if i.val < b.size then b[i.val]! else Fr.zero
    a[i.val]! + bi

/-- Multiply the coefficient-form polynomials `a` and `b`. -/
private def multiplyPolynomialcoeff (a b : PolynomialCoeff) : PolynomialCoeff := Id.run do
  -- Caller must ensure `len(a) + len(b) ≤ FIELD_ELEMENTS_PER_EXT_BLOB`.
  let mut r : PolynomialCoeff := #[Fr.zero]
  for power in [:a.size] do
    let coef := a[power]!
    let summand : PolynomialCoeff :=
      let zeros := Array.replicate power Fr.zero
      zeros ++ b.map (· * coef)
    r := addPolynomialcoeff r summand
  return r

/-- Long polynomial division for two coefficient-form polynomials. -/
private def dividePolynomialcoeff (a b : PolynomialCoeff) : PolynomialCoeff := Id.run do
  let mut a := a
  let mut o : PolynomialCoeff := Array.empty
  let mut apos : Int := (a.size : Int) - 1
  let bpos := b.size - 1
  let mut diff : Int := apos - (bpos : Int)
  -- The divisor's leading coefficient is loop-invariant; precompute its
  -- inverse once instead of paying for a full Fermat exponentiation
  -- (~570 Fp muls) on every outer iteration.
  let bLeadInv := b[bpos]!.inverse
  while diff ≥ 0 do
    let apos_n := apos.toNat
    let diff_n := diff.toNat
    let quot := a[apos_n]! * bLeadInv
    o := #[quot] ++ o
    let mut i : Int := bpos
    while i ≥ 0 do
      let i_n := i.toNat
      a := a.set! (diff_n + i_n) (a[diff_n + i_n]! - b[i_n]! * quot)
      i := i - 1
    apos := apos - 1
    diff := diff - 1
  return o

/-- Lagrange interpolation in coefficient form. Leading coefficients
may be zero. -/
private def interpolatePolynomialcoeff
    (xs ys : Array Fr) : PolynomialCoeff := Id.run do
  let mut r : PolynomialCoeff := #[Fr.zero]
  for i in [:xs.size] do
    let mut summand : PolynomialCoeff := #[ys[i]!]
    for j in [:ys.size] do
      if j ≠ i then
        let weightAdj := (xs[i]! - xs[j]!).inverse
        summand := multiplyPolynomialcoeff summand
                     #[(-weightAdj) * xs[j]!, weightAdj]
    r := addPolynomialcoeff r summand
  return r

/-- Compute the vanishing polynomial on `xs` (coefficient form). -/
def vanishingPolynomialcoeff (xs : Array Fr) : PolynomialCoeff := Id.run do
  let mut p : PolynomialCoeff := #[Fr.one]
  for x in xs do
    p := multiplyPolynomialcoeff p #[-x, Fr.one]
  return p

/-- Evaluate a coefficient-form polynomial at `z` using Horner's schema. -/
def evaluatePolynomialcoeff
    (polynomialCoeff : PolynomialCoeff) (z : Fr) : Fr := Id.run do
  let mut y : Fr := Fr.zero
  let n := polynomialCoeff.size
  for i in [:n] do
    let coef := polynomialCoeff[n - 1 - i]!
    y := y * z + coef
  return y

/-- Convert evaluation form to coefficient form via inverse FFT. -/
private def polynomialEvalToCoeff (polynomial : Polynomial) : PolynomialCoeff :=
  let roots := computeRootsOfUnity FIELD_ELEMENTS_PER_BLOB
  fftField (bitReversalPermutation polynomial) roots (inv := true)

/-! ## Cell cosets -/

/-- Shift `h` such that cell `cellIndex` is evaluated on the coset `h·G`,
where `G` is the order-`FIELD_ELEMENTS_PER_CELL` subgroup. -/
private def cosetShiftForCell (cellIndex : CellIndex) : Fr :=
  let domain := rootsOfUnityBrp FIELD_ELEMENTS_PER_EXT_BLOB
  domain[FIELD_ELEMENTS_PER_CELL * cellIndex]!

/-- The full evaluation coset for cell `cellIndex`. -/
private def cosetForCell (cellIndex : CellIndex) : Coset :=
  let domain := rootsOfUnityBrp FIELD_ELEMENTS_PER_EXT_BLOB
  let start := FIELD_ELEMENTS_PER_CELL * cellIndex
  Array.ofFn (n := FIELD_ELEMENTS_PER_CELL) fun i => domain[start + i.val]!

/-- Compute a KZG multi-evaluation proof for a set of `k` points.
For `Z(X)` the vanishing polynomial on `zs`, division gives
`f(X) = Q(X) * Z(X) + I(X)`, where the remainder `I(X)` is the
degree-`< k` interpolation polynomial through the evaluations at `zs`.
The proof commits to the quotient `Q(X)`. -/
private def computeKzgProofMultiImpl
    (polynomialCoeff : PolynomialCoeff) (zs : Coset) : KzgM (KZGProof × CosetEvals) := do
  let setup ← TrustedSetup.get!
  let ys : CosetEvals := zs.map (evaluatePolynomialcoeff polynomialCoeff)
  let denominator := vanishingPolynomialcoeff zs
  let quotient := dividePolynomialcoeff polynomialCoeff denominator
  let monomial := setup.g1MonomialBytes
  let proof := g1Lincomb (monomial.extract 0 quotient.size) quotient
  return (proof, ys)

/-- Reed-Solomon-extend `blob` and return its cells. -/
def computeCells (blob : Blob) : KzgM (Array Cell) := do
  if blob.size ≠ BYTES_PER_BLOB then
    throw (.badBlobSize blob.size)
  let polynomial ← blobToPolynomial blob
  let polynomialCoeff := polynomialEvalToCoeff polynomial
  let mut cells : Array Cell := Array.mkEmpty CELLS_PER_EXT_BLOB
  for i in [:CELLS_PER_EXT_BLOB] do
    let coset := cosetForCell i
    let ys : CosetEvals := coset.map (evaluatePolynomialcoeff polynomialCoeff)
    cells := cells.push (cosetEvalsToCell ys)
  return cells

/-- Compute cells and proofs for a polynomial in coefficient form. -/
def computeCellsAndKzgProofsPolynomialcoeff
    (polynomialCoeff : PolynomialCoeff) : KzgM (Array Cell × Array KZGProof) := do
  let mut cells  : Array Cell     := Array.mkEmpty CELLS_PER_EXT_BLOB
  let mut proofs : Array KZGProof := Array.mkEmpty CELLS_PER_EXT_BLOB
  for i in [:CELLS_PER_EXT_BLOB] do
    let coset := cosetForCell i
    let (proof, ys) ← computeKzgProofMultiImpl polynomialCoeff coset
    cells  := cells.push  (cosetEvalsToCell ys)
    proofs := proofs.push proof
  return (cells, proofs)

/-- Compute all cell proofs for an extended blob. Naive O(n²);
optimal implementations use FK20. -/
def computeCellsAndKzgProofs
    (blob : Blob) : KzgM (Array Cell × Array KZGProof) := do
  if blob.size ≠ BYTES_PER_BLOB then
    throw (.badBlobSize blob.size)
  let polynomial ← blobToPolynomial blob
  let polynomialCoeff := polynomialEvalToCoeff polynomial
  computeCellsAndKzgProofsPolynomialcoeff polynomialCoeff

/-- Random challenge `r` used in the universal verification equation. -/
def computeVerifyCellKzgProofBatchChallenge
    (commitments : Array KZGCommitment)
    (commitmentIndices : Array CommitmentIndex)
    (cellIndices : Array CellIndex)
    (cosetsEvals : Array CosetEvals)
    (proofs : Array KZGProof) : Fr := Id.run do
  let mut h := RANDOM_CHALLENGE_KZG_CELL_BATCH_DOMAIN
  h := h ++ intToBytesBE FIELD_ELEMENTS_PER_BLOB 8
  h := h ++ intToBytesBE FIELD_ELEMENTS_PER_CELL 8
  h := h ++ intToBytesBE commitments.size 8
  h := h ++ intToBytesBE cellIndices.size 8
  for c in commitments do
    h := h ++ c
  for k in [:cosetsEvals.size] do
    h := h ++ intToBytesBE commitmentIndices[k]! 8
    h := h ++ intToBytesBE cellIndices[k]! 8
    for ce in cosetsEvals[k]! do
      h := h ++ blsFieldToBytes ce
    h := h ++ proofs[k]!
  return hashToBlsField h

/-- Verify that a set of cells belong to their corresponding commitment.
The pairing equation has six accumulator terms, named LL, LR, RL, RLC,
RLI, RLP in the comments below. -/
private def verifyCellKzgProofBatchImpl
    (commitments : Array KZGCommitment)
    (commitmentIndices : Array CommitmentIndex)
    (cellIndices : Array CellIndex)
    (cosetsEvals : Array CosetEvals)
    (proofs : Array KZGProof) : KzgM Bool := do
  -- Length and bounds checks.
  if !( commitmentIndices.size = cellIndices.size
     && cellIndices.size = cosetsEvals.size
     && cosetsEvals.size = proofs.size ) then
    throw .inputLengthMismatch
  for ci in commitmentIndices do
    if ci ≥ commitments.size then
      throw .commitmentIndexOutOfBounds

  let setup ← TrustedSetup.get!
  let numCells := cellIndices.size
  let n := FIELD_ELEMENTS_PER_CELL
  let numCommitments := commitments.size

  -- Step 1: r and r^0..r^(num_cells-1).
  let r := computeVerifyCellKzgProofBatchChallenge
            commitments commitmentIndices cellIndices cosetsEvals proofs
  let rPowers := computePowers r numCells

  -- Step 2: LL = Σ_k r^k proofs[k].
  let ll : G1 := (Bls.G1.uncompress (g1Lincomb proofs rPowers)).toOption.get!

  -- Step 3: LR = [s^n].
  let lr : G2 := setup.g2Monomial[n]!

  -- Step 4.1: weights[i] = Σ_{k : commitmentIndices[k] = i} r^k.
  let mut weights : Array Fr :=
    Array.replicate numCommitments Fr.zero
  for k in [:numCells] do
    let i := commitmentIndices[k]!
    weights := weights.set! i (weights[i]! + rPowers[k]!)

  -- Step 4.1b: RLC = Σ_i weights[i] commitments[i].
  let rlc : G1 := (Bls.G1.uncompress (g1Lincomb commitments weights)).toOption.get!

  -- Step 4.2: RLI = [Σ_k r^k I_k(s)].
  let mut sumInterp : PolynomialCoeff :=
    Array.replicate n Fr.zero
  for k in [:numCells] do
    let interp := interpolatePolynomialcoeff (cosetForCell cellIndices[k]!) cosetsEvals[k]!
    let scaled := multiplyPolynomialcoeff #[rPowers[k]!] interp
    sumInterp := addPolynomialcoeff sumInterp scaled
  let rli : G1 := (Bls.G1.uncompress
                  (g1Lincomb (setup.g1MonomialBytes.extract 0 n) sumInterp)).toOption.get!

  -- Step 4.3: RLP = Σ_k (r^k * h_k^n) proofs[k].
  let mut weightedRPowers : Array Fr := Array.mkEmpty numCells
  for k in [:numCells] do
    let h_k := cosetShiftForCell cellIndices[k]!
    let h_k_pow := h_k ^ (Fr.ofNat n)
    weightedRPowers := weightedRPowers.push (rPowers[k]! * h_k_pow)
  let rlp : G1 := (Bls.G1.uncompress (g1Lincomb proofs weightedRPowers)).toOption.get!

  -- Step 4.4: RL = RLC - RLI + RLP.
  let rl : G1 := Bls.G1.add (Bls.G1.add rlc (Bls.G1.neg rli)) rlp

  -- Step 5: pairing(LL, LR) = pairing(RL, [1]).
  return Bls.pairingCheck #[
    (ll, lr),
    (rl, Bls.G2.neg setup.g2Monomial[0]!)
  ]

/-- Verify that a set of cells belong to their corresponding commitments.
Deduplicates `commitmentsBytes` and forwards into
`verifyCellKzgProofBatchImpl`. -/
def verifyCellKzgProofBatch
    (commitmentsBytes : Array Bytes48)
    (cellIndices : Array CellIndex)
    (cells : Array Cell)
    (proofsBytes : Array Bytes48) : KzgM Bool := do

  if !( commitmentsBytes.size = cells.size
     && cells.size = proofsBytes.size
     && proofsBytes.size = cellIndices.size ) then
    throw .inputLengthMismatch

  for cb in commitmentsBytes do
    if cb.size ≠ BYTES_PER_COMMITMENT then
      throw (.badCommitmentSize cb.size)
  for ci in cellIndices do
    if ci ≥ CELLS_PER_EXT_BLOB then
      throw .cellIndexOutOfBounds
  for c in cells do
    if c.size ≠ BYTES_PER_CELL then
      throw (.badCellSize c.size)
  for pb in proofsBytes do
    if pb.size ≠ BYTES_PER_PROOF then
      throw (.badProofSize pb.size)

  -- Deduplicate commitments while preserving the index of first occurrence.
  let mut deduped : Array KZGCommitment := Array.empty
  let mut commitmentIndices : Array CommitmentIndex := Array.empty
  for i in [:commitmentsBytes.size] do
    let cb := commitmentsBytes[i]!
    -- Validate (also acts as `bytes_to_kzg_commitment`).
    let _ ← match bytesToKzgCommitment cb with
            | .ok c    => pure c
            | .error _ => throw (.invalidCommitment (some i))
    -- Find or append. We use a simple linear scan; the input list of
    -- commitments tends to be short relative to the cell list.
    let mut found : Option Nat := none
    for j in [:deduped.size] do
      if deduped[j]! == cb then
        found := some j
        break
    match found with
    | some j => commitmentIndices := commitmentIndices.push j
    | none   =>
      commitmentIndices := commitmentIndices.push deduped.size
      deduped := deduped.push cb

  -- Convert cells to coset evaluations.
  let mut cosetsEvals : Array CosetEvals := Array.mkEmpty cells.size
  for c in cells do
    cosetsEvals := cosetsEvals.push (← cellToCosetEvals c)

  -- Validate proofs.
  let mut proofs : Array KZGProof := Array.mkEmpty proofsBytes.size
  for i in [:proofsBytes.size] do
    let pb := proofsBytes[i]!
    match bytesToKzgProof pb with
    | .ok p    => proofs := proofs.push p
    | .error _ => throw (.invalidProof (some i))

  verifyCellKzgProofBatchImpl deduped commitmentIndices cellIndices cosetsEvals proofs

end EthCryptographySpecs.Kzg
