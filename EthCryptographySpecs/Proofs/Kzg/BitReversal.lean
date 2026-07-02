import EthCryptographySpecs.Kzg.BitReversal

/-!
# Proofs: `BitReversal`

Correctness properties of `reverseBitsAux`, `reverseBits`, and
`bitReversalPermutation`.

The imperative loop in `reverseBitsAux` is first shown equal to the
structurally recursive `reverseBitsModel`, whose output bits are then
characterized via `Nat.testBit`. Everything else follows from that
characterization.
-/

namespace EthCryptographySpecs.Kzg.BitReversal

/-- Structurally recursive model of the loop inside `reverseBitsAux`.
`x` is the remaining input, `r` the accumulated (reversed) output. -/
def reverseBitsModel (x r : Nat) : Nat → Nat
  | 0 => r
  | bits + 1 => reverseBitsModel (x >>> 1) ((r <<< 1) ||| (x &&& 1)) bits

/-- The loop body of `reverseBitsAux`, folded over a list, computes
`reverseBitsModel`. Stated in the `% 2` form `simp` normalizes `&&& 1` to. -/
private theorem foldl_loop_eq_model (l : List Nat) (x r : Nat) :
    List.foldl
      (fun (s : MProd Nat Nat) (_ : Nat) =>
        ⟨(s.fst <<< 1) ||| (s.snd % 2), s.snd >>> 1⟩)
      ⟨r, x⟩ l
      = ⟨reverseBitsModel x r l.length, x >>> l.length⟩ := by
  induction l generalizing x r with
  | nil => simp [reverseBitsModel]
  | cons a l ih =>
    rw [List.foldl_cons, ih, List.length_cons, reverseBitsModel,
      Nat.and_one_is_mod, ← Nat.shiftRight_add, Nat.add_comm 1 l.length]

/-- The loop in `reverseBitsAux` computes `reverseBitsModel`. -/
theorem reverseBitsAux_eq_model (n bits : Nat) :
    reverseBitsAux n bits = reverseBitsModel n 0 bits := by
  unfold reverseBitsAux
  simp [Std.Legacy.Range.size, foldl_loop_eq_model]

/-- Bit `i` of `reverseBitsModel x r bits`: below `bits` it is the mirrored
bit of `x`; at and above `bits` it comes from the accumulator `r`. -/
theorem testBit_reverseBitsModel (bits x r i : Nat) :
    (reverseBitsModel x r bits).testBit i =
      if i < bits then x.testBit (bits - 1 - i) else r.testBit (i - bits) := by
  induction bits generalizing x r i with
  | zero => simp [reverseBitsModel]
  | succ b ih =>
    rw [reverseBitsModel, ih]
    rcases Nat.lt_trichotomy i b with h | h | h
    · rw [if_pos h, if_pos (by omega), Nat.testBit_shiftRight]
      exact congrArg x.testBit (by omega)
    · subst h
      rw [if_neg (Nat.lt_irrefl i), if_pos (Nat.lt_succ_self i),
        Nat.sub_self, show i + 1 - 1 - i = 0 by omega]
      simp
    · rw [if_neg (by omega), if_neg (by omega),
        show i - b = (i - (b + 1)) + 1 by omega]
      have hand : x &&& 1 < 2 ^ (i - (b + 1) + 1) :=
        Nat.lt_of_le_of_lt Nat.and_le_right
          (Nat.one_lt_two_pow (Nat.succ_ne_zero _))
      simp only [Nat.testBit_or, Nat.testBit_shiftLeft,
        Nat.testBit_lt_two_pow hand]
      simp [Nat.le_add_left]

/-- Bit `i` of `reverseBitsAux n bits` is bit `bits - 1 - i` of `n`
(and `false` at or above `bits`). -/
theorem testBit_reverseBitsAux (n bits i : Nat) :
    (reverseBitsAux n bits).testBit i =
      if i < bits then n.testBit (bits - 1 - i) else false := by
  rw [reverseBitsAux_eq_model, testBit_reverseBitsModel]
  simp

/-- `reverseBitsAux` stays below `2 ^ bits`. -/
theorem reverseBitsAux_lt_two_pow (n bits : Nat) :
    reverseBitsAux n bits < 2 ^ bits := by
  rcases Nat.lt_or_ge (reverseBitsAux n bits) (2 ^ bits) with h | h
  · exact h
  · obtain ⟨i, hi, hbit⟩ := Nat.exists_ge_and_testBit_of_ge_two_pow h
    rw [testBit_reverseBitsAux, if_neg (by omega)] at hbit
    exact absurd hbit Bool.false_ne_true

/-- `reverseBitsAux _ bits` is an involution on `[0, 2 ^ bits)`. -/
theorem reverseBitsAux_reverseBitsAux {n bits : Nat} (h : n < 2 ^ bits) :
    reverseBitsAux (reverseBitsAux n bits) bits = n := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_reverseBitsAux]
  by_cases hi : i < bits
  · rw [if_pos hi, testBit_reverseBitsAux, if_pos (by omega)]
    exact congrArg n.testBit (by omega)
  · rw [if_neg hi]
    exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h
      (Nat.pow_le_pow_right (by omega) (Nat.le_of_not_lt hi)))).symm

/-- Bit `i` of `reverseBits n (2 ^ k)` is bit `k - 1 - i` of `n`. -/
theorem testBit_reverseBits (n k i : Nat) :
    (reverseBits n (2 ^ k)).testBit i =
      if i < k then n.testBit (k - 1 - i) else false := by
  rw [reverseBits, Nat.log2_two_pow, testBit_reverseBitsAux]

/-- `reverseBits _ order` stays below `order` for power-of-two `order`. -/
theorem reverseBits_lt_two_pow (n k : Nat) :
    reverseBits n (2 ^ k) < 2 ^ k := by
  rw [reverseBits, Nat.log2_two_pow]
  exact reverseBitsAux_lt_two_pow n k

/-- `reverseBits _ order` is an involution on `[0, order)` for
power-of-two `order`. -/
theorem reverseBits_reverseBits {n k : Nat} (h : n < 2 ^ k) :
    reverseBits (reverseBits n (2 ^ k)) (2 ^ k) = n := by
  rw [reverseBits, reverseBits, Nat.log2_two_pow]
  exact reverseBitsAux_reverseBitsAux h

/-- `bitReversalPermutation` preserves size. -/
theorem size_bitReversalPermutation {α : Type _} [Inhabited α]
    (seq : Array α) :
    (bitReversalPermutation seq).size = seq.size := by
  simp [bitReversalPermutation]

/-- Element `i` of `bitReversalPermutation seq` is element
`reverseBits i seq.size` of `seq`. -/
theorem getElem_bitReversalPermutation {α : Type _} [Inhabited α]
    (seq : Array α) (i : Nat) (h : i < (bitReversalPermutation seq).size) :
    (bitReversalPermutation seq)[i] = seq[reverseBits i seq.size]! := by
  simp [bitReversalPermutation]

/-- `bitReversalPermutation` is an involution on arrays whose size is a
power of two, as claimed in its docstring. -/
theorem bitReversalPermutation_bitReversalPermutation {α : Type _}
    [Inhabited α] (seq : Array α) {k : Nat} (hsize : seq.size = 2 ^ k) :
    bitReversalPermutation (bitReversalPermutation seq) = seq := by
  apply Array.ext
  · rw [size_bitReversalPermutation, size_bitReversalPermutation]
  · intro i h1 h2
    have hrev : reverseBits i seq.size < seq.size := by
      rw [hsize]; exact reverseBits_lt_two_pow i k
    have hback : reverseBits (reverseBits i seq.size) seq.size = i := by
      rw [hsize]; exact reverseBits_reverseBits (hsize ▸ h2)
    rw [getElem_bitReversalPermutation _ i h1, size_bitReversalPermutation,
      getElem!_pos (bitReversalPermutation seq) (reverseBits i seq.size)
        (by rwa [size_bitReversalPermutation]),
      getElem_bitReversalPermutation seq (reverseBits i seq.size)
        (by rwa [size_bitReversalPermutation]),
      hback, getElem!_pos seq i h2]

end EthCryptographySpecs.Kzg.BitReversal
