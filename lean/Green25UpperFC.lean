import FormalConjectures.GreensOpenProblems.«25»

/-!
# Green's Open Problem 25: an improved upper bound

This file proves the `research open` theorem `Green25.green_25.upper` from
Formal Conjectures with the explicit answer `N ↦ ⌈N ^ (23 / 40)⌉`.
The main theorem `Green25.green_25` and the lower-bound question
`Green25.green_25.lower` are not claimed here.
-/

/- ## Part: `fractional_block` -/

section

/-
The analytic block estimate for Green 25, valid for any block length.
`moment n q a b` sums the q-th power of the terminal mass over all n-bit words,
using the carry transitions T₀(a,b)=(a,a+b), T₁(a,b)=(a+b,b).
The correspondence with integer sums and the final FC theorem are separate work.
-/

namespace Green25Fractional

/-- Sum of terminal mass to the power q over the full binary transition tree. -/
noncomputable def moment : ℕ → ℝ → ℝ → ℝ → ℝ
  | 0, q, a, b => (a + b) ^ q
  | n + 1, q, a, b => moment n q a (a + b) + moment n q (a + b) b

/-- This is B_L(q) in the paper, with normalized initial state (1/2,1/2). -/
noncomputable def blockCoeff (L : ℕ) (q : ℝ) : ℝ :=
  moment L q (1 / 2) (1 / 2)

theorem moment_nonneg (n : ℕ) (q a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ moment n q a b := by
  induction n generalizing a b with
  | zero => exact Real.rpow_nonneg (add_nonneg ha hb) q
  | succ n ih =>
    exact add_nonneg (ih _ _ ha (add_nonneg ha hb)) (ih _ _ (add_nonneg ha hb) hb)

theorem moment_swap (n : ℕ) (q a b : ℝ) : moment n q a b = moment n q b a := by
  induction n generalizing a b with
  | zero => simp [moment, add_comm]
  | succ n ih =>
    simp only [moment]
    rw [ih a (a + b), ih (a + b) b]
    simp [add_comm]

theorem moment_scale (n : ℕ) (q c a b : ℝ)
    (hc : 0 ≤ c) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    moment n q (c * a) (c * b) = c ^ q * moment n q a b := by
  induction n generalizing a b with
  | zero =>
    simp only [moment, ← mul_add]
    exact Real.mul_rpow hc (add_nonneg ha hb)
  | succ n ih =>
    simp only [moment, ← mul_add]
    rw [ih a (a + b) ha (add_nonneg ha hb), ih (a + b) b (add_nonneg ha hb) hb]
    ring

/-- Midpoint concavity on the nonnegative quadrant, proved by induction on the tree. -/
theorem moment_midpoint (n : ℕ) (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1)
    (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    (moment n q a b + moment n q c d) / 2 ≤
      moment n q ((a + c) / 2) ((b + d) / 2) := by
  induction n generalizing a b c d with
  | zero =>
    have h := (Real.concaveOn_rpow hq₀ hq₁).2
      (show a + b ∈ Set.Ici (0 : ℝ) from add_nonneg ha hb)
      (show c + d ∈ Set.Ici (0 : ℝ) from add_nonneg hc hd)
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
    simp only [smul_eq_mul] at h
    dsimp only [moment]
    convert h using 1 <;> congr 1 <;> ring
  | succ n ih =>
    have h₀ := ih a (a + b) c (c + d) ha (add_nonneg ha hb) hc (add_nonneg hc hd)
    have h₁ := ih (a + b) b (c + d) d (add_nonneg ha hb) hb (add_nonneg hc hd) hd
    dsimp only [moment]
    rw [show (a + c) / 2 + (b + d) / 2 = ((a + b) + (c + d)) / 2 by ring]
    linarith

/-- The central block inequality: the balanced input maximizes the fractional moment
among all nonnegative states of fixed total mass. No symmetry is assumed as a hypothesis. -/
theorem block_bound (L : ℕ) (q a b : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    moment L q a b ≤ blockCoeff L q * (a + b) ^ q := by
  have h := moment_midpoint L q hq₀ hq₁ a b b a ha hb hb ha
  rw [moment_swap L q b a] at h
  have heq : moment L q ((a + b) / 2) ((a + b) / 2) =
      blockCoeff L q * (a + b) ^ q := by
    have hs := moment_scale L q (a + b) (1 / 2) (1 / 2)
      (add_nonneg ha hb) (by norm_num) (by norm_num)
    simpa [blockCoeff, div_eq_mul_inv, mul_comm] using hs
  rw [add_comm b a] at h
  linarith

/-- Applying the block estimate at all leaves of a prefix. -/
theorem moment_add_le (n L : ℕ) (q a b : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    moment (n + L) q a b ≤ blockCoeff L q * moment n q a b := by
  induction n generalizing a b with
  | zero => simpa [moment] using block_bound L q a b hq₀ hq₁ ha hb
  | succ n ih =>
    simp only [Nat.succ_add, moment]
    have h₀ := ih a (a + b) ha (add_nonneg ha hb)
    have h₁ := ih (a + b) b (add_nonneg ha hb) hb
    nlinarith

/-- The block estimate iterates for arbitrarily many blocks. -/
theorem iterated_block_bound (L k : ℕ) (q a b : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    moment (L * k) q a b ≤ blockCoeff L q ^ k * (a + b) ^ q := by
  have hB : 0 ≤ blockCoeff L q := moment_nonneg L q _ _ (by norm_num) (by norm_num)
  induction k with
  | zero => simp [moment]
  | succ k ih =>
    rw [Nat.mul_succ]
    calc
      moment (L * k + L) q a b ≤ blockCoeff L q * moment (L * k) q a b :=
        moment_add_le _ _ _ _ _ hq₀ hq₁ ha hb
      _ ≤ blockCoeff L q * (blockCoeff L q ^ k * (a + b) ^ q) :=
        mul_le_mul_of_nonneg_left ih hB
      _ = blockCoeff L q ^ (k + 1) * (a + b) ^ q := by ring

/-- The one-bit coefficient, used for a final incomplete block. -/
theorem blockCoeff_one (q : ℝ) : blockCoeff 1 q = 2 * (3 / 2 : ℝ) ^ q := by
  norm_num [blockCoeff, moment]
  ring

/-- The full bound, including a remainder of r bits. -/
theorem block_bound_with_remainder (L k r : ℕ) (q a b : ℝ)
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    moment (L * k + r) q a b ≤
      blockCoeff L q ^ k * (2 * (3 / 2 : ℝ) ^ q) ^ r * (a + b) ^ q := by
  have hr := iterated_block_bound 1 r q (1 / 2) (1 / 2) hq₀ hq₁
    (by norm_num) (by norm_num)
  have hBr : blockCoeff r q ≤ (2 * (3 / 2 : ℝ) ^ q) ^ r := by
    simpa only [Nat.one_mul, blockCoeff_one, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num,
      Real.one_rpow, mul_one] using hr
  have hR : 0 ≤ (2 * (3 / 2 : ℝ) ^ q) ^ r := by positivity
  calc
    moment (L * k + r) q a b ≤ blockCoeff r q * moment (L * k) q a b :=
      moment_add_le _ _ _ _ _ hq₀ hq₁ ha hb
    _ ≤ (2 * (3 / 2 : ℝ) ^ q) ^ r * moment (L * k) q a b :=
      mul_le_mul_of_nonneg_right hBr (moment_nonneg _ _ _ _ ha hb)
    _ ≤ (2 * (3 / 2 : ℝ) ^ q) ^ r * (blockCoeff L q ^ k * (a + b) ^ q) :=
      mul_le_mul_of_nonneg_left (iterated_block_bound L k q a b hq₀ hq₁ ha hb) hR
    _ = _ := by ring

/-- The two final carry states contribute at most a fixed factor times their total mass. -/
theorem terminal_pair_bound (q a b : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ q + b ^ q ≤ (2 : ℝ) ^ (1 - q) * (a + b) ^ q := by
  have h := (Real.concaveOn_rpow hq₀ hq₁).2
    (show a ∈ Set.Ici (0 : ℝ) from ha) (show b ∈ Set.Ici (0 : ℝ) from hb)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  simp only [smul_eq_mul] at h
  have hmid : a ^ q + b ^ q ≤ 2 * ((a + b) / 2) ^ q := by
    have heq : (1 / 2 : ℝ) * a + (1 / 2 : ℝ) * b = (a + b) / 2 := by ring
    rw [heq] at h
    linarith
  calc
    _ ≤ 2 * ((a + b) / 2) ^ q := hmid
    _ = (2 : ℝ) ^ (1 - q) * (a + b) ^ q := by
      rw [Real.div_rpow (add_nonneg ha hb) (by norm_num),
        Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
      ring

end Green25Fractional

end

/- ## Part: `fractional_xor` -/

section

/-
The discrete XOR layer for the Green 25 fractional-moment construction.

We model a number below `2^d` by its `d` Boolean bits.  If `c` is an XOR
difference and `x` is one endpoint, the digitwise sum of `x` and `x xor c`
has digits in `{0,1,2}`.  A digit is `1` exactly at a set bit of `c`; hence
different XOR differences give different ternary words.  This supplies the
cardinality bound needed by the union bound without counting endpoint pairs.
-/

namespace Green25Fractional

/-- A `d`-bit word, with the least significant coordinate indexed by `0`. -/
abbrev BitWord (d : ℕ) := Fin d → Bool

def zeroBitWord (d : ℕ) : BitWord d := fun _ => false

/-- Regard a Boolean bit as a natural number. -/
def bitNat (b : Bool) : ℕ := if b then 1 else 0

/-- Pointwise XOR of two finite words. -/
def xorWord {d : ℕ} (x c : BitWord d) : BitWord d :=
  fun i => xor (x i) (c i)

/-- The natural number represented by a finite binary word. -/
def binaryValue {d : ℕ} (x : BitWord d) : ℕ :=
  ∑ i, bitNat (x i) * 2 ^ (i : ℕ)

/-- The coordinatewise integer sum of `x` and `x xor c`, as digits in `Fin 3`. -/
def sumDigits {d : ℕ} (x c : BitWord d) : Fin d → Fin 3 :=
  fun i => ⟨bitNat (x i) + bitNat (xorWord x c i), by
    have hx : bitNat (x i) ≤ 1 := by cases x i <;> simp [bitNat]
    have hy : bitNat (xorWord x c i) ≤ 1 := by
      cases xorWord x c i <;> simp [bitNat]
    omega⟩

/-- Evaluation of a word with digits `0`, `1`, or `2` in base two. -/
def ternaryValue {d : ℕ} (z : Fin d → Fin 3) : ℕ :=
  ∑ i, (z i : ℕ) * 2 ^ (i : ℕ)

/-- XOR differences capable of producing the integer sum `s`. -/
def CapableDifference (d s : ℕ) :=
  {c : BitWord d // ∃ x : BitWord d, binaryValue x + binaryValue (xorWord x c) = s}

/-- Relevant differences for distinct endpoint pairs. -/
def NonzeroCapableDifference (d s : ℕ) :=
  {c : BitWord d // c ≠ zeroBitWord d ∧
    ∃ x : BitWord d, binaryValue x + binaryValue (xorWord x c) = s}

/-- Three-valued base-two representations of the integer `s`. -/
def TernaryRepresentation (d s : ℕ) :=
  {z : Fin d → Fin 3 // ternaryValue z = s}

noncomputable instance capableDifferenceFintype (d s : ℕ) :
    Fintype (CapableDifference d s) := by
  classical
  unfold CapableDifference
  infer_instance

noncomputable instance nonzeroCapableDifferenceFintype (d s : ℕ) :
    Fintype (NonzeroCapableDifference d s) := by
  classical
  unfold NonzeroCapableDifference
  infer_instance

noncomputable instance ternaryRepresentationFintype (d s : ℕ) :
    Fintype (TernaryRepresentation d s) := by
  classical
  unfold TernaryRepresentation
  infer_instance

/-- Digitwise addition evaluates to ordinary addition of the two binary words. -/
theorem ternaryValue_sumDigits {d : ℕ} (x c : BitWord d) :
    ternaryValue (sumDigits x c) =
      binaryValue x + binaryValue (xorWord x c) := by
  simp only [ternaryValue, sumDigits, binaryValue]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Nat.add_mul]

/-- The sum digit is `1` precisely at a set bit of the XOR difference. -/
theorem sumDigits_eq_one_iff {d : ℕ} (x c : BitWord d) (i : Fin d) :
    (sumDigits x c i : ℕ) = 1 ↔ c i = true := by
  cases hx : x i <;> cases hc : c i <;>
    simp [sumDigits, xorWord, bitNat, hx, hc]

/-- The digitwise sum remembers the XOR difference, even though it forgets
which endpoint supplied the `1` at a differing coordinate. -/
theorem xor_eq_of_sumDigits_eq {d : ℕ} {x y c e : BitWord d}
    (h : sumDigits x c = sumDigits y e) : c = e := by
  funext i
  have hi : (sumDigits x c i : ℕ) = (sumDigits y e i : ℕ) := by
    exact congrArg Fin.val (congrFun h i)
  have htrue : c i = true ↔ e i = true := by
    rw [← sumDigits_eq_one_iff x c i, ← sumDigits_eq_one_iff y e i, hi]
  cases hc : c i <;> cases he : e i <;> simp_all

/-- Choose one endpoint witnessing that a difference can produce `s`. -/
noncomputable def capableWitness {d s : ℕ} (c : CapableDifference d s) : BitWord d :=
  Classical.choose c.property

/-- Send a capable XOR difference to its three-valued digit representation. -/
noncomputable def capableToRepresentation {d s : ℕ} (c : CapableDifference d s) :
    TernaryRepresentation d s :=
  ⟨sumDigits (capableWitness c) c.1, by
    rw [ternaryValue_sumDigits]
    exact Classical.choose_spec c.property⟩

/-- Distinct XOR differences map to distinct three-valued representations. -/
theorem capableToRepresentation_injective {d s : ℕ} :
    Function.Injective (capableToRepresentation :
      CapableDifference d s → TernaryRepresentation d s) := by
  intro c e h
  apply Subtype.ext
  exact xor_eq_of_sumDigits_eq (congrArg Subtype.val h)

/-- The number of relevant XOR differences is at most the number `h_d(s)` of
three-valued base-two representations.  This is the precise estimate used by
the probabilistic union bound. -/
theorem capable_card_le_representation_card (d s : ℕ) :
    Nat.card (CapableDifference d s) ≤
      Nat.card (TernaryRepresentation d s) :=
  Nat.card_le_card_of_injective capableToRepresentation
    capableToRepresentation_injective

def nonzeroCapableToCapable {d s : ℕ} (c : NonzeroCapableDifference d s) :
    CapableDifference d s := ⟨c.1, c.2.2⟩

theorem nonzeroCapableToCapable_injective {d s : ℕ} :
    Function.Injective (nonzeroCapableToCapable :
      NonzeroCapableDifference d s → CapableDifference d s) := by
  intro c e h
  exact Subtype.ext (congrArg (fun z : CapableDifference d s => z.1) h)

theorem nonzero_capable_card_le_representation_card (d s : ℕ) :
    Nat.card (NonzeroCapableDifference d s) ≤
      Nat.card (TernaryRepresentation d s) :=
  (Nat.card_le_card_of_injective nonzeroCapableToCapable
    nonzeroCapableToCapable_injective).trans
      (capable_card_le_representation_card d s)

/-- Notation-level definition of the multiplicity `h_d(s)`. -/
noncomputable def representationCount (d s : ℕ) : ℕ :=
  Nat.card (TernaryRepresentation d s)

theorem capable_card_le_representationCount (d s : ℕ) :
    Nat.card (CapableDifference d s) ≤ representationCount d s :=
  capable_card_le_representation_card d s

end Green25Fractional

end

/- ## Part: `fractional_carry` -/

section

/-
The two-state carry recurrence for the three-valued base-two representations.

After a fixed string of low output bits has been read, `(a,b)` records the
numbers of digit prefixes with carry `0` and carry `1`.  Reading the next
output bit applies one of

* `T₀(a,b) = (a,a+b)`,
* `T₁(a,b) = (a+b,b)`.

The two entries at a leaf are the multiplicities for the two possible final
carry bits.  This file proves the fractional terminal sum is controlled by
the `moment` already used in the finite `B₈` certificate.
-/

namespace Green25Fractional

/-- All terminal carry states after `n` output bits, retaining multiplicity. -/
def carryLeaves : ℕ → ℕ → ℕ → List (ℕ × ℕ)
  | 0, a, b => [(a, b)]
  | n + 1, a, b => carryLeaves n a (a + b) ++ carryLeaves n (a + b) b

/-- Fractional sum over both final carries at every leaf. -/
noncomputable def terminalMoment : ℕ → ℝ → ℝ → ℝ → ℝ
  | 0, q, a, b => a ^ q + b ^ q
  | n + 1, q, a, b =>
      terminalMoment n q a (a + b) + terminalMoment n q (a + b) b

theorem carryLeaves_length (n a b : ℕ) :
    (carryLeaves n a b).length = 2 ^ n := by
  induction n generalizing a b with
  | zero => simp [carryLeaves]
  | succ n ih =>
      simp only [carryLeaves, List.length_append, ih, pow_succ]
      omega

/-- The recursive real expression is exactly the sum over the integer carry
states.  Thus no analytic recurrence is being assumed independently of the
finite counting tree. -/
theorem terminalMoment_eq_carryLeaves (n a b : ℕ) (q : ℝ) :
    terminalMoment n q a b =
      ((carryLeaves n a b).map
        (fun p : ℕ × ℕ => (p.1 : ℝ) ^ q + (p.2 : ℝ) ^ q)).sum := by
  induction n generalizing a b with
  | zero => simp [terminalMoment, carryLeaves]
  | succ n ih =>
      simp only [terminalMoment, carryLeaves, List.map_append, List.sum_append]
      simpa only [Nat.cast_add] using
        congrArg₂ (fun u v : ℝ => u + v) (ih a (a + b)) (ih (a + b) b)

/-- At every depth, replacing the two final carry multiplicities by their sum
costs only the factor `2^(1-q)`. -/
theorem terminalMoment_le_moment (n : ℕ) (q a b : ℝ)
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    terminalMoment n q a b ≤ (2 : ℝ) ^ (1 - q) * moment n q a b := by
  induction n generalizing a b with
  | zero => simpa [terminalMoment, moment] using terminal_pair_bound q a b hq₀ hq₁ ha hb
  | succ n ih =>
      have h₀ := ih a (a + b) ha (add_nonneg ha hb)
      have h₁ := ih (a + b) b (add_nonneg ha hb) hb
      simp only [terminalMoment, moment]
      linarith

/-- Block iteration plus the terminal-carry factor.  This is the analytic
bound that will be applied to the representation-count histogram. -/
theorem terminalMoment_block_bound (L k r : ℕ) (q a b : ℝ)
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    terminalMoment (L * k + r) q a b ≤
      (2 : ℝ) ^ (1 - q) * blockCoeff L q ^ k *
        (2 * (3 / 2 : ℝ) ^ q) ^ r * (a + b) ^ q := by
  have ht := terminalMoment_le_moment (L * k + r) q a b hq₀ hq₁ ha hb
  have hm := block_bound_with_remainder L k r q a b hq₀ hq₁ ha hb
  have hc : 0 ≤ (2 : ℝ) ^ (1 - q) := Real.rpow_nonneg (by norm_num) _
  calc
    terminalMoment (L * k + r) q a b
        ≤ (2 : ℝ) ^ (1 - q) * moment (L * k + r) q a b := ht
    _ ≤ (2 : ℝ) ^ (1 - q) *
          (blockCoeff L q ^ k * (2 * (3 / 2 : ℝ) ^ q) ^ r * (a + b) ^ q) :=
      mul_le_mul_of_nonneg_left hm hc
    _ = _ := by ring

/-- The concrete initial carry state for three-valued digits. -/
theorem representation_terminal_bound (L k r : ℕ) (q : ℝ)
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    terminalMoment (L * k + r) q 1 0 ≤
      (2 : ℝ) ^ (1 - q) * blockCoeff L q ^ k *
        (2 * (3 / 2 : ℝ) ^ q) ^ r := by
  simpa using terminalMoment_block_bound L k r q 1 0 hq₀ hq₁ (by norm_num) (by norm_num)

end Green25Fractional

end

/- ## Part: `fractional_matrix` -/

section

/-
Finite averaging for the random binary linear coloring in Green 25.

The sample space is the finite type of all linear maps
`(Fin d → ZMod 2) →ₗ (Fin t → ZMod 2)`.  Evaluation at a nonzero
difference is surjective.  Rank-nullity in cardinal form therefore says that
exactly a `2^(-t)` fraction of the maps annihilate that difference.
-/

namespace Green25Fractional

abbrev F2 := ZMod 2
abbrev F2Word (d : ℕ) := Fin d → F2
abbrev LinearColoring (d t : ℕ) := F2Word d →ₗ[F2] F2Word t

/-- The coordinate embedding of Boolean words into the vector space over `F₂`. -/
def boolToF2Word {d : ℕ} (x : BitWord d) : F2Word d :=
  fun i => if x i then 1 else 0

theorem boolToF2Word_injective {d : ℕ} :
    Function.Injective (boolToF2Word : BitWord d → F2Word d) := by
  intro x y h
  funext i
  have hi := congrFun h i
  cases hx : x i <;> cases hy : y i <;> simp_all [boolToF2Word]

/-- Boolean XOR becomes vector addition over `F₂`. -/
theorem boolToF2Word_xor {d : ℕ} (x c : BitWord d) :
    boolToF2Word (xorWord x c) = boolToF2Word x + boolToF2Word c := by
  ext i
  cases hx : x i <;> cases hc : c i <;>
    simp [boolToF2Word, xorWord, hx, hc]
  decide

theorem boolToF2Word_zero (d : ℕ) :
    boolToF2Word (zeroBitWord d) = 0 := by
  ext i
  simp [boolToF2Word, zeroBitWord]

theorem boolToF2Word_ne_zero {d : ℕ} {c : BitWord d}
    (hc : c ≠ zeroBitWord d) : boolToF2Word c ≠ 0 := by
  intro h
  apply hc
  apply boolToF2Word_injective
  simpa [boolToF2Word_zero] using h

/-- Evaluation of a linear coloring at a fixed difference, itself as a linear map. -/
def evalColoringAt {d t : ℕ} (c : F2Word d) :
    LinearColoring d t →ₗ[F2] F2Word t where
  toFun H := H c
  map_add' H G := by ext; simp
  map_smul' a H := by ext; simp

/-- Evaluation at a nonzero input is onto: a rank-one map realizes any target. -/
theorem evalColoringAt_surjective {d t : ℕ} {c : F2Word d} (hc : c ≠ 0) :
    Function.Surjective (evalColoringAt (t := t) c) := by
  have hex : ∃ i : Fin d, c i ≠ 0 := by
    by_contra h
    push_neg at h
    apply hc
    funext i
    exact h i
  obtain ⟨i, hi⟩ := hex
  intro y
  refine ⟨(LinearMap.proj i).smulRight ((c i)⁻¹ • y), ?_⟩
  ext j
  simp [evalColoringAt, LinearMap.smulRight_apply, hi]

/-- Linear-map colorings identify `x` and `x+c` exactly when they annihilate `c`. -/
theorem add_same_color_iff {d t : ℕ} (H : LinearColoring d t) (x c : F2Word d) :
    H (x + c) = H x ↔ H c = 0 := by
  rw [H.map_add]
  simp

/-- Collision of two Boolean endpoints depends only on their XOR difference. -/
theorem xor_same_color_iff {d t : ℕ} (H : LinearColoring d t)
    (x c : BitWord d) :
    H (boolToF2Word (xorWord x c)) = H (boolToF2Word x) ↔
      H (boolToF2Word c) = 0 := by
  rw [boolToF2Word_xor]
  exact add_same_color_iff H _ _

/-- The finite set/type of colorings that annihilate one difference. -/
def AnnihilatingColoring (d t : ℕ) (c : F2Word d) :=
  {H : LinearColoring d t // H c = 0}

noncomputable instance linearColoringFintype (d t : ℕ) :
    Fintype (LinearColoring d t) :=
  Fintype.ofInjective
    (fun H : LinearColoring d t => (H : F2Word d → F2Word t))
    LinearMap.coe_injective

noncomputable instance annihilatingColoringFintype (d t : ℕ) (c : F2Word d) :
    Fintype (AnnihilatingColoring d t c) := by
  classical
  unfold AnnihilatingColoring
  infer_instance

noncomputable def annihilatingEquivKer {d t : ℕ} (c : F2Word d) :
    AnnihilatingColoring d t c ≃ LinearMap.ker (evalColoringAt (t := t) c) where
  toFun H := ⟨H.1, H.2⟩
  invFun H := ⟨H.1, H.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem f2Word_card (t : ℕ) : Nat.card (F2Word t) = 2 ^ t := by
  rw [Nat.card_eq_fintype_card]
  simp [F2Word, F2]

/-- Exact collision count for every nonzero difference.  This is the finite
probability `Pr[Hc=0]=1/2^t`, stated without a measure or division. -/
theorem annihilating_card_mul {d t : ℕ} {c : F2Word d} (hc : c ≠ 0) :
    Nat.card (AnnihilatingColoring d t c) * 2 ^ t =
      Nat.card (LinearColoring d t) := by
  let E := evalColoringAt (t := t) c
  have hsurj : Function.Surjective E := evalColoringAt_surjective hc
  have hquot : Nat.card (LinearColoring d t ⧸ LinearMap.ker E) = Nat.card (F2Word t) :=
    Nat.card_congr (E.quotKerEquivOfSurjective hsurj).toEquiv
  have hcard := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker E)
  calc
    Nat.card (AnnihilatingColoring d t c) * 2 ^ t =
        Nat.card (LinearMap.ker E) * Nat.card (F2Word t) := by
      rw [Nat.card_congr (annihilatingEquivKer (t := t) c), f2Word_card]
    _ = Nat.card (LinearMap.ker E) *
        Nat.card (LinearColoring d t ⧸ LinearMap.ker E) := by rw [hquot]
    _ = Nat.card (LinearColoring d t) := hcard.symm

noncomputable def annihilatingFinset {d t : ℕ} (c : F2Word d) :
    Finset (LinearColoring d t) := by
  classical
  exact Finset.univ.filter fun H => H c = 0

theorem annihilatingFinset_card {d t : ℕ} {c : F2Word d} (hc : c ≠ 0) :
    (annihilatingFinset (t := t) c).card * 2 ^ t =
      Fintype.card (LinearColoring d t) := by
  have h := annihilating_card_mul (t := t) hc
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
  change Fintype.card {H : LinearColoring d t // H c = 0} * 2 ^ t =
    Fintype.card (LinearColoring d t) at h
  rw [Fintype.card_subtype (fun H : LinearColoring d t => H c = 0)] at h
  simpa [annihilatingFinset] using h

/-- Colorings for which some nonzero difference capable of the sum `s`
collapses to zero. -/
noncomputable def badForSumFinset (d t s : ℕ) : Finset (LinearColoring d t) :=
  by
    classical
    exact Finset.univ.biUnion fun c : NonzeroCapableDifference d s =>
      annihilatingFinset (t := t) (boolToF2Word c.1)

/-- Integer-form union bound for one sum.  Combining this with
`nonzero_capable_card_le_representation_card` gives the numerator
`h_d(s)` used in the fractional-moment estimate. -/
theorem badForSum_card_mul_le (d t s : ℕ) :
    (badForSumFinset d t s).card * 2 ^ t ≤
      representationCount d s * Fintype.card (LinearColoring d t) := by
  classical
  calc
    (badForSumFinset d t s).card * 2 ^ t ≤
        (∑ c : NonzeroCapableDifference d s,
          (annihilatingFinset (t := t) (boolToF2Word c.1)).card) * 2 ^ t :=
      Nat.mul_le_mul_right _ (by
        simpa [badForSumFinset] using
          (Finset.card_biUnion_le (s := Finset.univ)
            (t := fun c : NonzeroCapableDifference d s =>
              annihilatingFinset (t := t) (boolToF2Word c.1))))
    _ = ∑ c : NonzeroCapableDifference d s,
          (annihilatingFinset (t := t) (boolToF2Word c.1)).card * 2 ^ t := by
      rw [Finset.sum_mul]
    _ = ∑ _c : NonzeroCapableDifference d s,
          Fintype.card (LinearColoring d t) := by
      apply Finset.sum_congr rfl
      intro c _
      exact annihilatingFinset_card (boolToF2Word_ne_zero c.2.1)
    _ = Fintype.card (NonzeroCapableDifference d s) *
          Fintype.card (LinearColoring d t) := by simp
    _ ≤ representationCount d s * Fintype.card (LinearColoring d t) := by
      apply Nat.mul_le_mul_right
      simpa [representationCount, Nat.card_eq_fintype_card] using
        nonzero_capable_card_le_representation_card d s

end Green25Fractional

end

/- ## Part: `fractional_average` -/

section

/-
The finite averaging step, separated from the analytic estimate.

Rows are colorings and columns are candidate integer sums.  Double counting
the incidence relation shows that if the total number of bad incidences is
less than `B * |Omega|`, some coloring has fewer than `B` bad sums.
-/

namespace Green25Fractional

/-- The `0/1` expansion of the cardinality of a filtered finite universe. -/
theorem card_filter_eq_sum_ite {A : Type*} [Fintype A] (p : A → Prop)
    [DecidablePred p] :
    (Finset.univ.filter p).card = ∑ a : A, if p a then 1 else 0 := by
  classical
  rw [Finset.card_eq_sum_ones]
  simp

/-- Swap the two ways of counting a finite incidence relation. -/
theorem sum_column_card_eq_sum_row_card {A S : Type*} [Fintype A] [Fintype S]
    (bad : A → S → Prop) [DecidableRel bad] :
    (∑ s : S, (Finset.univ.filter fun a : A => bad a s).card) =
      ∑ a : A, (Finset.univ.filter fun s : S => bad a s).card := by
  classical
  simp_rw [card_filter_eq_sum_ite]
  rw [Finset.sum_comm]

/-- Strict finite averaging in natural-number form. -/
theorem exists_row_card_lt_of_sum_column_card_lt
    {A S : Type*} [Fintype A] [Fintype S] [Nonempty A]
    (bad : A → S → Prop) [DecidableRel bad] (B : ℕ)
    (hbad : (∑ s : S, (Finset.univ.filter fun a : A => bad a s).card) <
      B * Fintype.card A) :
    ∃ a : A, (Finset.univ.filter fun s : S => bad a s).card < B := by
  classical
  by_contra h
  push_neg at h
  have hlower : B * Fintype.card A ≤
      ∑ a : A, (Finset.univ.filter fun s : S => bad a s).card := by
    calc
      B * Fintype.card A = ∑ _a : A, B := by simp [mul_comm]
      _ ≤ ∑ a : A, (Finset.univ.filter fun s : S => bad a s).card :=
        Finset.sum_le_sum fun a _ => h a
  rw [← sum_column_card_eq_sum_row_card bad] at hlower
  omega

/-- Candidate sums for `d` input bits include the zero coefficient above the
largest possible value; retaining it makes the range a power of two. -/
abbrev CandidateSum (d : ℕ) := Fin (2 ^ (d + 1))

/-- Number of candidate sums made bad by one linear coloring. -/
noncomputable def badSumCount (d t : ℕ) (H : LinearColoring d t) : ℕ :=
  Nat.card {s : CandidateSum d // H ∈ badForSumFinset d t s}

/-- Once an aggregate incidence estimate is supplied, a single coloring with
the desired number of bad sums exists. -/
theorem exists_coloring_with_few_bad_sums (d t B : ℕ)
    (hbad : (∑ s : CandidateSum d, (badForSumFinset d t s).card) <
      B * Fintype.card (LinearColoring d t)) :
    ∃ H : LinearColoring d t, badSumCount d t H < B := by
  classical
  let bad : LinearColoring d t → CandidateSum d → Prop :=
    fun H s => H ∈ badForSumFinset d t s
  letI : DecidableRel bad := fun _ _ => Classical.propDecidable _
  have hcols :
      (∑ s : CandidateSum d,
        (Finset.univ.filter fun H : LinearColoring d t => bad H s).card) =
      ∑ s : CandidateSum d, (badForSumFinset d t s).card := by
    apply Finset.sum_congr rfl
    intro s _
    congr 1
    ext H
    simp [bad]
  obtain ⟨H, hH⟩ := exists_row_card_lt_of_sum_column_card_lt bad B (by
    rw [hcols]
    exact hbad)
  refine ⟨H, ?_⟩
  rw [badSumCount, Nat.card_eq_fintype_card,
    Fintype.card_subtype (fun s : CandidateSum d => H ∈ badForSumFinset d t s)]
  convert hH using 1

end Green25Fractional

end

/- ## Part: `fractional_probability` -/

section

/-
The fractional-power conversion used after the finite union bound.
-/

namespace Green25Fractional

/-- For `0 ≤ q ≤ 1`, the fractional power dominates both branches needed
in `min(1,x)`. -/
theorem min_one_le_rpow (x q : ℝ) (hx : 0 ≤ x) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    min 1 x ≤ x ^ q := by
  by_cases hx₁ : x ≤ 1
  · rw [min_eq_right hx₁]
    exact Real.self_le_rpow_of_le_one hx hx₁ hq₁
  · rw [min_eq_left (le_of_not_ge hx₁)]
    exact Real.one_le_rpow (le_of_not_ge hx₁) hq₀

/-- Convert an integer union bound into the fractional probability estimate. -/
theorem fractional_ratio_bound (bad h total K : ℕ) (q : ℝ)
    (htotal : 0 < total) (hK : 0 < K) (hbad : bad ≤ total)
    (hunion : bad * K ≤ h * total) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    (bad : ℝ) / total ≤ ((h : ℝ) / K) ^ q := by
  have htotalR : (0 : ℝ) < total := by exact_mod_cast htotal
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hbadR : (bad : ℝ) ≤ total := by exact_mod_cast hbad
  have hunionR : (bad : ℝ) * K ≤ h * total := by exact_mod_cast hunion
  have hone : (bad : ℝ) / total ≤ 1 := (div_le_one htotalR).2 hbadR
  have hratio : (bad : ℝ) / total ≤ (h : ℝ) / K := by
    exact (div_le_div_iff₀ htotalR hKR).2 hunionR
  exact (le_min hone hratio).trans
    (min_one_le_rpow ((h : ℝ) / K) q (div_nonneg (by positivity) hKR.le) hq₀ hq₁)

/-- The exact finite-matrix bound in the paper:
`Pr[sum s is bad] ≤ (h_d(s)/2^t)^q`. -/
theorem badForSum_fractional_bound (d t s : ℕ) (q : ℝ)
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ((badForSumFinset d t s).card : ℝ) /
        Fintype.card (LinearColoring d t) ≤
      ((representationCount d s : ℝ) / ((2 ^ t : ℕ) : ℝ)) ^ q := by
  apply fractional_ratio_bound _ _ _ (2 ^ t) q
  · exact Fintype.card_pos
  · positivity
  · exact Finset.card_le_card (Finset.subset_univ _)
  · exact badForSum_card_mul_le d t s
  · exact hq₀
  · exact hq₁

end Green25Fractional

end

/- ## Part: `fractional_histogram` -/

section

/-
The exact carry automaton behind the representation histogram `h_d(s)`.

Digits and output bits are read from least significant to most significant.
For a prescribed binary output word, `carryMultiplicity` counts the ternary
words which produce that word and a prescribed final carry.  The four
recurrences below are the literal transition matrices

* `T₀(a,b) = (a,a+b)`,
* `T₁(a,b) = (a+b,b)`.

Thus this file turns the two-state tree in `fractional_carry.lean` into an
exact finite count, rather than merely an abstract recurrence.
-/

namespace Green25Fractional

/-- Output bit of adding a ternary digit and an incoming carry. -/
def carryOutput (z : Fin 3) (c : Bool) : Bool :=
  decide (((z : ℕ) + bitNat c) % 2 = 1)

/-- Outgoing carry of adding a ternary digit and an incoming carry. -/
def carryNext (z : Fin 3) (c : Bool) : Bool :=
  decide (2 ≤ (z : ℕ) + bitNat c)

/-- Run the base-two carry automaton, least significant digit first. -/
def runCarry : {d : ℕ} → (Fin d → Fin 3) → Bool → BitWord d × Bool
  | 0, _, c => (Fin.elim0, c)
  | _ + 1, z, c =>
      let rest := runCarry (Fin.tail z) (carryNext (z 0) c)
      (Fin.cons (carryOutput (z 0) c) rest.1, rest.2)

@[simp] theorem runCarry_zero (z : Fin 0 → Fin 3) (c : Bool) :
    runCarry z c = (Fin.elim0, c) := rfl

@[simp] theorem runCarry_cons {d : ℕ} (z : Fin 3) (zs : Fin d → Fin 3) (c : Bool) :
    runCarry (Fin.cons z zs) c =
      let rest := runCarry zs (carryNext z c)
      (Fin.cons (carryOutput z c) rest.1, rest.2) := by
  simp [runCarry]

theorem ternaryValue_cons {d : ℕ} (z : Fin 3) (zs : Fin d → Fin 3) :
    ternaryValue (Fin.cons z zs) = (z : ℕ) + 2 * ternaryValue zs := by
  simp only [ternaryValue, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
  rw [Finset.mul_sum]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem binaryValue_cons {d : ℕ} (z : Bool) (zs : BitWord d) :
    binaryValue (Fin.cons z zs) = bitNat z + 2 * binaryValue zs := by
  simp only [binaryValue, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
  rw [Finset.mul_sum]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem carry_step_value (z : Fin 3) (c : Bool) :
    (z : ℕ) + bitNat c = bitNat (carryOutput z c) + 2 * bitNat (carryNext z c) := by
  cases c <;> fin_cases z <;> norm_num [carryOutput, carryNext, bitNat]

/-- Arithmetic correctness of the carry automaton. -/
theorem runCarry_value {d : ℕ} (z : Fin d → Fin 3) (c : Bool) :
    ternaryValue z + bitNat c =
      binaryValue (runCarry z c).1 + bitNat (runCarry z c).2 * 2 ^ d := by
  induction d generalizing c with
  | zero =>
      simp [ternaryValue, binaryValue, runCarry]
  | succ d ih =>
      refine Fin.consCases (n := d) ?_ z
      intro digit tail
      let next := carryNext digit c
      let rest := runCarry tail next
      have hs := carry_step_value digit c
      have hi := ih tail next
      simp only [runCarry_cons, ternaryValue_cons, binaryValue_cons]
      change (digit : ℕ) + 2 * ternaryValue tail + bitNat c =
        bitNat (carryOutput digit c) + 2 * binaryValue rest.1 +
          bitNat rest.2 * 2 ^ (d + 1)
      change ternaryValue tail + bitNat next =
        binaryValue rest.1 + bitNat rest.2 * 2 ^ d at hi
      calc
        (digit : ℕ) + 2 * ternaryValue tail + bitNat c =
            ((digit : ℕ) + bitNat c) + 2 * ternaryValue tail := by ring
        _ = (bitNat (carryOutput digit c) + 2 * bitNat next) +
            2 * ternaryValue tail := by
              rw [show (digit : ℕ) + bitNat c =
                bitNat (carryOutput digit c) + 2 * bitNat next by
                  simpa only [next] using hs]
        _ = bitNat (carryOutput digit c) +
            2 * (ternaryValue tail + bitNat next) := by ring
        _ = bitNat (carryOutput digit c) +
            2 * (binaryValue rest.1 + bitNat rest.2 * 2 ^ d) := by rw [hi]
        _ = bitNat (carryOutput digit c) + 2 * binaryValue rest.1 +
            bitNat rest.2 * 2 ^ (d + 1) := by rw [pow_succ]; ring

/-- A finite binary word has value below the next power of two. -/
theorem binaryValue_lt_two_pow {d : ℕ} (w : BitWord d) :
    binaryValue w < 2 ^ d := by
  induction d with
  | zero => simp [binaryValue]
  | succ d ih =>
      refine Fin.consCases (n := d) ?_ w
      intro bit tail
      rw [binaryValue_cons, pow_succ]
      have ht := ih tail
      have hb : bitNat bit ≤ 1 := by cases bit <;> simp [bitNat]
      omega

/-- Fixed-length binary evaluation is injective. -/
theorem binaryValue_injective (d : ℕ) :
    Function.Injective (binaryValue : BitWord d → ℕ) := by
  induction d with
  | zero =>
      intro x y _
      exact Subsingleton.elim _ _
  | succ d ih =>
      intro x
      refine Fin.consCases (n := d) ?_ x
      intro xb xt y
      refine Fin.consCases (n := d) ?_ y
      intro yb yt h
      rw [binaryValue_cons, binaryValue_cons] at h
      cases xb with
      | false =>
          cases yb with
          | false =>
              simp [bitNat] at h ⊢
              apply ih
              omega
          | true =>
              simp [bitNat] at h
              omega
      | true =>
          cases yb with
          | false =>
              simp [bitNat] at h
              omega
          | true =>
              simp [bitNat] at h ⊢
              apply ih
              omega

/-- Numeric value of a binary output word together with its final carry. -/
def carryValue {d : ℕ} (w : BitWord d) (c : Bool) : ℕ :=
  binaryValue w + bitNat c * 2 ^ d

theorem carryValue_injective (d : ℕ) :
    Function.Injective (fun p : BitWord d × Bool => carryValue p.1 p.2) := by
  intro p r h
  rcases p with ⟨w, c⟩
  rcases r with ⟨v, e⟩
  cases c <;> cases e <;> simp [carryValue, bitNat] at h ⊢
  · exact binaryValue_injective d h
  · have hw := binaryValue_lt_two_pow w
    omega
  · have hv := binaryValue_lt_two_pow v
    omega
  · exact binaryValue_injective d h

/-- Equality of represented integers is equivalent to equality of the unique
binary output word and final carry. -/
theorem ternaryValue_eq_carryValue_iff {d : ℕ} (z : Fin d → Fin 3)
    (w : BitWord d) (c : Bool) :
    ternaryValue z = carryValue w c ↔ runCarry z false = (w, c) := by
  have hv := runCarry_value z false
  simp only [bitNat] at hv
  constructor
  · intro h
    apply carryValue_injective d
    change carryValue (runCarry z false).1 (runCarry z false).2 = carryValue w c
    rw [← h]
    simpa only [carryValue] using hv.symm
  · intro h
    rw [h] at hv
    simpa only [carryValue] using hv

/-- The encoded output lies in the full `(d+1)`-bit range. -/
def carryValueFin {d : ℕ} (p : BitWord d × Bool) : Fin (2 ^ (d + 1)) :=
  ⟨carryValue p.1 p.2, by
    have hw := binaryValue_lt_two_pow p.1
    cases p.2 <;> simp [carryValue, bitNat, pow_succ] <;> omega⟩

theorem carryValueFin_injective (d : ℕ) : Function.Injective (@carryValueFin d) := by
  intro p r h
  apply carryValue_injective d
  exact congrArg Fin.val h

theorem carryValueFin_bijective (d : ℕ) : Function.Bijective (@carryValueFin d) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · exact carryValueFin_injective d
  · simp [BitWord, pow_succ, Nat.mul_comm]

/-- Canonical reindexing equivalence between output/carry pairs and all
integers below `2^(d+1)`. -/
noncomputable def carryValueEquiv (d : ℕ) :
    (BitWord d × Bool) ≃ Fin (2 ^ (d + 1)) :=
  Equiv.ofBijective carryValueFin (carryValueFin_bijective d)

@[simp] theorem carryValueEquiv_apply {d : ℕ} (p : BitWord d × Bool) :
    carryValueEquiv d p = carryValueFin p := rfl

@[simp] theorem fin_consEquiv_apply {α : Type*} {d : ℕ} (z : α) (zs : Fin d → α) :
    (Fin.consEquiv (fun _ : Fin (d + 1) => α)) (z, zs) = Fin.cons z zs := rfl

/-- Number of ternary words producing exactly `w` and the stated final carry. -/
def carryMultiplicity {d : ℕ} (inputCarry : Bool) (w : BitWord d)
    (finalCarry : Bool) : ℕ :=
  ∑ z : Fin d → Fin 3, if runCarry z inputCarry = (w, finalCarry) then 1 else 0

/-- At the integer encoded by `(w,c)`, the representation number `h_d(s)` is
exactly the corresponding carry-automaton fiber size. -/
theorem representationCount_carryValue {d : ℕ} (w : BitWord d) (c : Bool) :
    representationCount d (carryValue w c) = carryMultiplicity false w c := by
  classical
  unfold representationCount TernaryRepresentation carryMultiplicity
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [ternaryValue_eq_carryValue_iff]
  exact (Finset.sum_boole _ _).symm

theorem carryMultiplicity_zero (inputCarry finalCarry : Bool) :
    carryMultiplicity inputCarry (zeroBitWord 0) finalCarry =
      if inputCarry = finalCarry then 1 else 0 := by
  have hfun : Fin.elim0 = zeroBitWord 0 := Subsingleton.elim _ _
  simp [carryMultiplicity, runCarry, hfun]

/-- For incoming carry zero and output bit zero, digits `0` and `2` give the
two possible next carries. -/
theorem carryMultiplicity_false_cons_false {d : ℕ} (w : BitWord d)
    (finalCarry : Bool) :
    carryMultiplicity false (Fin.cons false w) finalCarry =
      carryMultiplicity false w finalCarry + carryMultiplicity true w finalCarry := by
  unfold carryMultiplicity
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (d + 1) => Fin 3))]
  rw [Fintype.sum_prod_type]
  simp only [fin_consEquiv_apply, runCarry_cons]
  simp [Fin.sum_univ_succ, carryOutput, carryNext, bitNat]
  simp only [Prod.ext_iff]

/-- For incoming carry zero and output bit one, only digit `1` contributes. -/
theorem carryMultiplicity_false_cons_true {d : ℕ} (w : BitWord d)
    (finalCarry : Bool) :
    carryMultiplicity false (Fin.cons true w) finalCarry =
      carryMultiplicity false w finalCarry := by
  unfold carryMultiplicity
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (d + 1) => Fin 3))]
  rw [Fintype.sum_prod_type]
  simp only [fin_consEquiv_apply, runCarry_cons]
  simp [Fin.sum_univ_succ, carryOutput, carryNext, bitNat]
  simp only [Prod.ext_iff]

/-- For incoming carry one and output bit zero, only digit `1` contributes. -/
theorem carryMultiplicity_true_cons_false {d : ℕ} (w : BitWord d)
    (finalCarry : Bool) :
    carryMultiplicity true (Fin.cons false w) finalCarry =
      carryMultiplicity true w finalCarry := by
  unfold carryMultiplicity
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (d + 1) => Fin 3))]
  rw [Fintype.sum_prod_type]
  simp only [fin_consEquiv_apply, runCarry_cons]
  simp [Fin.sum_univ_succ, carryOutput, carryNext, bitNat]
  simp only [Prod.ext_iff]

/-- For incoming carry one and output bit one, digits `0` and `2` give the
two possible next carries. -/
theorem carryMultiplicity_true_cons_true {d : ℕ} (w : BitWord d)
    (finalCarry : Bool) :
    carryMultiplicity true (Fin.cons true w) finalCarry =
      carryMultiplicity false w finalCarry + carryMultiplicity true w finalCarry := by
  unfold carryMultiplicity
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (d + 1) => Fin 3))]
  rw [Fintype.sum_prod_type]
  simp only [fin_consEquiv_apply, runCarry_cons]
  simp [Fin.sum_univ_succ, carryOutput, carryNext, bitNat,
    Nat.add_comm]
  simp only [Prod.ext_iff]

/-- Apply the carry matrices selected by a low-to-high output word. -/
def carryState : {d : ℕ} → BitWord d → ℕ → ℕ → ℕ × ℕ
  | 0, _, a, b => (a, b)
  | _ + 1, w, a, b =>
      if w 0 then
        carryState (Fin.tail w) (a + b) b
      else
        carryState (Fin.tail w) a (a + b)

@[simp] theorem carryState_zero (w : BitWord 0) (a b : ℕ) :
    carryState w a b = (a, b) := rfl

@[simp] theorem carryState_cons_false {d : ℕ} (w : BitWord d) (a b : ℕ) :
    carryState (Fin.cons false w) a b = carryState w a (a + b) := by
  simp [carryState]

@[simp] theorem carryState_cons_true {d : ℕ} (w : BitWord d) (a b : ℕ) :
    carryState (Fin.cons true w) a b = carryState w (a + b) b := by
  simp [carryState]

/-- Linear combination of the two rows of the carry-transition matrix. -/
def weightedCarry {d : ℕ} (w : BitWord d) (a b : ℕ) : ℕ × ℕ :=
  (a * carryMultiplicity false w false + b * carryMultiplicity true w false,
   a * carryMultiplicity false w true + b * carryMultiplicity true w true)

theorem weightedCarry_zero (w : BitWord 0) (a b : ℕ) :
    weightedCarry w a b = (a, b) := by
  have hw : w = zeroBitWord 0 := Subsingleton.elim _ _
  subst w
  simp [weightedCarry, carryMultiplicity_zero]

theorem weightedCarry_cons_false {d : ℕ} (w : BitWord d) (a b : ℕ) :
    weightedCarry (Fin.cons false w) a b = weightedCarry w a (a + b) := by
  apply Prod.ext <;>
    simp [weightedCarry, carryMultiplicity_false_cons_false,
      carryMultiplicity_true_cons_false] <;> ring

theorem weightedCarry_cons_true {d : ℕ} (w : BitWord d) (a b : ℕ) :
    weightedCarry (Fin.cons true w) a b = weightedCarry w (a + b) b := by
  apply Prod.ext <;>
    simp [weightedCarry, carryMultiplicity_false_cons_true,
      carryMultiplicity_true_cons_true] <;> ring

/-- Exact semantic interpretation of the carry state.  The entries obtained
by multiplying the two transition matrices are the actual fiber counts of
the ternary-digit automaton. -/
theorem weightedCarry_eq_carryState {d : ℕ} (w : BitWord d) (a b : ℕ) :
    weightedCarry w a b = carryState w a b := by
  induction d generalizing a b with
  | zero => exact weightedCarry_zero w a b
  | succ d ih =>
      refine Fin.consCases (n := d) ?_ w
      intro bit tail
      cases bit with
      | false =>
          rw [weightedCarry_cons_false, carryState_cons_false]
          exact ih tail a (a + b)
      | true =>
          rw [weightedCarry_cons_true, carryState_cons_true]
          exact ih tail (a + b) b

/-- Starting with carry zero, the two terminal multiplicities are precisely
the two components of the carry-tree state. -/
theorem carryMultiplicity_pair_eq_carryState {d : ℕ} (w : BitWord d) :
    (carryMultiplicity false w false, carryMultiplicity false w true) =
      carryState w 1 0 := by
  simpa [weightedCarry] using weightedCarry_eq_carryState w 1 0

theorem carryMultiplicity_final_false_eq {d : ℕ} (w : BitWord d) :
    carryMultiplicity false w false = (carryState w 1 0).1 :=
  congrArg Prod.fst (carryMultiplicity_pair_eq_carryState w)

theorem carryMultiplicity_final_true_eq {d : ℕ} (w : BitWord d) :
    carryMultiplicity false w true = (carryState w 1 0).2 :=
  congrArg Prod.snd (carryMultiplicity_pair_eq_carryState w)

/-- Fractional moment obtained by summing the two terminal entries over all
binary output words. -/
noncomputable def carryStateMoment (d : ℕ) (q : ℝ) (a b : ℕ) : ℝ :=
  Finset.univ.sum (fun w : BitWord d =>
    ((carryState w a b).1 : ℝ) ^ q + ((carryState w a b).2 : ℝ) ^ q)

/-- Summing the exact states over all output words gives the recursive
terminal moment from `fractional_carry.lean`. -/
theorem carryStateMoment_eq_terminalMoment (d : ℕ) (q : ℝ) (a b : ℕ) :
    carryStateMoment d q a b = terminalMoment d q a b := by
  induction d generalizing a b with
  | zero =>
      simp [carryStateMoment, terminalMoment]
  | succ d ih =>
      unfold carryStateMoment
      rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (d + 1) => Bool))]
      rw [Fintype.sum_prod_type, Fintype.sum_bool]
      simp only [fin_consEquiv_apply, carryState_cons_true, carryState_cons_false]
      change carryStateMoment d q (a + b) b + carryStateMoment d q a (a + b) = _
      rw [ih (a + b) b, ih a (a + b)]
      simp only [terminalMoment, Nat.cast_add]
      ring

/-- The fractional moment of the actual automaton fiber sizes is exactly the
terminal carry-tree moment. -/
theorem carryMultiplicity_moment_eq_terminalMoment (d : ℕ) (q : ℝ) :
    (∑ w : BitWord d,
        ((carryMultiplicity false w false : ℝ) ^ q +
          (carryMultiplicity false w true : ℝ) ^ q)) =
      terminalMoment d q 1 0 := by
  calc
    (∑ w : BitWord d,
        ((carryMultiplicity false w false : ℝ) ^ q +
          (carryMultiplicity false w true : ℝ) ^ q)) =
        carryStateMoment d q 1 0 := by
      simp only [carryStateMoment, carryMultiplicity_final_false_eq,
        carryMultiplicity_final_true_eq]
    _ = terminalMoment d q 1 0 := by
      simpa using carryStateMoment_eq_terminalMoment d q 1 0

/-- Exact identification of the complete representation histogram with the
two-state terminal moment.  The finite range is exhaustive because ternary
digits have maximum value `2 * (2^d - 1) < 2^(d+1)`. -/
theorem representationCount_moment_eq_terminalMoment (d : ℕ) (q : ℝ) :
    (∑ s : Fin (2 ^ (d + 1)), (representationCount d (s : ℕ) : ℝ) ^ q) =
      terminalMoment d q 1 0 := by
  calc
    (∑ s : Fin (2 ^ (d + 1)), (representationCount d (s : ℕ) : ℝ) ^ q) =
        ∑ p : BitWord d × Bool,
          (representationCount d ((carryValueEquiv d p : Fin (2 ^ (d + 1))) : ℕ) : ℝ) ^ q := by
      symm
      exact Equiv.sum_comp (carryValueEquiv d)
        (fun s : Fin (2 ^ (d + 1)) => (representationCount d (s : ℕ) : ℝ) ^ q)
    _ = ∑ w : BitWord d,
        ((carryMultiplicity false w true : ℝ) ^ q +
          (carryMultiplicity false w false : ℝ) ^ q) := by
      rw [Fintype.sum_prod_type]
      simp only [Fintype.sum_bool, carryValueEquiv_apply, carryValueFin,
        representationCount_carryValue]
    _ = terminalMoment d q 1 0 := by
      simpa only [add_comm] using carryMultiplicity_moment_eq_terminalMoment d q

/-- The finite block certificate now bounds the actual `h_d(s)` histogram,
not merely the abstract carry recurrence. -/
theorem representationCount_moment_block_bound (L k r : ℕ) (q : ℝ)
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    (∑ s : Fin (2 ^ (L * k + r + 1)),
        (representationCount (L * k + r) (s : ℕ) : ℝ) ^ q) ≤
      (2 : ℝ) ^ (1 - q) * blockCoeff L q ^ k *
        (2 * (3 / 2 : ℝ) ^ q) ^ r := by
  rw [representationCount_moment_eq_terminalMoment]
  exact representation_terminal_bound L k r q hq₀ hq₁

end Green25Fractional

end

/- ## Part: `fractional_certificate` -/

section

/- The L=8, q=1/16 certificate. Every generated integer is checked by Lean.
No native_decide or external evaluator is trusted for the proof. -/

namespace Green25Fractional

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- Terminal masses for all bit words; the list retains multiplicities. -/
def terminalNorms : ℕ → ℕ → ℕ → List ℕ
  | 0, a, b => [a + b]
  | n + 1, a, b => terminalNorms n a (a + b) ++ terminalNorms n (a + b) b

/-- The real moment agrees with the explicit finite list, at any common scale. -/
theorem moment_eq_terminalNorms (n : ℕ) (q s : ℝ) (a b : ℕ) :
    moment n q (s * a) (s * b) =
      ((terminalNorms n a b).map (fun k : ℕ => (s * (k : ℝ)) ^ q)).sum := by
  induction n generalizing a b with
  | zero => simp [moment, terminalNorms, mul_add]
  | succ n ih =>
    simpa [moment, terminalNorms, List.map_append, List.sum_append, Nat.cast_add, mul_add]
      using congrArg₂ (fun x y : ℝ => x + y) (ih a (a + b)) (ih (a + b) b)

/-- Upper bounds for 10^6*(n/2)^(1/16), for the 51 masses occurring at depth 8. -/
def rootUpper : ℕ → ℕ
  | 10 => 1105824
  | 17 => 1143112
  | 22 => 1161682
  | 23 => 1164914
  | 25 => 1171000
  | 26 => 1173874
  | 27 => 1176647
  | 28 => 1179324
  | 29 => 1181913
  | 32 => 1189208
  | 33 => 1191497
  | 35 => 1195887
  | 37 => 1200047
  | 38 => 1202049
  | 39 => 1204002
  | 40 => 1205909
  | 41 => 1207772
  | 42 => 1209592
  | 43 => 1211372
  | 45 => 1214819
  | 47 => 1218125
  | 48 => 1219729
  | 49 => 1221302
  | 51 => 1224359
  | 52 => 1225846
  | 53 => 1227307
  | 55 => 1230151
  | 56 => 1231537
  | 57 => 1232900
  | 58 => 1234241
  | 59 => 1235561
  | 60 => 1236859
  | 61 => 1238138
  | 62 => 1239397
  | 63 => 1240637
  | 64 => 1241858
  | 65 => 1243062
  | 66 => 1244249
  | 67 => 1245419
  | 68 => 1246573
  | 69 => 1247711
  | 70 => 1248833
  | 71 => 1249941
  | 73 => 1252113
  | 74 => 1253178
  | 75 => 1254230
  | 76 => 1255269
  | 79 => 1258310
  | 80 => 1259299
  | 81 => 1260277
  | 89 => 1267718
  | _ => 0

/-- Checking every leaf of the actual transition tree, not assuming a supplied histogram. -/
theorem root_checks : ∀ n ∈ terminalNorms 8 1 1,
    n * 1000000 ^ 16 ≤ 2 * rootUpper n ^ 16 := by decide

theorem root_sum : ((terminalNorms 8 1 1).map rootUpper).sum = 312445416 := by decide

/-- Lift a certified integer power inequality to a real 16th-root bound. -/
theorem real_root_bound (n r : ℕ)
    (h : n * 1000000 ^ 16 ≤ 2 * r ^ 16) :
    ((n : ℝ) / 2) ^ (1 / 16 : ℝ) ≤ (r : ℝ) / 1000000 := by
  have hcast : (n : ℝ) * (1000000 : ℝ) ^ 16 ≤ 2 * (r : ℝ) ^ 16 := by
    exact_mod_cast h
  have hp : (n : ℝ) / 2 ≤ ((r : ℝ) / 1000000) ^ (16 : ℕ) := by
    rw [div_pow]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 1000000 ^ 16)).mpr
    nlinarith
  have hp' : (n : ℝ) / 2 ≤ ((r : ℝ) / 1000000) ^ (16 : ℝ) := by
    rw [Real.rpow_ofNat]
    exact hp
  simpa only [one_div] using
    (Real.rpow_inv_le_iff_of_pos (by positivity : (0 : ℝ) ≤ (n : ℝ) / 2)
      (by positivity : (0 : ℝ) ≤ (r : ℝ) / 1000000)
      (by norm_num : (0 : ℝ) < 16)).mpr hp'

theorem scaled_nat_sum (l : List ℕ) :
    (l.map (fun n : ℕ => (n : ℝ) / 1000000)).sum = ((l.sum : ℕ) : ℝ) / 1000000 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_add, ih]
    ring

/-- B_8(1/16) <= 312445416/10^6, with the finite computation checked by the kernel. -/
theorem block8_coefficient_bound :
    blockCoeff 8 (1 / 16) ≤ (312445416 : ℝ) / 1000000 := by
  have heq : blockCoeff 8 (1 / 16) =
      ((terminalNorms 8 1 1).map (fun n : ℕ => ((n : ℝ) / 2) ^ (1 / 16 : ℝ))).sum := by
    simpa [blockCoeff, div_eq_mul_inv, mul_comm] using
      moment_eq_terminalNorms 8 (1 / 16) (1 / 2) 1 1
  calc
    _ = _ := heq
    _ ≤ ((terminalNorms 8 1 1).map (fun n => (rootUpper n : ℝ) / 1000000)).sum :=
      List.sum_le_sum (fun n hn => real_root_bound n (rootUpper n) (root_checks n hn))
    _ = (312445416 : ℝ) / 1000000 := by
      simpa [List.map_map, root_sum] using scaled_nat_sum ((terminalNorms 8 1 1).map rootUpper)

/-- The original 683-digit integer inequality, checked independently of Python. -/
theorem integer_decay_certificate :
    1000 * (312445416 : ℕ) ^ 80 < 999 * 256000000 ^ 80 * 2 ^ 23 := by
  norm_num

end Green25Fractional

end

/- ## Part: `fractional_decay` -/

section

/- The finite certificate implies actual geometric decay for alpha=23/40. -/

namespace Green25Fractional

-- The certificate needs the concrete integer 2^663 (200 decimal digits).
set_option exponentiation.threshold 1024

noncomputable def decay8 : ℝ :=
  blockCoeff 8 (1 / 16) / (2 : ℝ) ^ (8 + 8 * (1 / 16) * (23 / 40) : ℝ)

theorem decay8_denominator_pow :
    ((2 : ℝ) ^ (8 + 8 * (1 / 16) * (23 / 40) : ℝ)) ^ (80 : ℕ) =
      (2 : ℝ) ^ (663 : ℕ) := by
  rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem decay8_nonneg : 0 ≤ decay8 := by
  unfold decay8
  exact div_nonneg (moment_nonneg 8 (1 / 16) _ _ (by norm_num) (by norm_num))
    (Real.rpow_nonneg (by norm_num) _)

/-- The quantitative margin claimed in the paper, now connected to the real B_8. -/
theorem decay8_power_bound : decay8 ^ (80 : ℕ) < (999 : ℝ) / 1000 := by
  have hpow : blockCoeff 8 (1 / 16) ^ (80 : ℕ) ≤
      ((312445416 : ℝ) / 1000000) ^ (80 : ℕ) :=
    pow_le_pow_left₀ (moment_nonneg 8 (1 / 16) _ _ (by norm_num) (by norm_num))
      block8_coefficient_bound 80
  unfold decay8
  rw [div_pow, decay8_denominator_pow]
  calc
    _ ≤ ((312445416 : ℝ) / 1000000) ^ (80 : ℕ) / (2 : ℝ) ^ (663 : ℕ) :=
      div_le_div_of_nonneg_right hpow (by positivity)
    _ < (999 : ℝ) / 1000 := by norm_num

theorem decay8_lt_one : decay8 < 1 := by
  by_contra h
  have hpow : 1 ≤ decay8 ^ (80 : ℕ) := one_le_pow₀ (le_of_not_gt h)
  linarith [decay8_power_bound]

theorem decay8_tendsto_zero :
    Filter.Tendsto (fun k : ℕ => decay8 ^ k) Filter.atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one decay8_nonneg decay8_lt_one

end Green25Fractional

end

/- ## Part: `fractional_aggregate` -/

section

/-
Aggregate the one-sum probability bounds and feed them into finite averaging.

This is the first module in which the matrix union bound, the exact
representation histogram, and the finite `B₈` certificate all meet.
-/

namespace Green25Fractional

/-- Sum the pointwise fractional probability estimates over every candidate
integer sum and replace the histogram by its exact carry moment. -/
theorem aggregate_bad_ratio_le_terminalMoment (d t : ℕ) (q : ℝ)
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    (∑ s : CandidateSum d,
        ((badForSumFinset d t s).card : ℝ) /
          Fintype.card (LinearColoring d t)) ≤
      terminalMoment d q 1 0 / (((2 ^ t : ℕ) : ℝ) ^ q) := by
  calc
    (∑ s : CandidateSum d,
        ((badForSumFinset d t s).card : ℝ) /
          Fintype.card (LinearColoring d t)) ≤
        ∑ s : CandidateSum d,
          (((representationCount d (s : ℕ) : ℝ) / ((2 ^ t : ℕ) : ℝ)) ^ q) :=
      Finset.sum_le_sum fun s _ => badForSum_fractional_bound d t s q hq₀ hq₁
    _ = (∑ s : CandidateSum d,
          (representationCount d (s : ℕ) : ℝ) ^ q) /
        (((2 ^ t : ℕ) : ℝ) ^ q) := by
      rw [div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s _
      simpa only [div_eq_mul_inv] using
        Real.div_rpow (show (0 : ℝ) ≤ representationCount d (s : ℕ) by positivity)
          (show (0 : ℝ) ≤ ((2 ^ t : ℕ) : ℝ) by positivity) q
    _ = terminalMoment d q 1 0 / (((2 ^ t : ℕ) : ℝ) ^ q) := by
      rw [representationCount_moment_eq_terminalMoment]

/-- The general block estimate for the aggregate bad-sum probability. -/
theorem aggregate_bad_ratio_block_bound (L k r t : ℕ) (q : ℝ)
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    (∑ s : CandidateSum (L * k + r),
        ((badForSumFinset (L * k + r) t s).card : ℝ) /
          Fintype.card (LinearColoring (L * k + r) t)) ≤
      ((2 : ℝ) ^ (1 - q) * blockCoeff L q ^ k *
        (2 * (3 / 2 : ℝ) ^ q) ^ r) /
          (((2 ^ t : ℕ) : ℝ) ^ q) := by
  refine (aggregate_bad_ratio_le_terminalMoment (L * k + r) t q hq₀ hq₁).trans ?_
  exact div_le_div_of_nonneg_right
    (representation_terminal_bound L k r q hq₀ hq₁) (by positivity)

/-- Convert a strict real aggregate estimate back to the natural-number
incidence inequality required by finite averaging. -/
theorem exists_coloring_of_aggregate_bad_ratio_lt (d t B : ℕ)
    (hbad : (∑ s : CandidateSum d,
        ((badForSumFinset d t s).card : ℝ) /
          Fintype.card (LinearColoring d t)) < B) :
    ∃ H : LinearColoring d t, badSumCount d t H < B := by
  have hcard : (0 : ℝ) < Fintype.card (LinearColoring d t) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (LinearColoring d t))
  have hratio :
      ((∑ s : CandidateSum d, (badForSumFinset d t s).card : ℕ) : ℝ) /
          Fintype.card (LinearColoring d t) < B := by
    rw [Nat.cast_sum, Finset.sum_div]
    exact hbad
  have hreal :
      ((∑ s : CandidateSum d, (badForSumFinset d t s).card : ℕ) : ℝ) <
        (B * Fintype.card (LinearColoring d t) : ℕ) := by
    rw [Nat.cast_mul]
    exact (div_lt_iff₀ hcard).mp hratio
  have hnat :
      (∑ s : CandidateSum d, (badForSumFinset d t s).card) <
        B * Fintype.card (LinearColoring d t) := by
    exact_mod_cast hreal
  exact exists_coloring_with_few_bad_sums d t B hnat

/-- A strict terminal-moment bound is sufficient for a concrete coloring. -/
theorem exists_coloring_of_terminalMoment_ratio_lt (d t B : ℕ) (q : ℝ)
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1)
    (hterminal : terminalMoment d q 1 0 / (((2 ^ t : ℕ) : ℝ) ^ q) < B) :
    ∃ H : LinearColoring d t, badSumCount d t H < B := by
  apply exists_coloring_of_aggregate_bad_ratio_lt d t B
  exact (aggregate_bad_ratio_le_terminalMoment d t q hq₀ hq₁).trans_lt hterminal

end Green25Fractional

end

/- ## Part: `fractional_collision` -/

section

/-
Interpret the bad-sum incidence set as an actual same-color restricted
sumset.  This closes the combinatorial soundness direction of the random
linear-coloring construction.
-/

namespace Green25Fractional

theorem xorWord_left_cancel {d : ℕ} (x y : BitWord d) :
    xorWord x (xorWord x y) = y := by
  funext i
  cases hx : x i <;> cases hy : y i <;> simp [xorWord, hx, hy]

theorem xorWord_zero_right {d : ℕ} (x : BitWord d) :
    xorWord x (zeroBitWord d) = x := by
  funext i
  cases hx : x i <;> simp [xorWord, zeroBitWord, hx]

theorem xorWord_ne_zero_of_ne {d : ℕ} {x y : BitWord d} (hxy : x ≠ y) :
    xorWord x y ≠ zeroBitWord d := by
  intro hzero
  apply hxy
  calc
    x = xorWord x (zeroBitWord d) := (xorWord_zero_right x).symm
    _ = xorWord x (xorWord x y) := by rw [hzero]
    _ = y := xorWord_left_cancel x y

/-- A sum is realized by two distinct words of the same linear color. -/
def SameColorSum {d t : ℕ} (H : LinearColoring d t) (s : ℕ) : Prop :=
  ∃ x y : BitWord d, x ≠ y ∧
    H (boolToF2Word x) = H (boolToF2Word y) ∧
      binaryValue x + binaryValue y = s

/-- Every actual same-color restricted sum belongs to the union-bound bad
set.  The witness difference is the XOR of the two endpoints. -/
theorem sameColorSum_mem_badForSum {d t s : ℕ} {H : LinearColoring d t}
    (hs : SameColorSum H s) : H ∈ badForSumFinset d t s := by
  rcases hs with ⟨x, y, hxy, hcolor, hsum⟩
  let c : BitWord d := xorWord x y
  have hcne : c ≠ zeroBitWord d := xorWord_ne_zero_of_ne hxy
  have hvalue : binaryValue x + binaryValue (xorWord x c) = s := by
    simpa only [c, xorWord_left_cancel] using hsum
  let nc : NonzeroCapableDifference d s := ⟨c, hcne, ⟨x, hvalue⟩⟩
  have hann : H (boolToF2Word c) = 0 := by
    apply (xor_same_color_iff H x c).mp
    simpa only [c, xorWord_left_cancel] using hcolor.symm
  simp only [badForSumFinset, Finset.mem_biUnion, Finset.mem_univ, true_and]
  refine ⟨nc, ?_⟩
  simpa [annihilatingFinset] using hann

/-- Candidate sums actually realized by a distinct same-color pair. -/
noncomputable def collisionSumFinset (d t : ℕ) (H : LinearColoring d t) :
    Finset (CandidateSum d) := by
  classical
  exact Finset.univ.filter fun s => SameColorSum H (s : ℕ)

/-- Candidate sums selected by the union-bound event for one coloring. -/
noncomputable def badSumFinset (d t : ℕ) (H : LinearColoring d t) :
    Finset (CandidateSum d) := by
  classical
  exact Finset.univ.filter fun s => H ∈ badForSumFinset d t s

theorem collisionSumFinset_subset_bad {d t : ℕ} (H : LinearColoring d t) :
    collisionSumFinset d t H ⊆ badSumFinset d t H := by
  classical
  intro s hs
  simp only [collisionSumFinset, badSumFinset, Finset.mem_filter, Finset.mem_univ,
    true_and] at hs ⊢
  exact sameColorSum_mem_badForSum hs

/-- The probabilistic count bounds the actual restricted-sum union. -/
theorem collisionSumFinset_card_le_badSumCount {d t : ℕ} (H : LinearColoring d t) :
    (collisionSumFinset d t H).card ≤ badSumCount d t H := by
  classical
  rw [badSumCount, Nat.card_eq_fintype_card,
    Fintype.card_subtype (fun s : CandidateSum d => H ∈ badForSumFinset d t s)]
  change (collisionSumFinset d t H).card ≤ (badSumFinset d t H).card
  exact Finset.card_le_card (collisionSumFinset_subset_bad H)

/-- A coloring produced by the aggregate estimate has fewer than `B`
actual same-color restricted sums. -/
theorem exists_coloring_with_few_collision_sums (d t B : ℕ) (q : ℝ)
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1)
    (hterminal : terminalMoment d q 1 0 / (((2 ^ t : ℕ) : ℝ) ^ q) < B) :
    ∃ H : LinearColoring d t, (collisionSumFinset d t H).card < B := by
  obtain ⟨H, hH⟩ :=
    exists_coloring_of_terminalMoment_ratio_lt d t B q hq₀ hq₁ hterminal
  exact ⟨H, (collisionSumFinset_card_le_badSumCount H).trans_lt hH⟩

/-- Concrete dyadic reduction at exponent `23/40`: on `2^(40m)` words use
`2^(23m)` linear colors.  Only the displayed one-variable decay inequality
remains to obtain fewer than `2^(40m)/16` collision sums. -/
theorem exists_block8_collision_coloring (m : ℕ)
    (hscalar :
      ((2 : ℝ) ^ (15 / 16 : ℝ) * blockCoeff 8 (1 / 16) ^ (5 * m)) /
          (((2 ^ (23 * m) : ℕ) : ℝ) ^ (1 / 16 : ℝ)) <
        (2 ^ (40 * m - 4) : ℕ)) :
    ∃ H : LinearColoring (40 * m) (23 * m),
      (collisionSumFinset (40 * m) (23 * m) H).card < 2 ^ (40 * m - 4) := by
  apply exists_coloring_with_few_collision_sums
    (40 * m) (23 * m) (2 ^ (40 * m - 4)) (1 / 16)
    (by norm_num) (by norm_num)
  have hd : 8 * (5 * m) + 0 = 40 * m := by omega
  have hb := representation_terminal_bound 8 (5 * m) 0 (1 / 16 : ℝ)
    (by norm_num) (by norm_num)
  rw [hd] at hb
  rw [show (1 : ℝ) - 1 / 16 = 15 / 16 by norm_num] at hb
  have hb' : terminalMoment (40 * m) (1 / 16) 1 0 ≤
      (2 : ℝ) ^ (15 / 16 : ℝ) * blockCoeff 8 (1 / 16) ^ (5 * m) := by
    simpa only [pow_zero, mul_one] using hb
  exact (div_le_div_of_nonneg_right hb' (by positivity)).trans_lt hscalar

end Green25Fractional

end

/- ## Part: `fractional_asymptotic` -/

section

/-
Extract a concrete sufficiently-large threshold from the certified decay.
-/

namespace Green25Fractional

set_option exponentiation.threshold 20000

/-- A reusable power-only form of the explicit decay estimate. -/
theorem decay8_pow_small {n : ℕ} (hn : 320000 ≤ n) :
    decay8 ^ n < 1 / 32 := by
  have hpow : (decay8 ^ (80 : ℕ)) ^ (4000 : ℕ) <
      ((999 : ℝ) / 1000) ^ (4000 : ℕ) :=
    pow_lt_pow_left₀ decay8_power_bound (pow_nonneg decay8_nonneg 80) (by norm_num)
  rw [← pow_mul] at hpow
  have hrat : ((999 : ℝ) / 1000) ^ (4000 : ℕ) < 1 / 32 := by
    norm_num
  have hsmall : decay8 ^ (320000 : ℕ) < 1 / 32 := by
    have hex : 80 * 4000 = 320000 := by norm_num
    rw [hex] at hpow
    exact hpow.trans hrat
  have hmono : decay8 ^ n ≤ decay8 ^ (320000 : ℕ) :=
    pow_le_pow_of_le_one decay8_nonneg decay8_lt_one.le hn
  exact hmono.trans_lt hsmall

/-- Four certified contraction batches provide enough room for all rounding
and incomplete-block constants in the all-dimension reduction. -/
theorem decay8_pow_very_small {n : ℕ} (hn : 1280000 ≤ n) :
    decay8 ^ n < 1 / 1048576 := by
  have hbase := decay8_pow_small (n := 320000) (by norm_num)
  have hfour : (decay8 ^ (320000 : ℕ)) ^ (4 : ℕ) <
      ((1 / 32 : ℝ) ^ (4 : ℕ)) :=
    pow_lt_pow_left₀ hbase (pow_nonneg decay8_nonneg 320000) (by norm_num)
  rw [← pow_mul] at hfour
  have hfixed : decay8 ^ (1280000 : ℕ) < 1 / 1048576 := by
    norm_num at hfour ⊢
    exact hfour
  have hmono : decay8 ^ n ≤ decay8 ^ (1280000 : ℕ) :=
    pow_le_pow_of_le_one decay8_nonneg decay8_lt_one.le hn
  exact hmono.trans_lt hfixed

/-- A deliberately conservative explicit threshold.  It avoids any
non-effective use of the limit theorem: 4000 blocks of the certified
80th-power contraction already beat the remaining constant factor. -/
theorem decay8_scaled_small {m : ℕ} (hm : 64000 ≤ m) :
    (2 : ℝ) ^ (15 / 16 : ℝ) * decay8 ^ (5 * m) < 1 / 16 := by
  have hexp : 320000 ≤ 5 * m := by omega
  have hdecay : decay8 ^ (5 * m) < 1 / 32 := decay8_pow_small hexp
  have htwo : (2 : ℝ) ^ (15 / 16 : ℝ) < 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
        (by norm_num : (15 / 16 : ℝ) < 1)
  calc
    (2 : ℝ) ^ (15 / 16 : ℝ) * decay8 ^ (5 * m) <
        (2 : ℝ) ^ (15 / 16 : ℝ) * (1 / 32 : ℝ) :=
      mul_lt_mul_of_pos_left hdecay (Real.rpow_pos_of_pos (by norm_num) _)
    _ < 2 * (1 / 32 : ℝ) := mul_lt_mul_of_pos_right htwo (by norm_num)
    _ = 1 / 16 := by norm_num

end Green25Fractional

end

/- ## Part: `fractional_refinement` -/

section

/- Refining a finite coloring to use exactly a prescribed number of colors. -/

namespace Green25Fractional

open Function Set

/-- If a finite coloring uses at most `k` colors and its domain has at least
`k` points, its color classes can be split until exactly `k` nonempty colors
are used.  The new coloring refines the old one, so every new monochromatic
pair was already monochromatic before the split. -/
theorem exists_surjective_refinement
    {X C : Type*} [Fintype X] (f : X → C) (k : ℕ)
    (hused : Nat.card (Set.range f) ≤ k)
    (hk : k ≤ Nat.card X) :
    ∃ g : X → Fin k, Function.Surjective g ∧
      ∀ ⦃x y : X⦄, g x = g y → f x = f y := by
  classical
  let R := Set.range f
  let q : X → R := fun x => ⟨f x, x, rfl⟩
  have hq : Function.Surjective q := by
    rintro ⟨c, x, rfl⟩
    exact ⟨x, rfl⟩
  let rep : R ↪ X :=
    ⟨Function.surjInv hq, Function.injective_surjInv hq⟩
  have hqrep (r : R) : q (rep r) = r := by
    exact Function.rightInverse_surjInv hq r
  have hrepCard : (Set.range rep).ncard = Nat.card R := by
    exact Set.ncard_range_of_injective rep.injective
  have hR : Nat.card R = Nat.card (Set.range f) := by rfl
  have hpickCard : (Set.range rep).ncard + (k - Nat.card R) ≤ Nat.card X := by
    rw [hrepCard]
    rw [hR]
    omega
  obtain ⟨pick, hdisj⟩ :=
    Fin.Embedding.exists_embedding_disjoint_range_of_add_le_Nat_card hpickCard
  let raw : X → R ⊕ Fin (k - Nat.card R) := fun x =>
    if hx : x ∈ Set.range pick then Sum.inr (Classical.choose hx)
    else Sum.inl (q x)
  have hraw_surj : Function.Surjective raw := by
    intro z
    rcases z with r | i
    · have hnot : rep r ∉ Set.range pick := by
        intro hr
        exact Set.disjoint_left.mp hdisj ⟨r, rfl⟩ hr
      refine ⟨rep r, ?_⟩
      simp only [raw, dif_neg hnot]
      exact congrArg Sum.inl (hqrep r)
    · have hi : pick i ∈ Set.range pick := ⟨i, rfl⟩
      refine ⟨pick i, ?_⟩
      simp only [raw, dif_pos hi]
      congr 1
      exact pick.injective (Classical.choose_spec hi)
  have hraw_refines :
      ∀ ⦃x y : X⦄, raw x = raw y → f x = f y := by
    intro x y hxy
    by_cases hx : x ∈ Set.range pick
    · by_cases hy : y ∈ Set.range pick
      · have hi : Classical.choose hx = Classical.choose hy := by
          apply Sum.inr_injective
          simpa only [raw, dif_pos hx, dif_pos hy] using hxy
        have hpoint : x = y :=
          (Classical.choose_spec hx).symm.trans
            ((congrArg pick hi).trans (Classical.choose_spec hy))
        exact congrArg f hpoint
      · have hbad : Sum.inr (Classical.choose hx) = Sum.inl (q y) := by
          simpa only [raw, dif_pos hx, dif_neg hy] using hxy
        exact False.elim (Sum.inr_ne_inl hbad)
    · by_cases hy : y ∈ Set.range pick
      · have hbad : Sum.inl (q x) = Sum.inr (Classical.choose hy) := by
          simpa only [raw, dif_neg hx, dif_pos hy] using hxy
        exact False.elim (Sum.inl_ne_inr hbad)
      · have hqxy : q x = q y := by
          apply Sum.inl_injective
          simpa only [raw, dif_neg hx, dif_neg hy] using hxy
        exact congrArg Subtype.val hqxy
  have hsumCard : Fintype.card (R ⊕ Fin (k - Nat.card R)) = k := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    rw [← Nat.card_eq_fintype_card]
    rw [hR]
    omega
  let e : R ⊕ Fin (k - Nat.card R) ≃ Fin k :=
    Fintype.equivOfCardEq (by simpa using hsumCard)
  let g : X → Fin k := fun x => e (raw x)
  refine ⟨g, ?_, ?_⟩
  · intro j
    obtain ⟨x, hx⟩ := hraw_surj (e.symm j)
    refine ⟨x, ?_⟩
    simp only [g, hx, Equiv.apply_symm_apply]
  · intro x y hxy
    apply hraw_refines
    exact e.injective hxy

end Green25Fractional

end

/- ## Part: `fractional_dyadic` -/

section

/- Exact normalization and the unconditional dyadic `23/40` construction. -/

namespace Green25Fractional

/-- The normalization exponent is exact: five 8-bit blocks contribute
`40m` input bits and the remaining `23m/16` exponent is precisely cancelled
by the number of colors. -/
theorem decay8_scale_factor (m : ℕ) :
    (((2 : ℝ) ^ (663 / 80 : ℝ)) ^ (5 * m : ℕ)) =
      ((2 ^ (40 * m) : ℕ) : ℝ) *
        (((2 ^ (23 * m) : ℕ) : ℝ) ^ (1 / 16 : ℝ)) := by
  have h40 : ((2 ^ (40 * m) : ℕ) : ℝ) = (2 : ℝ) ^ (40 * m : ℕ) := by
    norm_num
  have h23 : ((2 ^ (23 * m) : ℕ) : ℝ) = (2 : ℝ) ^ (23 * m : ℕ) := by
    norm_num
  rw [h40, h23]
  calc
    (((2 : ℝ) ^ (663 / 80 : ℝ)) ^ (5 * m : ℕ)) =
        (2 : ℝ) ^ ((663 / 80 : ℝ) * ((5 * m : ℕ) : ℝ)) := by
      rw [Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
    _ = (2 : ℝ) ^ (((40 * m : ℕ) : ℝ) +
        ((23 * m : ℕ) : ℝ) * (1 / 16 : ℝ)) := by
      congr 1
      push_cast
      ring
    _ = (2 : ℝ) ^ (((40 * m : ℕ) : ℝ)) *
        (2 : ℝ) ^ (((23 * m : ℕ) : ℝ) * (1 / 16 : ℝ)) :=
      Real.rpow_add (by norm_num : (0 : ℝ) < 2) _ _
    _ = (2 : ℝ) ^ (40 * m : ℕ) *
        (((2 : ℝ) ^ (23 * m : ℕ)) ^ (1 / 16 : ℝ)) := by
      congr 1
      · exact Real.rpow_natCast 2 (40 * m)
      · rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
          Real.rpow_natCast]

/-- Rewrite the concrete scalar in the dyadic reduction as `2^(40m)` times
the certified decaying factor. -/
theorem block8_scalar_eq_scaled_decay (m : ℕ) :
    ((2 : ℝ) ^ (15 / 16 : ℝ) * blockCoeff 8 (1 / 16) ^ (5 * m)) /
        (((2 ^ (23 * m) : ℕ) : ℝ) ^ (1 / 16 : ℝ)) =
      ((2 ^ (40 * m) : ℕ) : ℝ) *
        ((2 : ℝ) ^ (15 / 16 : ℝ) * decay8 ^ (5 * m)) := by
  have hexp :
      (8 + 8 * (1 / 16 : ℝ) * (23 / 40 : ℝ)) = 663 / 80 := by norm_num
  have hbase :
      blockCoeff 8 (1 / 16) = decay8 * (2 : ℝ) ^ (663 / 80 : ℝ) := by
    unfold decay8
    rw [hexp]
    field_simp
  rw [hbase, mul_pow, decay8_scale_factor]
  have hden : (0 : ℝ) < (((2 ^ (23 * m) : ℕ) : ℝ) ^ (1 / 16 : ℝ)) :=
    Real.rpow_pos_of_pos (by positivity) _
  field_simp

/-- The concrete scalar inequality required by the dyadic construction holds
from the explicit threshold onward. -/
theorem block8_scalar_small {m : ℕ} (hm : 64000 ≤ m) :
    ((2 : ℝ) ^ (15 / 16 : ℝ) * blockCoeff 8 (1 / 16) ^ (5 * m)) /
          (((2 ^ (23 * m) : ℕ) : ℝ) ^ (1 / 16 : ℝ)) <
        (2 ^ (40 * m - 4) : ℕ) := by
  have hn : 4 ≤ 40 * m := by omega
  have hpowNat : 2 ^ (40 * m - 4) * 2 ^ 4 = 2 ^ (40 * m) :=
    pow_sub_mul_pow 2 hn
  have hcast : ((2 ^ (40 * m - 4) : ℕ) : ℝ) =
      ((2 ^ (40 * m) : ℕ) : ℝ) * (1 / 16 : ℝ) := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) hpowNat
    norm_num at h ⊢
    linarith
  rw [block8_scalar_eq_scaled_decay, hcast]
  exact mul_lt_mul_of_pos_left (decay8_scaled_small hm) (by positivity)

/-- Unconditional dyadic `23/40` construction at all explicit large block
indices. -/
theorem exists_large_dyadic_collision_coloring {m : ℕ} (hm : 64000 ≤ m) :
    ∃ H : LinearColoring (40 * m) (23 * m),
      (collisionSumFinset (40 * m) (23 * m) H).card < 2 ^ (40 * m - 4) :=
  exists_block8_collision_coloring m (block8_scalar_small hm)

/-- Colors which are actually used by a linear coloring. -/
noncomputable def usedColorFinset (d t : ℕ) (H : LinearColoring d t) :
    Finset (F2Word t) := by
  classical
  exact Finset.univ.image fun x : BitWord d => H (boolToF2Word x)

theorem usedColorFinset_card_le (d t : ℕ) (H : LinearColoring d t) :
    (usedColorFinset d t H).card ≤ 2 ^ t := by
  calc
    (usedColorFinset d t H).card ≤ Fintype.card (F2Word t) :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = 2 ^ t := by
      rw [← Nat.card_eq_fintype_card]
      exact f2Word_card t

/-- Dyadic construction packaged with both its number of nonempty colors and
its actual same-color restricted-sum bound. -/
theorem exists_large_dyadic_coloring_data {m : ℕ} (hm : 64000 ≤ m) :
    ∃ H : LinearColoring (40 * m) (23 * m),
      (usedColorFinset (40 * m) (23 * m) H).card ≤ 2 ^ (23 * m) ∧
      (collisionSumFinset (40 * m) (23 * m) H).card < 2 ^ (40 * m - 4) := by
  obtain ⟨H, hH⟩ := exists_large_dyadic_collision_coloring hm
  exact ⟨H, usedColorFinset_card_le _ _ H, hH⟩

/-- A sum realized by two distinct points in one fiber of an arbitrary
finite coloring. -/
def FiberSameColorSum {d : ℕ} {K : Type*} (g : BitWord d → K) (s : ℕ) : Prop :=
  ∃ x y : BitWord d, x ≠ y ∧ g x = g y ∧
    binaryValue x + binaryValue y = s

/-- The actual restricted-sum union for an arbitrary coloring of the binary
cube. -/
noncomputable def fiberCollisionSumFinset {K : Type*}
    (d : ℕ) (g : BitWord d → K) : Finset (CandidateSum d) := by
  classical
  exact Finset.univ.filter fun s => FiberSameColorSum g (s : ℕ)

/-- Refining color classes cannot create a new monochromatic restricted sum. -/
theorem fiberCollisionSumFinset_subset_of_refines {d t : ℕ} {K : Type*}
    (H : LinearColoring d t) (g : BitWord d → K)
    (hrefines : ∀ ⦃x y : BitWord d⦄, g x = g y →
      H (boolToF2Word x) = H (boolToF2Word y)) :
    fiberCollisionSumFinset d g ⊆ collisionSumFinset d t H := by
  classical
  intro s hs
  simp only [fiberCollisionSumFinset, collisionSumFinset, Finset.mem_filter,
    Finset.mem_univ, true_and] at hs ⊢
  rcases hs with ⟨x, y, hxy, hcolor, hsum⟩
  exact ⟨x, y, hxy, hrefines hcolor, hsum⟩

/-- For every explicit large dyadic block, the construction can be made to
use exactly `2^(23m)` nonempty colors, without weakening its collision-sum
bound. -/
theorem exists_large_dyadic_exact_coloring {m : ℕ} (hm : 64000 ≤ m) :
    ∃ g : BitWord (40 * m) → Fin (2 ^ (23 * m)),
      Function.Surjective g ∧
      (fiberCollisionSumFinset (40 * m) g).card < 2 ^ (40 * m - 4) := by
  obtain ⟨H, hH⟩ := exists_large_dyadic_collision_coloring hm
  let f : BitWord (40 * m) → F2Word (23 * m) :=
    fun x => H (boolToF2Word x)
  have hused : Nat.card (Set.range f) ≤ 2 ^ (23 * m) := by
    calc
      Nat.card (Set.range f) ≤ Nat.card (F2Word (23 * m)) :=
        Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
      _ = 2 ^ (23 * m) := f2Word_card (23 * m)
  have hdomain : Nat.card (BitWord (40 * m)) = 2 ^ (40 * m) := by
    rw [Nat.card_eq_fintype_card]
    simp [BitWord]
  have hk : 2 ^ (23 * m) ≤ Nat.card (BitWord (40 * m)) := by
    rw [hdomain]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨g, hsurj, hrefines⟩ :=
    exists_surjective_refinement f (2 ^ (23 * m)) hused hk
  refine ⟨g, hsurj, ?_⟩
  exact (Finset.card_le_card
    (fiberCollisionSumFinset_subset_of_refines H g hrefines)).trans_lt hH

end Green25Fractional

end

/- ## Part: `fractional_interval` -/

section

/- Transport the exact dyadic coloring from bit words to the interval
`{1, ..., 2^d}`. -/

namespace Green25Fractional

/-- Binary evaluation, with its sharp range proof bundled into `Fin`. -/
def binaryValueFin {d : ℕ} (w : BitWord d) : Fin (2 ^ d) :=
  ⟨binaryValue w, binaryValue_lt_two_pow w⟩

theorem binaryValueFin_bijective (d : ℕ) :
    Function.Bijective (@binaryValueFin d) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro x y h
    exact binaryValue_injective d (congrArg Fin.val h)
  · simp [BitWord]

/-- Canonical equivalence between `d`-bit words and integers below `2^d`. -/
noncomputable def binaryValueEquiv (d : ℕ) : BitWord d ≃ Fin (2 ^ d) :=
  Equiv.ofBijective binaryValueFin (binaryValueFin_bijective d)

@[simp] theorem binaryValueEquiv_apply {d : ℕ} (w : BitWord d) :
    binaryValueEquiv d w = binaryValueFin w := rfl

/-- A restricted monochromatic sum after indexing `Fin N` as the interval
`{1, ..., N}`. -/
def FinIntervalSameColorSum {N : ℕ} {K : Type*}
    (g : Fin N → K) (s : ℕ) : Prop :=
  ∃ x y : Fin N, x ≠ y ∧ g x = g y ∧
    (x : ℕ) + 1 + ((y : ℕ) + 1) = s

/-- All restricted monochromatic sums of an interval coloring. -/
noncomputable def finIntervalCollisionSumFinset {K : Type*}
    (N : ℕ) (g : Fin N → K) : Finset (Fin (2 * N + 2)) := by
  classical
  exact Finset.univ.filter fun s => FinIntervalSameColorSum g (s : ℕ)

/-- Adding one to each endpoint shifts a binary-cube sum by exactly two. -/
def shiftCandidate (d : ℕ) (s : CandidateSum d) : Fin (2 * 2 ^ d + 2) :=
  ⟨(s : ℕ) + 2, by
    have hs := s.isLt
    have hs' : (s : ℕ) < 2 * 2 ^ d := by
      calc
        (s : ℕ) < 2 ^ (d + 1) := hs
        _ = 2 * 2 ^ d := by rw [pow_succ]; omega
    omega⟩

theorem shiftCandidate_injective (d : ℕ) :
    Function.Injective (shiftCandidate d) := by
  intro s t h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [shiftCandidate] at this
  omega

/-- The interval sums of the transported coloring inject into the shifted
binary-cube collision sums. -/
theorem finIntervalCollisionSumFinset_subset_shift {d k : ℕ}
    (g : BitWord d → Fin k) :
    finIntervalCollisionSumFinset (2 ^ d)
        (fun i => g ((binaryValueEquiv d).symm i)) ⊆
      (fiberCollisionSumFinset d g).image (shiftCandidate d) := by
  classical
  intro s hs
  simp only [finIntervalCollisionSumFinset, Finset.mem_filter,
    Finset.mem_univ, true_and] at hs
  rcases hs with ⟨x, y, hxy, hcolor, hsum⟩
  let wx : BitWord d := (binaryValueEquiv d).symm x
  let wy : BitWord d := (binaryValueEquiv d).symm y
  have hxval : binaryValue wx = (x : ℕ) := by
    have h := congrArg Fin.val ((binaryValueEquiv d).apply_symm_apply x)
    simpa only [binaryValueEquiv_apply, binaryValueFin] using h
  have hyval : binaryValue wy = (y : ℕ) := by
    have h := congrArg Fin.val ((binaryValueEquiv d).apply_symm_apply y)
    simpa only [binaryValueEquiv_apply, binaryValueFin] using h
  have hword : wx ≠ wy := by
    intro h
    apply hxy
    exact (binaryValueEquiv d).symm.injective h
  let old : CandidateSum d :=
    ⟨binaryValue wx + binaryValue wy, by
      have hx := binaryValue_lt_two_pow wx
      have hy := binaryValue_lt_two_pow wy
      rw [pow_succ]
      omega⟩
  have hold : old ∈ fiberCollisionSumFinset d g := by
    simp only [fiberCollisionSumFinset, Finset.mem_filter, Finset.mem_univ,
      true_and]
    refine ⟨wx, wy, hword, ?_, rfl⟩
    simpa only [wx, wy] using hcolor
  refine Finset.mem_image.mpr ⟨old, hold, ?_⟩
  apply Fin.ext
  simp only [shiftCandidate, old]
  omega

/-- Exact-color interval form of the dyadic construction.  The interval has
`N = 2^(40m)` points, all `N^(23/40) = 2^(23m)` colors are nonempty, and
fewer than `N/16` restricted monochromatic sums occur. -/
theorem exists_large_dyadic_exact_interval_coloring {m : ℕ} (hm : 64000 ≤ m) :
    ∃ g : Fin (2 ^ (40 * m)) → Fin (2 ^ (23 * m)),
      Function.Surjective g ∧
      (finIntervalCollisionSumFinset (2 ^ (40 * m)) g).card <
        2 ^ (40 * m - 4) := by
  obtain ⟨g, hsurj, hsum⟩ := exists_large_dyadic_exact_coloring hm
  let e := binaryValueEquiv (40 * m)
  let g' : Fin (2 ^ (40 * m)) → Fin (2 ^ (23 * m)) :=
    fun i => g (e.symm i)
  have hsurj' : Function.Surjective g' := by
    intro c
    obtain ⟨w, hw⟩ := hsurj c
    exact ⟨e w, by simpa only [g', e, Equiv.symm_apply_apply] using hw⟩
  refine ⟨g', hsurj', ?_⟩
  calc
    (finIntervalCollisionSumFinset (2 ^ (40 * m)) g').card ≤
        ((fiberCollisionSumFinset (40 * m) g).image
          (shiftCandidate (40 * m))).card :=
      Finset.card_le_card (by
        simpa only [g', e] using
          finIntervalCollisionSumFinset_subset_shift g)
    _ ≤ (fiberCollisionSumFinset (40 * m) g).card := Finset.card_image_le
    _ < 2 ^ (40 * m - 4) := hsum

end Green25Fractional

end

/- ## Part: `fractional_finpartition` -/

section

/- Package a surjective interval coloring as a `Finpartition`. -/

namespace Green25Fractional

open Finset

/-- The interval point corresponding to an index in `Fin N`. -/
def finSucc {N : ℕ} (x : Fin N) : ℕ := (x : ℕ) + 1

theorem finSucc_injective {N : ℕ} :
    Function.Injective (@finSucc N) := by
  intro x y h
  apply Fin.ext
  simp only [finSucc] at h
  omega

theorem finSucc_mem_Icc {N : ℕ} (x : Fin N) :
    finSucc x ∈ Icc 1 N := by
  simp only [mem_Icc, finSucc]
  omega

theorem exists_finSucc_of_mem_Icc {N a : ℕ} (ha : a ∈ Icc 1 N) :
    ∃ x : Fin N, finSucc x = a := by
  simp only [mem_Icc] at ha
  let x : Fin N := ⟨a - 1, by omega⟩
  exact ⟨x, by simp only [finSucc, x]; omega⟩

/-- One color class, represented as a finset in `{1, ..., N}`. -/
noncomputable def intervalFiber {N k : ℕ} (g : Fin N → Fin k) (c : Fin k) :
    Finset ℕ := by
  classical
  exact (Finset.univ.filter fun x => g x = c).image finSucc

theorem mem_intervalFiber {N k : ℕ} (g : Fin N → Fin k) (c : Fin k) (a : ℕ) :
    a ∈ intervalFiber g c ↔
      ∃ x : Fin N, g x = c ∧ finSucc x = a := by
  classical
  simp [intervalFiber]

theorem intervalFiber_subset_Icc {N k : ℕ} (g : Fin N → Fin k) (c : Fin k) :
    intervalFiber g c ⊆ Icc 1 N := by
  intro a ha
  obtain ⟨x, -, rfl⟩ := (mem_intervalFiber g c a).mp ha
  exact finSucc_mem_Icc x

theorem intervalFiber_nonempty {N k : ℕ} (g : Fin N → Fin k)
    (hsurj : Function.Surjective g) (c : Fin k) :
    (intervalFiber g c).Nonempty := by
  obtain ⟨x, hx⟩ := hsurj c
  exact ⟨finSucc x, (mem_intervalFiber g c _).mpr ⟨x, hx, rfl⟩⟩

theorem intervalFiber_injective {N k : ℕ} (g : Fin N → Fin k)
    (hsurj : Function.Surjective g) :
    Function.Injective (intervalFiber g) := by
  intro c d hcd
  obtain ⟨x, hx⟩ := hsurj c
  have hmemc : finSucc x ∈ intervalFiber g c :=
    (mem_intervalFiber g c _).mpr ⟨x, hx, rfl⟩
  have hmemd : finSucc x ∈ intervalFiber g d := by
    rw [← hcd]
    exact hmemc
  obtain ⟨y, hy, hyx⟩ := (mem_intervalFiber g d _).mp hmemd
  have heq : y = x := finSucc_injective hyx
  calc
    c = g x := hx.symm
    _ = g y := congrArg g heq.symm
    _ = d := hy

/-- The partition into the nonempty fibers of a surjective coloring. -/
noncomputable def intervalFinpartition {N k : ℕ} (g : Fin N → Fin k)
    (hsurj : Function.Surjective g) : Finpartition (Icc 1 N) := by
  classical
  let parts : Finset (Finset ℕ) := Finset.univ.image (intervalFiber g)
  apply Finpartition.ofExistsUnique parts
  · intro p hp
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hp
    exact intervalFiber_subset_Icc g c
  · intro a ha
    obtain ⟨x, hx⟩ := exists_finSucc_of_mem_Icc ha
    refine ⟨intervalFiber g (g x), ?_, ?_⟩
    · exact ⟨Finset.mem_image.mpr ⟨g x, Finset.mem_univ _, rfl⟩,
        (mem_intervalFiber g (g x) _).mpr ⟨x, rfl, hx⟩⟩
    · intro t ht
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp ht.1
      obtain ⟨y, hy, hya⟩ := (mem_intervalFiber g c a).mp ht.2
      have hyx : y = x := finSucc_injective (hya.trans hx.symm)
      have hc : c = g x := hy.symm.trans (congrArg g hyx)
      exact congrArg (intervalFiber g) hc
  · intro hempty
    obtain ⟨c, -, hc⟩ := Finset.mem_image.mp hempty
    have hcne := intervalFiber_nonempty g hsurj c
    rw [hc] at hcne
    exact Finset.not_nonempty_empty hcne

@[simp] theorem intervalFinpartition_parts {N k : ℕ} (g : Fin N → Fin k)
    (hsurj : Function.Surjective g) :
    (intervalFinpartition g hsurj).parts =
      Finset.univ.image (intervalFiber g) := rfl

theorem intervalFinpartition_card_parts {N k : ℕ} (g : Fin N → Fin k)
    (hsurj : Function.Surjective g) :
    (intervalFinpartition g hsurj).parts.card = k := by
  rw [intervalFinpartition_parts,
    Finset.card_image_of_injective _ (intervalFiber_injective g hsurj),
    Finset.card_univ, Fintype.card_fin]

end Green25Fractional

end

/- ## Part: `fractional_fc_bridge` -/

section

/- Connect the exact dyadic construction to the current Formal Conjectures
definition of Green 25. -/

namespace Green25Fractional

open Finset

/-- Forget the bounded-value wrapper on the interval collision sums. -/
noncomputable def intervalCollisionValues {N k : ℕ} (g : Fin N → Fin k) :
    Finset ℕ := by
  classical
  exact (finIntervalCollisionSumFinset N g).image Fin.val

theorem intervalCollisionValues_card {N k : ℕ} (g : Fin N → Fin k) :
    (intervalCollisionValues g).card =
      (finIntervalCollisionSumFinset N g).card := by
  classical
  exact Finset.card_image_of_injective _ Fin.val_injective

/-- Every restricted sum in a color-class part is one of the collision sums
counted by the interval model. -/
theorem finpartition_restrictedSumset_subset_collisionValues
    {N k : ℕ} (g : Fin N → Fin k) (hsurj : Function.Surjective g) :
    (intervalFinpartition g hsurj).parts.biUnion Finset.restrictedSumset ⊆
      intervalCollisionValues g := by
  classical
  intro s hs
  rw [Finset.mem_biUnion] at hs
  obtain ⟨A, hAP, hsA⟩ := hs
  rw [intervalFinpartition_parts] at hAP
  obtain ⟨c, -, hcA⟩ := Finset.mem_image.mp hAP
  subst A
  rw [Finset.restrictedSumset, Finset.mem_image] at hsA
  obtain ⟨p, hp, hpsum⟩ := hsA
  have hp' := Finset.mem_offDiag.mp hp
  obtain ⟨x, hxc, hxval⟩ :=
    (mem_intervalFiber g c p.1).mp hp'.1
  obtain ⟨y, hyc, hyval⟩ :=
    (mem_intervalFiber g c p.2).mp hp'.2.1
  have hxy : x ≠ y := by
    intro h
    apply hp'.2.2
    calc
      p.1 = finSucc x := hxval.symm
      _ = finSucc y := congrArg finSucc h
      _ = p.2 := hyval
  have hcolor : g x = g y := hxc.trans hyc.symm
  have hsum : (x : ℕ) + 1 + ((y : ℕ) + 1) = s := by
    simpa only [finSucc] using
      (congrArg₂ (· + ·) hxval hyval).trans hpsum
  have hsBound : s < 2 * N + 2 := by
    have hxN := x.isLt
    have hyN := y.isLt
    omega
  let sf : Fin (2 * N + 2) := ⟨s, hsBound⟩
  have hsf : sf ∈ finIntervalCollisionSumFinset N g := by
    simp only [finIntervalCollisionSumFinset, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨x, y, hxy, hcolor, hsum⟩
  exact Finset.mem_image.mpr ⟨sf, hsf, rfl⟩

/-- The FC restricted-sum union is bounded by the collision finset used in
the probabilistic construction. -/
theorem finpartition_restrictedSumset_card_le {N k : ℕ}
    (g : Fin N → Fin k) (hsurj : Function.Surjective g) :
    ((intervalFinpartition g hsurj).parts.biUnion
      Finset.restrictedSumset).card ≤
      (finIntervalCollisionSumFinset N g).card := by
  calc
    ((intervalFinpartition g hsurj).parts.biUnion
      Finset.restrictedSumset).card ≤ (intervalCollisionValues g).card :=
        Finset.card_le_card
          (finpartition_restrictedSumset_subset_collisionValues g hsurj)
    _ = (finIntervalCollisionSumFinset N g).card := intervalCollisionValues_card g

/-- A genuine FC `Finpartition` counterexample on every sufficiently large
member of the dyadic subsequence. -/
theorem exists_large_dyadic_finpartition_counterexample
    {m : ℕ} (hm : 64000 ≤ m) :
    ∃ P : Finpartition (Icc 1 (2 ^ (40 * m))),
      P.parts.card = 2 ^ (23 * m) ∧
      (P.parts.biUnion Finset.restrictedSumset).card <
        2 ^ (40 * m - 4) := by
  obtain ⟨g, hsurj, hsmall⟩ :=
    exists_large_dyadic_exact_interval_coloring hm
  let P := intervalFinpartition g hsurj
  refine ⟨P, intervalFinpartition_card_parts g hsurj, ?_⟩
  exact (finpartition_restrictedSumset_card_le g hsurj).trans_lt hsmall

/-- Directly in the current Formal Conjectures predicate: at the dyadic
sizes `N = 2^(40m)`, `k = 2^(23m)` fails `Property25`. -/
theorem not_property25_large_dyadic {m : ℕ} (hm : 64000 ≤ m) :
    ¬ Green25.Property25 (2 ^ (23 * m)) (2 ^ (40 * m)) := by
  obtain ⟨P, hparts, hsmall⟩ :=
    exists_large_dyadic_finpartition_counterexample hm
  intro hproperty
  have hlower := hproperty.2.2 P hparts
  have hfour : 4 ≤ 40 * m := by omega
  have hscale : 2 ^ (40 * m - 4) * 16 = 2 ^ (40 * m) := by
    have h := pow_sub_mul_pow 2 hfour
    norm_num at h ⊢
    exact h
  omega

end Green25Fractional

end

/- ## Part: `fractional_restrict` -/

section

/- Restrict an interval coloring and then split its fibers to recover an
exact prescribed number of nonempty colors. -/

namespace Green25Fractional

/-- Restriction from an interval of length `M` to its first `N` points. -/
def restrictIntervalColor {N M k : ℕ} (hNM : N ≤ M)
    (g : Fin M → Fin k) : Fin N → Fin k :=
  fun x => g (Fin.castLE hNM x)

/-- Splitting color classes cannot create interval collision sums. -/
theorem finIntervalCollisionSumFinset_subset_of_refines
    {N k ell : ℕ} (old : Fin N → Fin k) (new : Fin N → Fin ell)
    (hrefines : ∀ ⦃x y : Fin N⦄, new x = new y → old x = old y) :
    finIntervalCollisionSumFinset N new ⊆
      finIntervalCollisionSumFinset N old := by
  classical
  intro s hs
  simp only [finIntervalCollisionSumFinset, Finset.mem_filter,
    Finset.mem_univ, true_and] at hs ⊢
  rcases hs with ⟨x, y, hxy, hcolor, hsum⟩
  exact ⟨x, y, hxy, hrefines hcolor, hsum⟩

/-- Restricting to the first `N` points cannot create a new numerical sum. -/
theorem intervalCollisionValues_restrict_subset
    {N M k : ℕ} (hNM : N ≤ M) (g : Fin M → Fin k) :
    intervalCollisionValues (restrictIntervalColor hNM g) ⊆
      intervalCollisionValues g := by
  classical
  intro s hs
  rw [intervalCollisionValues, Finset.mem_image] at hs ⊢
  obtain ⟨sf, hsf, hsval⟩ := hs
  simp only [finIntervalCollisionSumFinset, Finset.mem_filter,
    Finset.mem_univ, true_and] at hsf
  rcases hsf with ⟨x, y, hxy, hcolor, hsum⟩
  let x' : Fin M := Fin.castLE hNM x
  let y' : Fin M := Fin.castLE hNM y
  have hxy' : x' ≠ y' := by
    intro h
    apply hxy
    apply Fin.ext
    simpa only [x', y', Fin.castLE] using congrArg Fin.val h
  have hcolor' : g x' = g y' := by
    simpa only [restrictIntervalColor, x', y'] using hcolor
  have hsum' : (x' : ℕ) + 1 + ((y' : ℕ) + 1) = s := by
    have hsfeq : (sf : ℕ) = s := hsval
    simpa only [x', y', Fin.castLE] using hsum.trans hsfeq
  have hsBound : s < 2 * M + 2 := by
    have hxM := x'.isLt
    have hyM := y'.isLt
    omega
  let sf' : Fin (2 * M + 2) := ⟨s, hsBound⟩
  refine ⟨sf', ?_, rfl⟩
  simp only [finIntervalCollisionSumFinset, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact ⟨x', y', hxy', hcolor', hsum'⟩

/-- Generic all-interval reduction.  If the old coloring has `k` available
colors, then on any prefix of length `N` one may use exactly `ell` nonempty
colors whenever `k ≤ ell ≤ N`, while keeping no more collision sums than the
old coloring. -/
theorem exists_exact_restriction_refinement
    {N M k ell : ℕ} (hNM : N ≤ M) (g : Fin M → Fin k)
    (hkell : k ≤ ell) (hellN : ell ≤ N) :
    ∃ new : Fin N → Fin ell, Function.Surjective new ∧
      (finIntervalCollisionSumFinset N new).card ≤
        (finIntervalCollisionSumFinset M g).card := by
  let old : Fin N → Fin k := restrictIntervalColor hNM g
  have hused : Nat.card (Set.range old) ≤ ell := by
    calc
      Nat.card (Set.range old) ≤ Nat.card (Fin k) :=
        Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
      _ = k := by simp
      _ ≤ ell := hkell
  have hdomain : ell ≤ Nat.card (Fin N) := by simpa using hellN
  obtain ⟨new, hsurj, hrefines⟩ :=
    exists_surjective_refinement old ell hused hdomain
  refine ⟨new, hsurj, ?_⟩
  calc
    (finIntervalCollisionSumFinset N new).card =
        (intervalCollisionValues new).card :=
      (intervalCollisionValues_card new).symm
    _ ≤ (intervalCollisionValues old).card :=
      Finset.card_le_card (by
        intro s hs
        rw [intervalCollisionValues, Finset.mem_image] at hs ⊢
        obtain ⟨sf, hsf, rfl⟩ := hs
        exact ⟨sf,
          finIntervalCollisionSumFinset_subset_of_refines old new hrefines hsf,
          rfl⟩)
    _ ≤ (intervalCollisionValues g).card :=
      Finset.card_le_card (intervalCollisionValues_restrict_subset hNM g)
    _ = (finIntervalCollisionSumFinset M g).card :=
      intervalCollisionValues_card g

end Green25Fractional

end

/- ## Part: `fractional_general` -/

section

/- The combinatorial all-dimension pipeline.  Only one explicit scalar
inequality remains to instantiate it for a chosen interval size. -/

namespace Green25Fractional

/-- A conservative output-bit count for restricting a `2^d` coloring to an
arbitrary interval whose size is larger than `2^(d-1)`. -/
def targetBitCount (d : ℕ) : ℕ := 23 * (d - 1) / 40

theorem targetBitCount_bounds (d : ℕ) :
    40 * targetBitCount d ≤ 23 * (d - 1) ∧
      23 * (d - 1) < 40 * (targetBitCount d + 1) := by
  constructor
  · simpa only [targetBitCount, Nat.mul_comm] using
      Nat.div_mul_le_self (23 * (d - 1)) 40
  · simpa only [targetBitCount] using
      Nat.lt_mul_div_succ (23 * (d - 1)) (by norm_num : 0 < 40)

theorem targetBitCount_le (d : ℕ) : targetBitCount d ≤ d := by
  unfold targetBitCount
  rw [Nat.div_le_iff_le_mul_add_pred (by norm_num : 0 < 40)]
  omega

/-- Arbitrary numbers of complete 8-bit blocks and remainder bits. -/
theorem exists_block8_remainder_collision_coloring
    (ell r t B : ℕ)
    (hscalar :
      ((2 : ℝ) ^ (15 / 16 : ℝ) * blockCoeff 8 (1 / 16) ^ ell *
          (2 * (3 / 2 : ℝ) ^ (1 / 16 : ℝ)) ^ r) /
          (((2 ^ t : ℕ) : ℝ) ^ (1 / 16 : ℝ)) < B) :
    ∃ H : LinearColoring (8 * ell + r) t,
      (collisionSumFinset (8 * ell + r) t H).card < B := by
  apply exists_coloring_with_few_collision_sums
    (8 * ell + r) t B (1 / 16) (by norm_num) (by norm_num)
  have hb := representation_terminal_bound 8 ell r (1 / 16 : ℝ)
    (by norm_num) (by norm_num)
  rw [show (1 : ℝ) - 1 / 16 = 15 / 16 by norm_num] at hb
  exact (div_le_div_of_nonneg_right hb (by positivity)).trans_lt hscalar

/-- Under the same scalar estimate, all `2^t` colors can be made nonempty on
the binary cube, without increasing the collision set. -/
theorem exists_block8_remainder_exact_coloring
    (ell r t B : ℕ) (ht : t ≤ 8 * ell + r)
    (hscalar :
      ((2 : ℝ) ^ (15 / 16 : ℝ) * blockCoeff 8 (1 / 16) ^ ell *
          (2 * (3 / 2 : ℝ) ^ (1 / 16 : ℝ)) ^ r) /
          (((2 ^ t : ℕ) : ℝ) ^ (1 / 16 : ℝ)) < B) :
    ∃ g : BitWord (8 * ell + r) → Fin (2 ^ t),
      Function.Surjective g ∧
      (fiberCollisionSumFinset (8 * ell + r) g).card < B := by
  obtain ⟨H, hH⟩ :=
    exists_block8_remainder_collision_coloring ell r t B hscalar
  let f : BitWord (8 * ell + r) → F2Word t :=
    fun x => H (boolToF2Word x)
  have hused : Nat.card (Set.range f) ≤ 2 ^ t := by
    calc
      Nat.card (Set.range f) ≤ Nat.card (F2Word t) :=
        Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
      _ = 2 ^ t := f2Word_card t
  have hdomain : Nat.card (BitWord (8 * ell + r)) = 2 ^ (8 * ell + r) := by
    rw [Nat.card_eq_fintype_card]
    simp [BitWord]
  have hk : 2 ^ t ≤ Nat.card (BitWord (8 * ell + r)) := by
    rw [hdomain]
    exact Nat.pow_le_pow_right (by norm_num) ht
  obtain ⟨g, hsurj, hrefines⟩ :=
    exists_surjective_refinement f (2 ^ t) hused hk
  refine ⟨g, hsurj, ?_⟩
  exact (Finset.card_le_card
    (fiberCollisionSumFinset_subset_of_refines H g hrefines)).trans_lt hH

/-- Interval form of the arbitrary-dimension exact coloring. -/
theorem exists_block8_remainder_exact_interval_coloring
    (ell r t B : ℕ) (ht : t ≤ 8 * ell + r)
    (hscalar :
      ((2 : ℝ) ^ (15 / 16 : ℝ) * blockCoeff 8 (1 / 16) ^ ell *
          (2 * (3 / 2 : ℝ) ^ (1 / 16 : ℝ)) ^ r) /
          (((2 ^ t : ℕ) : ℝ) ^ (1 / 16 : ℝ)) < B) :
    ∃ g : Fin (2 ^ (8 * ell + r)) → Fin (2 ^ t),
      Function.Surjective g ∧
      (finIntervalCollisionSumFinset (2 ^ (8 * ell + r)) g).card < B := by
  obtain ⟨g, hsurj, hsum⟩ :=
    exists_block8_remainder_exact_coloring ell r t B ht hscalar
  let e := binaryValueEquiv (8 * ell + r)
  let g' : Fin (2 ^ (8 * ell + r)) → Fin (2 ^ t) :=
    fun i => g (e.symm i)
  have hsurj' : Function.Surjective g' := by
    intro c
    obtain ⟨w, hw⟩ := hsurj c
    exact ⟨e w, by simpa only [g', e, Equiv.symm_apply_apply] using hw⟩
  refine ⟨g', hsurj', ?_⟩
  calc
    (finIntervalCollisionSumFinset (2 ^ (8 * ell + r)) g').card ≤
        ((fiberCollisionSumFinset (8 * ell + r) g).image
          (shiftCandidate (8 * ell + r))).card :=
      Finset.card_le_card (by
        simpa only [g', e] using
          finIntervalCollisionSumFinset_subset_shift g)
    _ ≤ (fiberCollisionSumFinset (8 * ell + r) g).card := Finset.card_image_le
    _ < B := hsum

/-- Once the analytic estimate is known on a containing binary interval, the
already-proved restriction/refinement layer gives exactly `K` nonempty colors
on the desired prefix. -/
theorem exists_exact_prefix_coloring_of_scalar
    (ell r t B N K : ℕ)
    (ht : t ≤ 8 * ell + r)
    (hN : N ≤ 2 ^ (8 * ell + r))
    (hcolors : 2 ^ t ≤ K) (hKN : K ≤ N)
    (hscalar :
      ((2 : ℝ) ^ (15 / 16 : ℝ) * blockCoeff 8 (1 / 16) ^ ell *
          (2 * (3 / 2 : ℝ) ^ (1 / 16 : ℝ)) ^ r) /
          (((2 ^ t : ℕ) : ℝ) ^ (1 / 16 : ℝ)) < B) :
    ∃ g : Fin N → Fin K, Function.Surjective g ∧
      (finIntervalCollisionSumFinset N g).card < B := by
  obtain ⟨old, -, hold⟩ :=
    exists_block8_remainder_exact_interval_coloring ell r t B ht hscalar
  obtain ⟨new, hsurj, hle⟩ :=
    exists_exact_restriction_refinement hN old hcolors hKN
  exact ⟨new, hsurj, hle.trans_lt hold⟩

end Green25Fractional

end

/- ## Part: `fractional_allN_scalar` -/

section

/- Explicit control of the scalar estimate for arbitrary binary dimensions. -/

namespace Green25Fractional

set_option exponentiation.threshold 20000

/-- The floor in `targetBitCount` costs less than one output bit.  After
clearing denominators, this is exactly the exponent comparison needed below. -/
theorem targetBitCount_scale_nat (ell r : ℕ) :
    5304 * ell ≤
      40 * targetBitCount (8 * ell + r) + 640 * ((8 * ell + r) + 1) := by
  have hround := (targetBitCount_bounds (8 * ell + r)).2
  generalize targetBitCount (8 * ell + r) = t at hround ⊢
  omega

/-- Real-exponent form of `targetBitCount_scale_nat`. -/
theorem targetBitCount_scale_real (ell r : ℕ) :
    (663 / 80 : ℝ) * (ell : ℝ) ≤
      (targetBitCount (8 * ell + r) : ℝ) * (1 / 16 : ℝ) +
        (((8 * ell + r) + 1 : ℕ) : ℝ) := by
  have h := targetBitCount_scale_nat ell r
  have hcast : ((5304 * ell : ℕ) : ℝ) ≤
      ((40 * targetBitCount (8 * ell + r) +
        640 * ((8 * ell + r) + 1) : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast at hcast
  norm_num at hcast ⊢
  linarith

/-- The large power inside the 8-bit block coefficient is cancelled by the
chosen number of colors, up to one harmless input bit. -/
theorem block8_scale_ratio_le (ell r : ℕ) :
    (((2 : ℝ) ^ (663 / 80 : ℝ)) ^ ell) /
        (((2 ^ targetBitCount (8 * ell + r) : ℕ) : ℝ) ^ (1 / 16 : ℝ)) ≤
      ((2 ^ ((8 * ell + r) + 1) : ℕ) : ℝ) := by
  let t := targetBitCount (8 * ell + r)
  let d := 8 * ell + r
  have hexp : (663 / 80 : ℝ) * (ell : ℝ) ≤
      (((d + 1 : ℕ) : ℝ)) + (t : ℝ) * (1 / 16 : ℝ) := by
    simpa only [t, d, add_comm] using targetBitCount_scale_real ell r
  have hmono := Real.rpow_le_rpow_of_exponent_le
    (by norm_num : (1 : ℝ) ≤ 2) hexp
  have hnum : (((2 : ℝ) ^ (663 / 80 : ℝ)) ^ ell) =
      (2 : ℝ) ^ ((663 / 80 : ℝ) * (ell : ℝ)) := by
    exact (Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2) _ ell).symm
  have hden : (((2 ^ t : ℕ) : ℝ) ^ (1 / 16 : ℝ)) =
      (2 : ℝ) ^ ((t : ℝ) * (1 / 16 : ℝ)) := by
    calc
      (((2 ^ t : ℕ) : ℝ) ^ (1 / 16 : ℝ)) =
          (((2 : ℝ) ^ (t : ℕ)) ^ (1 / 16 : ℝ)) := by norm_num
      _ = (((2 : ℝ) ^ (t : ℝ)) ^ (1 / 16 : ℝ)) := by
        rw [Real.rpow_natCast]
      _ = (2 : ℝ) ^ ((t : ℝ) * (1 / 16 : ℝ)) := by
        rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hrhs : ((2 ^ (d + 1) : ℕ) : ℝ) =
      (2 : ℝ) ^ (((d + 1 : ℕ) : ℝ)) := by
    calc
      ((2 ^ (d + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (d + 1 : ℕ) := by norm_num
      _ = (2 : ℝ) ^ (((d + 1 : ℕ) : ℝ)) :=
        (Real.rpow_natCast 2 (d + 1)).symm
  have hdenpos : 0 < (2 : ℝ) ^ ((t : ℝ) * (1 / 16 : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  rw [show targetBitCount (8 * ell + r) = t by rfl,
    show 8 * ell + r = d by rfl, hnum, hden, hrhs]
  rw [div_le_iff₀ hdenpos, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  exact hmono

/-- At most seven remainder bits contribute less than `2^12`. -/
theorem remainder_factor_lt (r : ℕ) (hr : r < 8) :
    (2 * (3 / 2 : ℝ) ^ (1 / 16 : ℝ)) ^ r < 4096 := by
  have hroot : (3 / 2 : ℝ) ^ (1 / 16 : ℝ) < 3 / 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 3 / 2)
        (by norm_num : (1 / 16 : ℝ) < 1)
  have hbase : 0 ≤ 2 * (3 / 2 : ℝ) ^ (1 / 16 : ℝ) := by positivity
  have hbasele : 2 * (3 / 2 : ℝ) ^ (1 / 16 : ℝ) ≤ 3 := by
    linarith
  calc
    (2 * (3 / 2 : ℝ) ^ (1 / 16 : ℝ)) ^ r ≤ (3 : ℝ) ^ r :=
      pow_le_pow_left₀ hbase hbasele r
    _ ≤ (3 : ℝ) ^ 7 :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (by omega)
    _ < 4096 := by norm_num

/-- The arbitrary-dimension scalar estimate.  The threshold is conservative:
it spends four certified contraction batches to absorb all floor and remainder
constants. -/
theorem block8_remainder_scalar_small {ell r : ℕ}
    (hell : 1280000 ≤ ell) (hr : r < 8) :
    ((2 : ℝ) ^ (15 / 16 : ℝ) * blockCoeff 8 (1 / 16) ^ ell *
        (2 * (3 / 2 : ℝ) ^ (1 / 16 : ℝ)) ^ r) /
        (((2 ^ targetBitCount (8 * ell + r) : ℕ) : ℝ) ^ (1 / 16 : ℝ)) <
      (2 ^ ((8 * ell + r) - 6) : ℕ) := by
  let d := 8 * ell + r
  let t := targetBitCount d
  have hd6 : 6 ≤ d := by simp only [d]; omega
  have hlead : (2 : ℝ) ^ (15 / 16 : ℝ) < 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
        (by norm_num : (15 / 16 : ℝ) < 1)
  have hdecay : decay8 ^ ell < 1 / 1048576 := decay8_pow_very_small hell
  have hrem : (2 * (3 / 2 : ℝ) ^ (1 / 16 : ℝ)) ^ r < 4096 :=
    remainder_factor_lt r hr
  have hscale : (((2 : ℝ) ^ (663 / 80 : ℝ)) ^ ell) /
        (((2 ^ t : ℕ) : ℝ) ^ (1 / 16 : ℝ)) ≤
      ((2 ^ (d + 1) : ℕ) : ℝ) := by
    simpa only [t, d] using block8_scale_ratio_le ell r
  have hexp :
      (8 + 8 * (1 / 16 : ℝ) * (23 / 40 : ℝ)) = 663 / 80 := by norm_num
  have hbase :
      blockCoeff 8 (1 / 16) = decay8 * (2 : ℝ) ^ (663 / 80 : ℝ) := by
    unfold decay8
    rw [hexp]
    field_simp
  have hdenpos : 0 < (((2 ^ t : ℕ) : ℝ) ^ (1 / 16 : ℝ)) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hreassoc :
      ((2 : ℝ) ^ (15 / 16 : ℝ) *
          (decay8 ^ ell * (((2 : ℝ) ^ (663 / 80 : ℝ)) ^ ell)) *
          (2 * (3 / 2 : ℝ) ^ (1 / 16 : ℝ)) ^ r) /
          (((2 ^ t : ℕ) : ℝ) ^ (1 / 16 : ℝ)) =
        (2 : ℝ) ^ (15 / 16 : ℝ) * decay8 ^ ell *
          (2 * (3 / 2 : ℝ) ^ (1 / 16 : ℝ)) ^ r *
          ((((2 : ℝ) ^ (663 / 80 : ℝ)) ^ ell) /
            (((2 ^ t : ℕ) : ℝ) ^ (1 / 16 : ℝ))) := by
    field_simp
  have hdecayNonneg : 0 ≤ decay8 ^ ell := pow_nonneg decay8_nonneg ell
  have hprele :
      (2 : ℝ) ^ (15 / 16 : ℝ) * decay8 ^ ell *
          (2 * (3 / 2 : ℝ) ^ (1 / 16 : ℝ)) ^ r *
          ((((2 : ℝ) ^ (663 / 80 : ℝ)) ^ ell) /
            (((2 ^ t : ℕ) : ℝ) ^ (1 / 16 : ℝ))) ≤
        2 * decay8 ^ ell * 4096 * ((2 ^ (d + 1) : ℕ) : ℝ) := by
    gcongr
  have hbound :
      (2 : ℝ) ^ (15 / 16 : ℝ) * decay8 ^ ell *
          (2 * (3 / 2 : ℝ) ^ (1 / 16 : ℝ)) ^ r *
          ((((2 : ℝ) ^ (663 / 80 : ℝ)) ^ ell) /
            (((2 ^ t : ℕ) : ℝ) ^ (1 / 16 : ℝ))) <
        2 * (1 / 1048576 : ℝ) * 4096 * ((2 ^ (d + 1) : ℕ) : ℝ) := by
    calc
      _ ≤ 2 * decay8 ^ ell * 4096 * ((2 ^ (d + 1) : ℕ) : ℝ) := hprele
      _ < 2 * (1 / 1048576 : ℝ) * 4096 *
          ((2 ^ (d + 1) : ℕ) : ℝ) := by
        gcongr
  have hseven : 7 ≤ d + 1 := by omega
  have hpowNat : 2 ^ (d - 6) * 2 ^ 7 = 2 ^ (d + 1) := by
    have h := pow_sub_mul_pow 2 hseven
    have hsub : d + 1 - 7 = d - 6 := by omega
    simpa only [hsub] using h
  have hcast := congrArg (fun n : ℕ => (n : ℝ)) hpowNat
  have hconst :
      2 * (1 / 1048576 : ℝ) * 4096 * ((2 ^ (d + 1) : ℕ) : ℝ) =
        ((2 ^ (d - 6) : ℕ) : ℝ) := by
    norm_num at hcast ⊢
    linarith
  rw [show 8 * ell + r = d by rfl, show targetBitCount d = t by rfl,
    hbase, mul_pow, hreassoc]
  exact hbound.trans_eq hconst

end Green25Fractional

end

/- ## Part: `fractional_allN` -/

section

/- The arbitrary-dimension and arbitrary-prefix Green 25 counterexample. -/

namespace Green25Fractional

open Finset

/-- Exact coloring on every sufficiently large binary dimension, including
dimensions which are not multiples of forty. -/
theorem exists_large_dimension_exact_interval_coloring
    {ell r : ℕ} (hell : 1280000 ≤ ell) (hr : r < 8) :
    ∃ g : Fin (2 ^ (8 * ell + r)) →
        Fin (2 ^ targetBitCount (8 * ell + r)),
      Function.Surjective g ∧
      (finIntervalCollisionSumFinset (2 ^ (8 * ell + r)) g).card <
        2 ^ ((8 * ell + r) - 6) := by
  exact exists_block8_remainder_exact_interval_coloring ell r
    (targetBitCount (8 * ell + r)) (2 ^ ((8 * ell + r) - 6))
    (targetBitCount_le _) (block8_remainder_scalar_small hell hr)

/-- The collision allowance `2^(d-6)` is already less than one tenth of
every prefix lying above `2^(d-1)`. -/
theorem ten_pow_sub_six_lt_pow_sub_one {d : ℕ} (hd : 6 ≤ d) :
    10 * 2 ^ (d - 6) < 2 ^ (d - 1) := by
  have hfive : 5 ≤ d - 1 := by omega
  have hpow : 2 ^ (d - 6) * 2 ^ 5 = 2 ^ (d - 1) := by
    have h := pow_sub_mul_pow 2 hfive
    have hsub : d - 1 - 5 = d - 6 := by omega
    simpa only [hsub] using h
  have hpos : 0 < 2 ^ (d - 6) := pow_pos (by norm_num) _
  norm_num at hpow ⊢
  omega

/-- Exact `K`-color counterexample on an arbitrary prefix of a sufficiently
large binary interval.  The output is stated in the `10 * card < N` form
needed by the current Formal Conjectures predicate. -/
theorem exists_large_prefix_exact_coloring
    {ell r N K : ℕ} (hell : 1280000 ≤ ell) (hr : r < 8)
    (hlower : 2 ^ ((8 * ell + r) - 1) < N)
    (hupper : N ≤ 2 ^ (8 * ell + r))
    (hcolors : 2 ^ targetBitCount (8 * ell + r) ≤ K)
    (hKN : K ≤ N) :
    ∃ g : Fin N → Fin K, Function.Surjective g ∧
      10 * (finIntervalCollisionSumFinset N g).card < N := by
  let d := 8 * ell + r
  let t := targetBitCount d
  have hd6 : 6 ≤ d := by simp only [d]; omega
  obtain ⟨g, hsurj, hsmall⟩ :=
    exists_exact_prefix_coloring_of_scalar ell r t (2 ^ (d - 6)) N K
      (by simpa only [t, d] using targetBitCount_le d)
      (by simpa only [d] using hupper)
      (by simpa only [t, d] using hcolors) hKN
      (by simpa only [t, d] using block8_remainder_scalar_small hell hr)
  refine ⟨g, hsurj, ?_⟩
  have hbudget : 10 * 2 ^ (d - 6) < N := by
    calc
      10 * 2 ^ (d - 6) < 2 ^ (d - 1) := ten_pow_sub_six_lt_pow_sub_one hd6
      _ < N := by simpa only [d] using hlower
  omega

/-- Finpartition form of the arbitrary-prefix construction. -/
theorem exists_large_prefix_finpartition_counterexample
    {ell r N K : ℕ} (hell : 1280000 ≤ ell) (hr : r < 8)
    (hlower : 2 ^ ((8 * ell + r) - 1) < N)
    (hupper : N ≤ 2 ^ (8 * ell + r))
    (hcolors : 2 ^ targetBitCount (8 * ell + r) ≤ K)
    (hKN : K ≤ N) :
    ∃ P : Finpartition (Icc 1 N), P.parts.card = K ∧
      10 * (P.parts.biUnion Finset.restrictedSumset).card < N := by
  obtain ⟨g, hsurj, hsmall⟩ :=
    exists_large_prefix_exact_coloring hell hr hlower hupper hcolors hKN
  let P := intervalFinpartition g hsurj
  refine ⟨P, intervalFinpartition_card_parts g hsurj, ?_⟩
  have hle := finpartition_restrictedSumset_card_le g hsurj
  change 10 * ((intervalFinpartition g hsurj).parts.biUnion
    Finset.restrictedSumset).card < N
  omega

/-- Direct statement against `Green25.Property25`: every `K` in the stated
range fails the property on every sufficiently large binary prefix. -/
theorem not_property25_large_prefix
    {ell r N K : ℕ} (hell : 1280000 ≤ ell) (hr : r < 8)
    (hlower : 2 ^ ((8 * ell + r) - 1) < N)
    (hupper : N ≤ 2 ^ (8 * ell + r))
    (hcolors : 2 ^ targetBitCount (8 * ell + r) ≤ K)
    (hKN : K ≤ N) :
    ¬ Green25.Property25 K N := by
  obtain ⟨P, hparts, hsmall⟩ :=
    exists_large_prefix_finpartition_counterexample
      hell hr hlower hupper hcolors hKN
  intro hproperty
  have hlowerFC := hproperty.2.2 P hparts
  omega

end Green25Fractional

end

/- ## Part: `fractional_target` -/

section

/- Specialize the arbitrary-prefix theorem to
`k(N) = ceil (N^(23/40))` and choose the binary interval automatically. -/

namespace Green25Fractional

/-- The requested number of colors, with the real power and ceiling made
explicit in Lean. -/
noncomputable def green25ColorCount (N : ℕ) : ℕ :=
  Nat.ceil ((N : ℝ) ^ (23 / 40 : ℝ))

/-- Explicit bit threshold used by the certified all-`N` theorem.  Keeping it
as a definition prevents the kernel from expanding the astronomically large
integer `2^(10239999)`. -/
def allNThresholdBits : ℕ := 8 * 1280000

theorem allNThresholdBits_eq : allNThresholdBits = 10240000 := by
  rfl

/-- Since `23/40 ≤ 1`, the requested number of colors never exceeds `N`
once `N` is positive. -/
theorem green25ColorCount_le {N : ℕ} (hN : 1 ≤ N) :
    green25ColorCount N ≤ N := by
  rw [green25ColorCount, Nat.ceil_le]
  exact Real.rpow_le_self_of_one_le (by exact_mod_cast hN)
    (by norm_num : (23 / 40 : ℝ) ≤ 1)

/-- The conservative output-bit count available below `N` fits inside
`ceil (N^(23/40))`. -/
theorem pow_targetBitCount_le_green25ColorCount {d N : ℕ}
    (hlower : 2 ^ (d - 1) < N) :
    2 ^ targetBitCount d ≤ green25ColorCount N := by
  let t := targetBitCount d
  have hround := (targetBitCount_bounds d).1
  have hroundReal : ((40 * t : ℕ) : ℝ) ≤
      ((23 * (d - 1) : ℕ) : ℝ) := by
    exact_mod_cast hround
  have hexp : (t : ℝ) ≤ ((d - 1 : ℕ) : ℝ) * (23 / 40 : ℝ) := by
    push_cast at hroundReal
    norm_num at hroundReal ⊢
    linarith
  have hcastT : ((2 ^ t : ℕ) : ℝ) = (2 : ℝ) ^ (t : ℝ) := by
    calc
      ((2 ^ t : ℕ) : ℝ) = (2 : ℝ) ^ (t : ℕ) := by norm_num
      _ = (2 : ℝ) ^ (t : ℝ) := (Real.rpow_natCast 2 t).symm
  have hpowD :
      (2 : ℝ) ^ (((d - 1 : ℕ) : ℝ) * (23 / 40 : ℝ)) =
        (((2 ^ (d - 1) : ℕ) : ℝ) ^ (23 / 40 : ℝ)) := by
    calc
      (2 : ℝ) ^ (((d - 1 : ℕ) : ℝ) * (23 / 40 : ℝ)) =
          (((2 : ℝ) ^ (((d - 1 : ℕ) : ℝ))) ^ (23 / 40 : ℝ)) := by
        rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ = (((2 : ℝ) ^ (d - 1 : ℕ)) ^ (23 / 40 : ℝ)) := by
        rw [Real.rpow_natCast]
      _ = (((2 ^ (d - 1) : ℕ) : ℝ) ^ (23 / 40 : ℝ)) := by norm_num
  have hbase : ((2 ^ (d - 1) : ℕ) : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hlower.le
  have hreal : ((2 ^ t : ℕ) : ℝ) ≤
      (N : ℝ) ^ (23 / 40 : ℝ) := by
    calc
      ((2 ^ t : ℕ) : ℝ) = (2 : ℝ) ^ (t : ℝ) := hcastT
      _ ≤ (2 : ℝ) ^ (((d - 1 : ℕ) : ℝ) * (23 / 40 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = (((2 ^ (d - 1) : ℕ) : ℝ) ^ (23 / 40 : ℝ)) := hpowD
      _ ≤ (N : ℝ) ^ (23 / 40 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hbase (by norm_num)
  have hceil : ((2 ^ t : ℕ) : ℝ) ≤
      (green25ColorCount N : ℝ) := by
    exact hreal.trans (by
      simpa only [green25ColorCount] using
        (Nat.le_ceil ((N : ℝ) ^ (23 / 40 : ℝ))))
  exact_mod_cast hceil

/-- Complete all-sufficiently-large-`N` statement for the concrete color
function.  The huge threshold is explicit and comes solely from the deliberately
coarse certified contraction estimate. -/
theorem not_property25_green25ColorCount_of_large {N : ℕ}
    (hlarge : 2 ^ (allNThresholdBits - 1) < N) :
    ¬ Green25.Property25 (green25ColorCount N) N := by
  let d := Nat.clog 2 N
  let ell := d / 8
  let r := d % 8
  have hN : 1 < N := by
    have hpowpos : 0 < 2 ^ (allNThresholdBits - 1) := pow_pos (by norm_num) _
    omega
  have hdlarge : allNThresholdBits ≤ d := by
    have hclog : allNThresholdBits - 1 < Nat.clog 2 N :=
      (Nat.lt_clog_iff_pow_lt (by norm_num : 1 < 2)).2 hlarge
    change allNThresholdBits ≤ Nat.clog 2 N
    have hthreshold : 0 < allNThresholdBits := by
      rw [allNThresholdBits_eq]
      norm_num
    omega
  have hell : 1280000 ≤ ell := by
    rw [show ell = d / 8 by rfl, Nat.le_div_iff_mul_le (by norm_num : 0 < 8)]
    rw [allNThresholdBits_eq] at hdlarge
    omega
  have hr : r < 8 := by
    exact Nat.mod_lt d (by norm_num)
  have hdecomp : 8 * ell + r = d := by
    simp only [ell, r]
    omega
  have hlowerD : 2 ^ (d - 1) < N := by
    simpa only [d, Nat.pred_eq_sub_one] using
      Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) hN
  have hupperD : N ≤ 2 ^ d := by
    simpa only [d] using Nat.le_pow_clog (by norm_num : 1 < 2) N
  have hcolorsD : 2 ^ targetBitCount d ≤ green25ColorCount N :=
    pow_targetBitCount_le_green25ColorCount hlowerD
  have hKN : green25ColorCount N ≤ N :=
    green25ColorCount_le hN.le
  apply not_property25_large_prefix (ell := ell) (r := r)
    (N := N) (K := green25ColorCount N) hell hr
  · simpa only [hdecomp] using hlowerD
  · simpa only [hdecomp] using hupperD
  · simpa only [hdecomp] using hcolorsD
  · exact hKN

end Green25Fractional

end

/- ## Part: `fractional_upper_witness` -/

section

/- The asymptotic part of the concrete Green 25 upper-bound witness. -/

open Asymptotics Filter

namespace Green25Fractional

/-- The underlying real power is little-o of `N / log N`. -/
theorem rpow_23_40_isLittleO_bestUpper :
    (fun N : ℕ => (N : ℝ) ^ (23 / 40 : ℝ)) =o[atTop]
      (fun N : ℕ => Green25.bestUpper N) := by
  have hlog : (fun N : ℕ => Real.log (N : ℝ)) =o[atTop]
      (fun N : ℕ => (N : ℝ) ^ (17 / 40 : ℝ)) :=
    IsLittleO.natCast_atTop
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 17 / 40))
  have hraw :=
    (isBigO_refl (fun N : ℕ => (N : ℝ) ^ (23 / 40 : ℝ)) atTop).mul_isLittleO hlog
  have hproduct :
      (fun N : ℕ => Real.log (N : ℝ) * (N : ℝ) ^ (23 / 40 : ℝ))
        =o[atTop] (fun N : ℕ => (N : ℝ)) := by
    refine hraw.congr' (Eventually.of_forall fun N => by ring) ?_
    filter_upwards [Ici_mem_atTop 1] with N hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    rw [← Real.rpow_add hNpos]
    norm_num
  have hlogNe : ∀ᶠ N : ℕ in atTop, Real.log (N : ℝ) ≠ 0 := by
    filter_upwards [Ici_mem_atTop 2] with N hN
    exact ne_of_gt (Real.log_pos (by exact_mod_cast hN))
  have hdiv := (isLittleO_mul_iff_isLittleO_div hlogNe).mp hproduct
  simpa only [Green25.bestUpper] using hdiv

/-- Taking the natural ceiling changes the power by only a constant factor. -/
theorem green25ColorCount_isBigO_rpow :
    (fun N : ℕ => (green25ColorCount N : ℝ)) =O[atTop]
      (fun N : ℕ => (N : ℝ) ^ (23 / 40 : ℝ)) := by
  refine IsBigO.of_bound 2 ?_
  filter_upwards [Ici_mem_atTop 1] with N hN
  have hbase : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hone : (1 : ℝ) ≤ (N : ℝ) ^ (23 / 40 : ℝ) :=
    Real.one_le_rpow hbase (by norm_num)
  have hceil := Nat.ceil_lt_add_one
    (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ N) (23 / 40 : ℝ))
  rw [Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  change (green25ColorCount N : ℝ) ≤
    2 * (N : ℝ) ^ (23 / 40 : ℝ)
  rw [green25ColorCount]
  linarith

/-- The requested ceiling-valued color count is little-o of the best-known
`N / log N` upper scale. -/
theorem green25ColorCount_isLittleO_bestUpper :
    (fun N : ℕ => (green25ColorCount N : ℝ)) =o[atTop]
      (fun N : ℕ => Green25.bestUpper N) :=
  green25ColorCount_isBigO_rpow.trans_isLittleO
    rpow_23_40_isLittleO_bestUpper

/-- The concrete color count is eventually a valid partition size. -/
theorem green25ColorCount_eventually_valid :
    ∀ᶠ N : ℕ in atTop, 1 ≤ green25ColorCount N ∧ green25ColorCount N ≤ N := by
  filter_upwards [Ici_mem_atTop 1] with N hN
  constructor
  · have hpow : (1 : ℝ) ≤ (N : ℝ) ^ (23 / 40 : ℝ) :=
      Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)
    have hceil := hpow.trans
      (Nat.le_ceil ((N : ℝ) ^ (23 / 40 : ℝ)))
    exact_mod_cast hceil
  · exact green25ColorCount_le hN

/-- The all-`N` construction gives counterexamples eventually, not merely on
an unbounded subsequence. -/
theorem green25ColorCount_eventually_not_property :
    ∀ᶠ N : ℕ in atTop, ¬ Green25.Property25 (green25ColorCount N) N := by
  filter_upwards [eventually_gt_atTop (2 ^ (allNThresholdBits - 1))] with N hN
  exact not_property25_green25ColorCount_of_large hN

theorem green25ColorCount_not_eventually_property :
    ¬ ∀ᶠ N : ℕ in atTop, Green25.Property25 (green25ColorCount N) N := by
  intro hproperty
  have hfalse : ∀ᶠ _N : ℕ in atTop, False :=
    (green25ColorCount_eventually_not_property.and hproperty).mono
      (fun _N h => h.1 h.2)
  obtain ⟨_N, h⟩ := hfalse.exists
  exact h

/-- The body of `Green25.green_25.upper`, with its opaque `answer(sorry)`
replaced by the explicit function proved in this development. -/
theorem green_25_upper_concrete :
    let ans := green25ColorCount
    (∀ᶠ N in atTop, 1 ≤ ans N ∧ ans N ≤ N) ∧
    (fun N => (ans N : ℝ)) =o[atTop] Green25.bestUpper ∧
    ¬ ∀ᶠ N in atTop, Green25.Property25 (ans N) N := by
  exact ⟨green25ColorCount_eventually_valid,
    green25ColorCount_isLittleO_bestUpper,
    green25ColorCount_not_eventually_property⟩

/-- A version of the FC upper statement with the witness quantified explicitly.
This is the statement to which `green25ColorCount` can actually be supplied. -/
theorem exists_improved_upper_witness :
    ∃ k : ℕ → ℕ,
      (∀ᶠ N in atTop, 1 ≤ k N ∧ k N ≤ N) ∧
      (fun N => (k N : ℝ)) =o[atTop] Green25.bestUpper ∧
      ¬ ∀ᶠ N in atTop, Green25.Property25 (k N) N := by
  exact ⟨green25ColorCount, green25ColorCount_eventually_valid,
    green25ColorCount_isLittleO_bestUpper,
    green25ColorCount_not_eventually_property⟩

end Green25Fractional

end

/- ## The Formal Conjectures target -/

open Asymptotics Filter

namespace Green25Fractional

/-- Exact Formal Conjectures target `Green25.green_25.upper` with the explicit
answer `N ↦ ⌈N ^ (23 / 40)⌉`. -/
@[category research solved, AMS 5 11]
theorem green_25_upper_solved :
    let ans := (answer(fun N => Nat.ceil ((N : ℝ) ^ (23 / 40 : ℝ))) : ℕ → ℕ)
    (∀ᶠ N in atTop, 1 ≤ ans N ∧ ans N ≤ N) ∧
    (fun N => (ans N : ℝ)) =o[atTop] Green25.bestUpper ∧
    ¬ ∀ᶠ N in atTop, Green25.Property25 (ans N) N := by
  exact green_25_upper_concrete

end Green25Fractional

#print axioms Green25Fractional.green_25_upper_solved
