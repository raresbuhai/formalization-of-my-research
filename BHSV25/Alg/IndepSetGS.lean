module

public import BHSV25.Alg.IndepSet
public import BHSV25.Alg.EigGap
public import BHSV25.Net.GSCorrect
public import BHSV25.Net.GSPolyTime

/-!
# Theorem 7.20: the algorithm with the greedy net

The algorithm of [BHSV25, Theorem 7.20] (`BHSV25.Alg.indepAlgGS`): the largest rounding of the
sets `{x : c_x ≥ 0}` for the vectors `c` of the greedy net of the bottom eigenspace
(`BHSV25.Net.netGS`), and of the set of all vertices. It reads its parameters `(a, T, N, B)`: the
net has `T` rounds, the grid of radius `N` cut at `B`, and the filter `((I - Ã) / 2)^(a n⁵)`.

* **Polynomial time** (`BHSV25.Alg.indepAlgGS_polytime`), as one machine reading the parameters
  in unary with the graph.
* **One candidate at constant precision** (`BHSV25.Alg.card_roundIndep_thrBits_ge`)
  [BHSV25, Lemmas 7.22 and 7.23]: a vector within `ρ` of the projection of the sign vector `u` of
  an independent set `I` onto the eigenvectors with eigenvalue at most `-θ` rounds to an
  independent set of at least `|I| - (1 + η) 4 (n/2 - |I|) / (1 - θ) - (1 + 1/η) ρ² n` vertices.
* **The guarantee** (`BHSV25.Alg.card_indepAlgGS_ge`), for `N = (⌊√T⌋ + 1) K`,
  `B = (3 + 12 K)^T` and `a ≥ 8 (T + 2 + K/2) / c''`, on regular graphs with at most `T`
  eigenvalues at most `-λ`: the net is applied at the thresholds `θ' = min(λ, 1 - 1/(4n⁴))` and
  `θ = θ' + c'' (1 - θ')`. The count of eigenvalues at most `-θ'` is at most `T` because no
  eigenvalue lies in `(-1, -1 + 1/(2n⁴))` (`BHSV25.Alg.eig_eq_neg_one_or_ge`), and
  `1 - θ' ≥ 1/(4 n⁴)`, so the power `a n⁵` makes the filter's error at most `2/K`, like the grid's;
  the precision is `ρ = 4/K`, and `1 - θ ≥ (1 - c'') (1 - λ)`.
-/

@[expose] public section

namespace BHSV25.Alg

open Turing.MultiTapeTM ComputableInPolyTime Matrix
open Encoding (encRat)

/-! ### The algorithm -/

/-- The net of Theorem 7.20 for the parameters `(a, T, N, B)`: the greedy net of the bottom
eigenspace with the filter `((I - Ã) / 2)^(a n⁵)`. -/
def indepNet (p : ℕ × ℕ × ℕ × ℕ) (x : ℕ × List Bool) : List (List ℚ) :=
  Net.netGS true (p.1 * numV x ^ 5) p.2.1 p.2.2.1 p.2.2.2 x

/-- **The algorithm** of [BHSV25, Theorem 7.20], for the parameters `(a, T, N, B)`. -/
def indepAlgGS (p : ℕ × ℕ × ℕ × ℕ) (x : ℕ × List Bool) : List Bool := indepAlg (indepNet p) x

/-- The input of the machine: the parameters in unary, with the graph. -/
abbrev encIndepIn : (ℕ × ℕ × ℕ × ℕ) × (ℕ × List Bool) ↪ List Bool :=
  encPair Net.encGSPar (encPair encNat encBits)

theorem indepNet_polytime : ComputableInPolyTime
    (fun z : (ℕ × ℕ × ℕ × ℕ) × (ℕ × List Bool) ↦ indepNet z.1 z.2) encIndepIn
    (encList (encList encRat)) := by
  have hpar : ComputableInPolyTime (fun z : (ℕ × ℕ × ℕ × ℕ) × (ℕ × List Bool) ↦ z.1) encIndepIn
      Net.encGSPar := fst _ _
  have hx : ComputableInPolyTime (fun z : (ℕ × ℕ × ℕ × ℕ) × (ℕ × List Bool) ↦ z.2) encIndepIn
      (encPair encNat encBits) := snd _ _
  have ha := (fst _ _).comp hpar
  have hrest := (snd _ _).comp hpar
  have hn := numV_polytime.comp hx
  have hn5 : ComputableInPolyTime (fun z : (ℕ × ℕ × ℕ × ℕ) × (ℕ × List Bool) ↦ numV z.2 ^ 5)
      encIndepIn encUnary := by
    have h := unary_mul' (unary_mul' (unary_mul' (unary_mul' hn hn) hn) hn) hn
    convert h using 1
    funext z
    simp only [Function.comp_apply]
    ring
  have hE := unary_mul' ha hn5
  have hp := hE.prod hrest
  have key := (Net.netGS_polytime true).comp (hp.prod hx)
  exact key

/-- **The algorithm runs in polynomial time**, reading its parameters in unary with the graph. -/
theorem indepAlgGS_polytime : ComputableInPolyTime
    (fun z : (ℕ × ℕ × ℕ × ℕ) × (ℕ × List Bool) ↦ indepAlgGS z.1 z.2) encIndepIn encBits := by
  unfold indepAlgGS indepAlg
  have hx : ComputableInPolyTime (fun z : (ℕ × ℕ × ℕ × ℕ) × (ℕ × List Bool) ↦ z.2) encIndepIn
      (encPair encNat encBits) := snd _ _
  have hn := numV_polytime.comp hx
  have hadj : ComputableInPolyTime (fun z : (ℕ × ℕ × ℕ × ℕ) × (ℕ × List Bool) ↦ z.2.2)
      encIndepIn encBits := (snd _ _).comp hx
  have hrep : ComputableInPolyTime
      (fun z : (ℕ × ℕ × ℕ × ℕ) × (ℕ × List Bool) ↦ List.replicate (numV z.2) true)
      encIndepIn encBits :=
    (bits_encList_polyTime encBool).2.comp (replicate hn (const true))
  have hL : ComputableInPolyTime (fun z : (ℕ × ℕ × ℕ × ℕ) × (ℕ × List Bool) ↦
      (indepNet z.1 z.2).map fun c ↦ roundIndep (numV z.2) z.2.2 (thrBits (numV z.2) c))
      encIndepIn (encList encBits) :=
    mapWithInput indepNet_polytime (roundIndep' (hn.comp (fst _ _)) (hadj.comp (fst _ _))
      (thrBits' (hn.comp (fst _ _)) (snd _ _)))
  exact bestOf' hn (roundIndep' hn hadj hrep) hL

/-! ### One candidate at constant precision -/

open Classical in
/-- **One candidate** [BHSV25, Lemmas 7.22 and 7.23]: if `w` is within `ρ` of the projection of
`signVec I` onto the span of the eigenvectors with eigenvalue at most `-θ`, the rounding of the
vertices where `w ≥ 0` is an independent set of at least
`|I| - (1 + η) 4 (n/2 - |I|) / (1 - θ) - (1 + 1/η) ρ² n` vertices. -/
theorem card_roundIndep_thrBits_ge (G : Graph) {d : ℕ} (hd : G.2.IsRegularOfDegree d)
    (hd0 : d ≠ 0) (hn : 0 < G.1) {I : Finset (Fin G.1)} (hI : G.2.IsIndepSet (I : Set (Fin G.1)))
    {θ ρ η : ℝ} (hθ1 : θ < 1) (hη : 0 < η) (c : List ℚ)
    (hc : (Net.vecOf G.1 c - Spectral.proj G.normAdj_isHermitian (· ≤ -θ) (signVec I)) ⬝ᵥ
        (Net.vecOf G.1 c - Spectral.proj G.normAdj_isHermitian (· ≤ -θ) (signVec I)) ≤ ρ ^ 2) :
    (I.card : ℝ) - (1 + η) * 4 / (1 - θ) * (G.1 / 2 - I.card) - (1 + 1 / η) * ρ ^ 2 * G.1 ≤
      (G.vertexSet (roundIndep G.1 (adjTable G) (thrBits G.1 c))).card := by
  classical
  set u := signVec I with hu
  set P := Spectral.proj G.normAdj_isHermitian (· ≤ -θ) u with hP
  set w := Net.vecOf G.1 c with hw
  set Ih := G.vertexSet (thrBits G.1 c) with hIh
  set R := G.vertexSet (roundIndep G.1 (adjTable G) (thrBits G.1 c)) with hR
  have hn' : (0 : ℝ) < G.1 := Nat.cast_pos.2 hn
  have hθ' : 0 < 1 - θ := by linarith only [hθ1]
  have hη' : 0 < 1 + 1 / η := by positivity
  have hIh' : Ih = Finset.univ.filter fun x ↦ 0 ≤ w x := by
    ext x
    rw [hIh, mem_vertexSet_thrBits, Finset.mem_filter]
    exact ⟨fun h ↦ ⟨Finset.mem_univ _, h⟩, fun h ↦ h.2⟩
  set D := (I.filter fun x ↦ w x < 0).card + ((Finset.univ.filter fun x ↦ 0 ≤ w x) \ I).card
    with hD
  have hloss : I.card ≤ R.card + D := by
    have h1 := card_inter_le_card_roundIndep G (thrBits G.1 c) hI
    rw [← hIh, ← hR] at h1
    have h2 : (Ih ∩ I).card + (I.filter fun x ↦ w x < 0).card = I.card := by
      have hsplit := Finset.card_filter_add_card_filter_not (s := I) (fun x ↦ 0 ≤ w x)
      have e1 : Ih ∩ I = I.filter fun x ↦ 0 ≤ w x := by
        ext x
        rw [hIh', Finset.mem_inter, Finset.mem_filter, Finset.mem_filter]
        exact ⟨fun h ↦ ⟨h.2, h.1.2⟩, fun h ↦ ⟨⟨Finset.mem_univ _, h.2⟩, h.1⟩⟩
      have e2 : (I.filter fun x ↦ ¬0 ≤ w x) = I.filter fun x ↦ w x < 0 :=
        Finset.filter_congr fun x _ ↦ not_le
      rw [e1, ← e2]
      exact hsplit
    rw [hIh'] at h1
    rw [hIh'] at h2
    omega
  have hmis := card_misclassified_le hn I w
  rw [← hD] at hmis
  have hq : u ⬝ᵥ (G.normAdj *ᵥ u) = 1 - 4 * I.card / G.1 := quad_signVec G hd hd0 hn hI
  have hu1 : u ⬝ᵥ u = 1 := signVec_dot_self hn I
  have hdist : (1 - θ) * ((u - P) ⬝ᵥ (u - P)) ≤ u ⬝ᵥ (G.normAdj *ᵥ u) + u ⬝ᵥ u :=
    one_sub_mul_dist_proj_le G θ u
  rw [hq, hu1] at hdist
  have hwu : (w - u) ⬝ᵥ (w - u) ≤ (1 + η) * ((u - P) ⬝ᵥ (u - P)) + (1 + 1 / η) * ρ ^ 2 := by
    have h := dot_add_le (P - u) (w - P) hη
    rw [show P - u + (w - P) = w - u by abel, show P - u = -(u - P) by abel, neg_dot_neg] at h
    have := mul_le_mul_of_nonneg_left hc hη'.le
    linarith only [h, this]
  have hb : (u - P) ⬝ᵥ (u - P) ≤ 4 * (G.1 / 2 - I.card) / G.1 / (1 - θ) := by
    rw [le_div_iff₀ hθ']
    have e : 4 * ((G.1 : ℝ) / 2 - I.card) / G.1 = 1 - 4 * I.card / G.1 + 1 := by
      field_simp
      ring
    rw [e, mul_comm]
    exact hdist
  have h3 : (G.1 : ℝ) * ((1 + η) * (4 * (G.1 / 2 - I.card) / G.1 / (1 - θ))) =
      (1 + η) * 4 / (1 - θ) * (G.1 / 2 - I.card) := by
    field_simp
  have h5 := mul_le_mul_of_nonneg_left hb (by positivity : (0 : ℝ) ≤ 1 + η)
  have h6' : (w - u) ⬝ᵥ (w - u) ≤ (1 + η) * (4 * (G.1 / 2 - I.card) / G.1 / (1 - θ)) +
      (1 + 1 / η) * ρ ^ 2 := hwu.trans (add_le_add_left h5 _)
  have h6 := mul_le_mul_of_nonneg_left h6' hn'.le
  rw [mul_add, h3] at h6
  have hR' : (I.card : ℝ) ≤ R.card + D := by exact_mod_cast hloss
  have hDle := hmis.trans h6
  nlinarith [hR', hDle]

/-! ### The guarantee -/

/-- `exp(-K/2) ≤ 2 / K`. -/
theorem exp_neg_half_le {K : ℝ} (hK : 0 < K) : Real.exp (-(K / 2)) ≤ 2 / K := by
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) hK]
  have := Real.add_one_le_exp (K / 2)
  linarith

/-- **The filter's error**: for `n ≥ 1`, `1 - θ' ≥ 1/(4 n⁴)`, `θ = θ' + c'' (1 - θ')` and
`a ≥ 8 (T + 2 + K/2) / c''`, `√n 2^(T+1) ((1 + θ') / (1 + θ))^(a n⁵) ≤ 2 / K`. -/
theorem filter_error_le {n T K a : ℕ} (hn : 0 < n) (hK : 0 < K) {cc θ' : ℝ} (hcc0 : 0 < cc)
    (hcc1 : cc < 1) (hθ'0 : 0 < θ') (hδ : 1 / (4 * (n : ℝ) ^ 4) ≤ 1 - θ')
    (ha : 8 / cc * (T + 2 + K / 2 : ℝ) ≤ a) :
    Real.sqrt n * 2 ^ (T + 1) * ((1 + θ') / (1 + (θ' + cc * (1 - θ')))) ^ (a * n ^ 5) ≤
      2 / K := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  set θ := θ' + cc * (1 - θ') with hθ
  have hθ'1 : θ' < 1 := by
    have : 0 < 1 / (4 * (n : ℝ) ^ 4) := by positivity
    linarith
  have h1θ : 0 < 1 + θ := by nlinarith
  -- the ratio
  set r := (1 + θ') / (1 + θ) with hr
  have hr0 : 0 ≤ r := div_nonneg (by linarith) h1θ.le
  have hθle : θ ≤ 1 := by nlinarith
  have hr1 : r ≤ 1 - cc / (8 * (n : ℝ) ^ 4) := by
    rw [hr, div_le_iff₀ h1θ]
    have h2 : cc * (1 - θ') / 2 ≤ cc * (1 - θ') / (1 + θ) * 1 := by
      rw [mul_one]
      exact div_le_div_of_nonneg_left (by nlinarith) h1θ (by linarith)
    have h3 : (1 + θ') = (1 + θ) * (1 - cc * (1 - θ') / (1 + θ)) := by
      field_simp
      rw [hθ]
      ring
    have h4 : cc / (8 * (n : ℝ) ^ 4) ≤ cc * (1 - θ') / 2 := by
      have := mul_le_mul_of_nonneg_left hδ hcc0.le
      have e : cc / (8 * (n : ℝ) ^ 4) = cc * (1 / (4 * (n : ℝ) ^ 4)) / 2 := by
        field_simp
        ring
      rw [e]
      linarith
    rw [h3]
    have h5 : cc * (1 - θ') / (1 + θ) ≥ cc / (8 * (n : ℝ) ^ 4) := by linarith
    nlinarith
  have hrexp : r ≤ Real.exp (-(cc / (8 * (n : ℝ) ^ 4))) := by
    have := Real.add_one_le_exp (-(cc / (8 * (n : ℝ) ^ 4)))
    linarith
  have hpow : r ^ (a * n ^ 5) ≤ Real.exp (-(cc * a * n / 8)) := by
    refine (pow_le_pow_left₀ hr0 hrexp _).trans (le_of_eq ?_)
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  -- the exponent
  have hX : (n : ℝ) + (T + 1) + K / 2 ≤ cc * a * n / 8 := by
    have h1 : (T + 2 + K / 2 : ℝ) * n ≤ cc * a * n / 8 := by
      have := mul_le_mul_of_nonneg_left ha hcc0.le
      rw [show cc * (8 / cc * (T + 2 + K / 2 : ℝ)) = 8 * (T + 2 + K / 2) by field_simp] at this
      nlinarith
    have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
    nlinarith
  have hsq : Real.sqrt n ≤ Real.exp n := by
    have h1 : Real.sqrt n ≤ n + 1 := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith
    linarith [Real.add_one_le_exp (n : ℝ)]
  have h2 : (2 : ℝ) ^ (T + 1) ≤ Real.exp (T + 1) := by
    have h := Real.add_one_le_exp 1
    calc (2 : ℝ) ^ (T + 1) ≤ Real.exp 1 ^ (T + 1) :=
          pow_le_pow_left₀ (by norm_num) (by linarith) _
      _ = Real.exp (T + 1) := by rw [← Real.exp_nat_mul, mul_one]; push_cast; ring_nf
  calc Real.sqrt n * 2 ^ (T + 1) * r ^ (a * n ^ 5)
      ≤ Real.exp n * Real.exp (T + 1) * Real.exp (-(cc * a * n / 8)) := by
        gcongr
    _ = Real.exp (n + (T + 1) - cc * a * n / 8) := by
        rw [← Real.exp_add, ← Real.exp_add]
        ring_nf
    _ ≤ Real.exp (-(K / 2)) := Real.exp_le_exp.2 (by linarith)
    _ ≤ 2 / K := exp_neg_half_le hK'

open Classical in
/-- **The guarantee of the algorithm** on a `d`-regular graph, `d ≥ 1`, with at most `T`
eigenvalues at most `-λ`, for every independent set `I` and `η > 0`: the output has at least
`|I| - (1 + η) 4 (n/2 - |I|) / ((1 - c'') (1 - λ)) - (1 + 1/η) (4/K)² n` vertices. -/
theorem card_indepAlgGS_ge (G : Graph) {d : ℕ} (hd : G.2.IsRegularOfDegree d) (hd0 : d ≠ 0)
    (hn : 0 < G.1) {lam : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1) {T : ℕ}
    (hT : (Finset.univ.filter fun i ↦ G.eig i ≤ -lam).card ≤ T) {cc : ℝ} (hcc0 : 0 < cc)
    (hcc1 : cc < 1) {K a : ℕ} (hK : 0 < K) (ha : 8 / cc * (T + 2 + K / 2 : ℝ) ≤ a)
    {I : Finset (Fin G.1)} (hI : G.2.IsIndepSet (I : Set (Fin G.1))) {η : ℝ} (hη : 0 < η) :
    (I.card : ℝ) - (1 + η) * 4 / ((1 - cc) * (1 - lam)) * (G.1 / 2 - I.card) -
        (1 + 1 / η) * (4 / K) ^ 2 * G.1 ≤
      (G.vertexSet (indepAlgGS (a, T, (Nat.sqrt T + 1) * K, (3 + 12 * K) ^ T)
        (G.1, adjTable G))).card := by
  have hn' : (1 : ℝ) ≤ G.1 := by exact_mod_cast hn
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  set δ : ℝ := 1 / (4 * (G.1 : ℝ) ^ 4) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 / 4 := by
    rw [hδ]
    have : (1 : ℝ) ≤ (G.1 : ℝ) ^ 4 := one_le_pow₀ hn'
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  -- the thresholds
  set θ' := min lam (1 - δ) with hθ'
  have hθ'0 : 0 < θ' := lt_min hl0 (by linarith)
  have hθ'l : θ' ≤ lam := min_le_left _ _
  have hθ'δ : δ ≤ 1 - θ' := by have := min_le_right lam (1 - δ); linarith
  set θ := θ' + cc * (1 - θ') with hθ
  have hθθ' : θ' < θ := by nlinarith
  have hθ1 : θ < 1 := by nlinarith
  have h1θ : 1 - θ = (1 - cc) * (1 - θ') := by rw [hθ]; ring
  -- few eigenvalues at most `-θ'`
  have hT' : (Finset.univ.filter fun i ↦ G.eig i ≤ -θ').card ≤ T := by
    refine (Finset.card_le_card fun i hi ↦ ?_).trans hT
    rw [Finset.mem_filter] at hi ⊢
    refine ⟨hi.1, ?_⟩
    rcases le_total lam (1 - δ) with h | h
    · rw [hθ', min_eq_left h] at hi
      exact hi.2
    · rcases eig_eq_neg_one_or_ge G ⟨d, hd⟩ i with he | he
      · rw [he]; linarith
      · exfalso
        rw [hθ', min_eq_right h] at hi
        have : 1 / (2 * (G.1 : ℝ) ^ 4) = 2 * δ := by rw [hδ]; field_simp; ring
        rw [this] at he
        linarith [hi.2]
  -- the net
  set u := signVec I with hu
  set w := Spectral.proj G.normAdj_isHermitian (· ≤ -θ) u with hw
  have hw1 : w ⬝ᵥ w ≤ 1 := (proj_dot_self_le _ _ _).trans (signVec_dot_self hn I).le
  have hw2 : G.InEigSpan (· ≤ -θ) w := Spectral.inEigSpan_proj _ _ _
  set N := (Nat.sqrt T + 1) * K with hN
  have hNpos : 0 < N := Nat.mul_pos (Nat.succ_pos _) hK
  obtain ⟨c, hc, hcw⟩ := Net.netGS_bottom_correct G ⟨d, hd⟩ hθ'0 hθθ' hT' (a * G.1 ^ 5) hNpos
    (Net.ballBudget_sqrt T K) w hw1 hw2
  -- the error is at most `4 / K`
  have hgrid : 2 * Real.sqrt T / N ≤ 2 / K := by
    have hs : Real.sqrt T ≤ (Nat.sqrt T + 1 : ℕ) := by
      push_cast
      exact (Real.real_sqrt_lt_nat_sqrt_succ).le
    rw [hN, Nat.cast_mul, div_le_div_iff₀ (by positivity) hK']
    have := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 2 * K)
    nlinarith
  have hfilt := filter_error_le (T := T) hn hK hcc0 hcc1 hθ'0 hθ'δ ha
  have herr : (Net.vecOf G.1 c - w) ⬝ᵥ (Net.vecOf G.1 c - w) ≤ (4 / K) ^ 2 := by
    have h1 : Real.sqrt ((Net.ratVec G.1 c - w) ⬝ᵥ (Net.ratVec G.1 c - w)) ≤ 4 / K := by
      refine hcw.trans ?_
      have : (4 : ℝ) / K = 2 / K + 2 / K := by ring
      rw [this]
      exact add_le_add hgrid hfilt
    have h2 := Real.sq_sqrt (Net.dot_self_nonneg (Net.ratVec G.1 c - w))
    have h3 : Real.sqrt ((Net.ratVec G.1 c - w) ⬝ᵥ (Net.ratVec G.1 c - w)) ^ 2 ≤ (4 / K) ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
    rw [h2] at h3
    exact h3
  -- the candidate and the output
  have hcand := card_roundIndep_thrBits_ge G hd hd0 hn hI hθ1 hη c herr
  have hmem : c ∈ indepNet (a, T, N, (3 + 12 * K) ^ T) (G.1, adjTable G) := by
    rw [indepNet, numV_graph]
    exact hc
  have hle : ((G.vertexSet (roundIndep G.1 (adjTable G) (thrBits G.1 c))).card : ℝ) ≤
      (G.vertexSet (indepAlgGS (a, T, N, (3 + 12 * K) ^ T) (G.1, adjTable G))).card := by
    exact_mod_cast card_cand_le_indepAlg _ G hmem
  -- `1 - θ ≥ (1 - c'') (1 - λ)`
  have hg0 : (0 : ℝ) ≤ G.1 / 2 - I.card := by
    have : (2 * I.card : ℝ) ≤ G.1 := by exact_mod_cast two_mul_card_le G hd hd0 hI
    linarith
  have hcoef : (1 + η) * 4 / (1 - θ) ≤ (1 + η) * 4 / ((1 - cc) * (1 - lam)) := by
    rw [h1θ]
    refine div_le_div_of_nonneg_left (by positivity) (mul_pos (by linarith) (by linarith))
      (mul_le_mul_of_nonneg_left (by linarith) (by linarith))
  have := mul_le_mul_of_nonneg_right hcoef hg0
  linarith

end BHSV25.Alg
