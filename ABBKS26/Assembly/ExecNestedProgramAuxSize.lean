module

public import ABBKS26.Assembly.ExecNestedAuxLayout

/-! # Direct storage bounds for the plain sparse expansion -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.NestedProgram

open Common
open Encoding
open SoS.Solver (RawPoly encRawPoly encProblem)

private def Shape (p : RawPoly) (v E b : ℕ) : Prop :=
  ∀ t ∈ p, t.1.length ≤ v ∧ (∀ x ∈ t.1, x ≤ E) ∧ (encRat t.2).length ≤ b

private theorem Shape.mono {p : RawPoly} {v E b v' E' b' : ℕ}
    (hp : Shape p v E b) (hv : v ≤ v') (hE : E ≤ E') (hb : b ≤ b') :
    Shape p v' E' b' := by
  intro t ht
  obtain ⟨h1, h2, h3⟩ := hp t ht
  exact ⟨h1.trans hv, fun x hx ↦ (h2 x hx).trans hE, h3.trans hb⟩

private theorem Shape.append {p q : RawPoly} {v E b : ℕ}
    (hp : Shape p v E b) (hq : Shape q v E b) : Shape (p ++ q) v E b := by
  intro t ht
  exact (List.mem_append.1 ht).elim (hp t) (hq t)

private theorem Shape.constant (v E : ℕ) (c : ℚ) :
    Shape (constant c) v E (encRat c).length := by
  intro t ht
  have : t = ([], c) := by simpa [NestedProgram.constant] using ht
  subst t
  simp

private theorem Shape.neg {p : RawPoly} {v E b : ℕ} (hp : Shape p v E b) :
    Shape (scale (-1) p) v E b := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ht
  simpa only [neg_one_mul, Rounding.RawAux.length_rat_neg] using hp s hs

private theorem getD_le {e : List ℕ} {E : ℕ} (he : ∀ x ∈ e, x ≤ E) (i : ℕ) :
    e.getD i 0 ≤ E := by
  by_cases hi : i < e.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact he _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    omega

private theorem mul_length (v : ℕ) (p q : RawPoly) :
    (SoS.Coords.mulRaw v p q).length = p.length * q.length := by
  simp [SoS.Coords.mulRaw, List.length_flatMap, List.map_const', List.sum_replicate]

private theorem Shape.mul_one {p q : RawPoly} {v E F b : ℕ}
    (hp : ∀ t ∈ p, (∀ x ∈ t.1, x ≤ E) ∧ t.2 = 1)
    (hq : Shape q v F b) : Shape (SoS.Coords.mulRaw v p q) v (E + F) b := by
  intro z hz
  obtain ⟨s, hs, hz⟩ := List.mem_flatMap.1 hz
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hz
  obtain ⟨he, hc⟩ := hp s hs
  obtain ⟨_, hf, hb⟩ := hq t ht
  refine ⟨by simp [SoS.Poly.addE], ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    exact Nat.add_le_add (getD_le he i) (getD_le hf i)
  · simpa only [hc, one_mul] using hb

private theorem unitExp_shape (v i e : ℕ) :
    (unitExp v i e).length = v ∧ ∀ x ∈ unitExp v i e, x ≤ e := by
  refine ⟨by simp [unitExp], ?_⟩
  intro x hx
  obtain ⟨j, _, rfl⟩ := List.mem_map.1 hx
  split_ifs <;> omega

private theorem gram_shape (I : Rounding.RawInput) (s : ℕ) (M : List (List ℕ))
    (hM : ∀ e ∈ M, e.length = I.family.dimension ∧ ∀ x ∈ e, x ≤ I.degree) :
    Shape (gramRaw I s M) (I.family.dimension + numVars I) (2 * (I.degree + 1))
      (encRat 1).length ∧
    (∀ t ∈ gramRaw I s M, t.2 = 1) ∧ (gramRaw I s M).length = M.length ^ 3 := by
  have hrow (c : ℕ) :
      Shape (M.zipIdx.map fun a ↦
        (a.1 ++ unitExp (numVars I) (s + a.2 * M.length + c) 1, (1 : ℚ)))
        (I.family.dimension + numVars I) (I.degree + 1) (encRat 1).length := by
    intro t ht
    obtain ⟨⟨e, a⟩, ha, rfl⟩ := List.mem_map.1 ht
    have he := hM e (List.fst_mem_of_mem_zipIdx ha)
    refine ⟨by simp [he.1, (unitExp_shape _ _ _).1], ?_, le_rfl⟩
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact (he.2 x hx).trans (by omega)
    · exact ((unitExp_shape _ _ _).2 x hx).trans (by omega)
  constructor
  · intro t ht
    obtain ⟨c, _, ht⟩ := List.mem_flatMap.1 ht
    have hu : ∀ t ∈ M.zipIdx.map (fun a ↦
        (a.1 ++ unitExp (numVars I) (s + a.2 * M.length + c) 1, (1 : ℚ))),
        (∀ x ∈ t.1, x ≤ I.degree + 1) ∧ t.2 = 1 := by
      intro t ht
      refine ⟨(hrow c t ht).2.1, ?_⟩
      obtain ⟨a, _, rfl⟩ := List.mem_map.1 ht
      rfl
    simpa only [two_mul] using Shape.mul_one hu (hrow c) t ht
  constructor
  · intro z hz
    obtain ⟨c, _, hz⟩ := List.mem_flatMap.1 hz
    obtain ⟨s, hs, hz⟩ := List.mem_flatMap.1 hz
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hz
    obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
    obtain ⟨a', _, rfl⟩ := List.mem_map.1 ht
    norm_num
  · simp only [gramRaw, List.length_flatMap, mul_length, List.length_map,
      List.length_zipIdx, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
    ring

private theorem clean_shape {p : RawPoly} {d K b : ℕ}
    (hp : ∀ t ∈ p, t.1.sum ≤ K ∧ (encRat t.2).length ≤ b) :
    Shape (clean d p) d K b ∧ (clean d p).length ≤ p.length := by
  constructor
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ht
    have hs' := (List.mem_filter.1 hs).1
    refine ⟨by simp, ?_, (hp s hs').2⟩
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hx
    apply getD_le (fun x hx ↦ (List.single_le_sum (fun _ _ ↦ Nat.zero_le _) x hx).trans
      (hp s hs').1)
  · simpa [clean] using List.length_filter_le
      (fun t ↦ decide (SoS.Poly.coeff d p (SoS.Poly.expo d t.1) ≠ 0)) p

private theorem shape_encoding {p : RawPoly} {v E b : ℕ} (hp : Shape p v E b) :
    (encRawPoly p).length ≤ p.length * (2 * (2 * (v * (2 * E + 1)) + 1 + b) + 1) := by
  apply Rounding.RawAux.length_list_le
  intro t ht
  rw [Rounding.RawAux.length_pair]
  have he : (encList encNat t.1).length ≤ v * (2 * E + 1) :=
    (Rounding.RawAux.length_list_le encNat t.1 fun x hx ↦
      (Rounding.RawAux.length_nat_le x).trans ((hp t ht).2.1 x hx)).trans
        (Nat.mul_le_mul_right _ (hp t ht).1)
  have hb := (hp t ht).2.2
  omega

private theorem rat_four_bits (q : ℚ) :
    (encRat (4 * q)).length ≤ 4 * (encRat q).length + 6 := by
  have hn := congrArg Int.natAbs (Rat.num_mul_num_eq_num_mul_gcd (4 : ℚ) q)
  have hg : 0 < Nat.gcd (4 * q.num.natAbs) q.den :=
    Nat.gcd_pos_of_pos_right _ q.den_pos
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at hn
  have hn' : (4 * q).num.natAbs ≤ 4 * q.num.natAbs := by
    norm_num at hn
    have h := Nat.mul_le_mul_left (4 * q).num.natAbs (show 1 ≤
      Nat.gcd (4 * q.num.natAbs) q.den by omega)
    simpa only [Nat.mul_one, ← hn] using h
  have hd : (4 * q).den ≤ q.den := by
    have h := Rat.mul_den_dvd (4 : ℚ) q
    norm_num at h
    exact Nat.le_of_dvd q.den_pos h
  have hs : (4 * q.num.natAbs).size ≤ 4 * q.num.natAbs.size + 3 := by
    have h1 := Nat.size_add_le q.num.natAbs q.num.natAbs
    have h2 := Nat.size_add_le (q.num.natAbs + q.num.natAbs)
      (q.num.natAbs + q.num.natAbs)
    have he : 4 * q.num.natAbs =
        (q.num.natAbs + q.num.natAbs) + (q.num.natAbs + q.num.natAbs) := by omega
    rw [he]
    omega
  have hnum := (Nat.size_le_size hn').trans hs
  have hden := Nat.size_le_size hd
  have hlen (r : ℚ) : (encRat r).length =
      2 * r.num.natAbs.size + r.den.size + 3 := by
    change (encPair encInt encNat (r.num, r.den)).length = _
    rw [Rounding.RawAux.length_pair]
    change 2 * (r.num.natAbs.bits.length + 1) + 1 + r.den.bits.length = _
    simp only [← Nat.size_eq_bits_len]
    omega
  rw [hlen, hlen]
  omega

private theorem plain_basis_bound (I : Rounding.RawInput)
    (hfuel : (Rounding.nestedVars I.family.real I.degree + 2) ^
      (2 * I.degree + 2) ≤ I.fuel) (j : ℕ) (hj : j < I.family.plain.length + 1) :
    ((plainBases I).getD j []).length ≤ (I.family.dimension + 1) ^ I.degree ∧
      ∀ e ∈ (plainBases I).getD j [],
        e.length = I.family.dimension ∧ ∀ x ∈ e, x ≤ I.degree := by
  have hj' : j < (constant 1 :: I.family.plain).length := by simpa using hj
  rw [plainBases, List.getD_eq_getElem _ _ (by simpa using hj'), List.getElem_map,
    bases_uncapped I hfuel _ (by omega)]
  constructor
  · exact (SoS.Mono.length_all_le _ _).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  · intro e he
    obtain ⟨hlen, hsum⟩ := SoS.Mono.mem_all.1 he
    refine ⟨hlen, fun x hx ↦ ?_⟩
    exact (List.single_le_sum (fun _ _ ↦ Nat.zero_le _) x hx).trans (hsum.trans (by omega))

private theorem plain_template_bound (I : Rounding.RawInput) (support bits : ℕ)
    (hS : I.family.slots = [])
    (hfuel : (Rounding.nestedVars I.family.real I.degree + 2) ^
      (2 * I.degree + 2) ≤ I.fuel)
    (hp : ∀ p ∈ I.family.plain, p.length ≤ support ∧
      ∀ t ∈ p, t.1.sum ≤ I.degree ∧ (encRat t.2).length ≤ bits) :
    Shape (templateRaw I) (I.family.dimension + numVars I) (4 * (I.degree + 1))
      (bits + 8) ∧ (templateRaw I).length ≤
        (I.family.plain.length + 1) * (support + 1) *
          ((I.family.dimension + 1) ^ I.degree) ^ 3 := by
  have hslots : slots I = [] := by simp [slots, hS]
  have hps : ∀ p ∈ constant 1 :: I.family.plain, p.length ≤ support + 1 ∧
      ∀ t ∈ p, t.1.sum ≤ I.degree ∧ (encRat t.2).length ≤ bits + 8 := by
    intro p hp'
    rcases List.mem_cons.1 hp' with rfl | hp'
    · simp only [constant, List.length_cons, List.length_nil]
      refine ⟨by omega, ?_⟩
      intro t ht
      have : t = ([], (1 : ℚ)) := by simpa using ht
      subst t
      constructor
      · simp
      · change 6 ≤ bits + 8
        omega
    · exact ⟨(hp p hp').1.trans (by omega), fun t ht ↦
        ⟨(hp p hp').2 t ht |>.1, ((hp p hp').2 t ht).2.trans (by omega)⟩⟩
  have hblock (p : RawPoly × ℕ) (hp' : p ∈ (constant 1 :: I.family.plain).zipIdx) :
      Shape (SoS.Coords.mulRaw (I.family.dimension + numVars I)
        (gramRaw I (plainStart I p.2) ((plainBases I).getD p.2 []))
        (clean I.family.dimension p.1))
        (I.family.dimension + numVars I) (4 * (I.degree + 1)) (bits + 8) ∧
      (SoS.Coords.mulRaw (I.family.dimension + numVars I)
        (gramRaw I (plainStart I p.2) ((plainBases I).getD p.2 []))
        (clean I.family.dimension p.1)).length ≤
          (support + 1) * ((I.family.dimension + 1) ^ I.degree) ^ 3 := by
    have hj : p.2 < I.family.plain.length + 1 := by
      simpa using List.snd_lt_of_mem_zipIdx hp'
    obtain ⟨hrows, hM⟩ := plain_basis_bound I hfuel p.2 hj
    obtain ⟨hg, hu, hl⟩ := gram_shape I (plainStart I p.2) _ hM
    have hc := clean_shape (d := I.family.dimension)
      ((hps p.1 (List.fst_mem_of_mem_zipIdx hp')).2)
    constructor
    · exact (Shape.mul_one (fun t ht ↦ ⟨(hg t ht).2.1, hu t ht⟩)
        (hc.1.mono (by omega) le_rfl le_rfl)).mono le_rfl (by omega) le_rfl
    · rw [mul_length, hl]
      calc
        _ ≤ ((I.family.dimension + 1) ^ I.degree) ^ 3 * (support + 1) :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hrows _) (hc.2.trans
            (hps p.1 (List.fst_mem_of_mem_zipIdx hp')).1)
        _ = _ := by ring
  simp only [templateRaw, hslots, List.zipIdx_nil, List.flatMap_nil, List.append_nil]
  constructor
  · intro t ht
    obtain ⟨p, hp', ht⟩ := List.mem_flatMap.1 ht
    exact (hblock p hp').1 t ht
  · rw [List.length_flatMap]
    have h := List.sum_le_length_nsmul
      (((constant 1 :: I.family.plain).zipIdx).map fun p ↦
        (SoS.Coords.mulRaw (I.family.dimension + numVars I)
          (gramRaw I (plainStart I p.2) ((plainBases I).getD p.2 []))
          (clean I.family.dimension p.1)).length)
      ((support + 1) * ((I.family.dimension + 1) ^ I.degree) ^ 3) (by
        intro x hx
        obtain ⟨p, hp', rfl⟩ := List.mem_map.1 hx
        exact (hblock p hp').2)
    simpa [List.length_zipIdx, Nat.mul_assoc] using h

private theorem norm_shape (n d : ℕ) :
    Shape (normRaw n d) n 2 (encRat 1).length ∧ (normRaw n d).length = d := by
  refine ⟨?_, by simp [normRaw]⟩
  intro t ht
  obtain ⟨i, _, rfl⟩ := List.mem_map.1 ht
  exact ⟨(unitExp_shape _ _ _).1.le, (unitExp_shape _ _ _).2, le_rfl⟩

private theorem residual_bound (I : Rounding.RawInput) (support bits : ℕ)
    (hS : I.family.slots = [])
    (hfuel : (Rounding.nestedVars I.family.real I.degree + 2) ^
      (2 * I.degree + 2) ≤ I.fuel)
    (hp : ∀ p ∈ I.family.plain, p.length ≤ support ∧
      ∀ t ∈ p, t.1.sum ≤ I.degree ∧ (encRat t.2).length ≤ bits)
    (hε : (encRat I.epsilon).length ≤ bits) :
    Shape (residual I) (I.family.dimension + numVars I) (4 * (I.degree + 1))
      (4 * bits + 8) ∧ (residual I).length ≤ 1 + I.family.dimension ^ 2 +
        (I.family.plain.length + 1) * (support + 1) *
          ((I.family.dimension + 1) ^ I.degree) ^ 3 := by
  obtain ⟨ht, htl⟩ := plain_template_bound I support bits hS hfuel hp
  let uv : RawPoly := (List.range I.family.dimension).map fun i ↦
    (unitExp I.family.dimension i 1 ++ unitExp (numVars I) i 1, 1)
  have huv : Shape uv (I.family.dimension + numVars I) 1 (encRat 1).length := by
    intro t hmem
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hmem
    refine ⟨by simp [unitExp], ?_, le_rfl⟩
    intro x hx
    exact (List.mem_append.1 hx).elim ((unitExp_shape _ _ _).2 x)
      ((unitExp_shape _ _ _).2 x)
  have hu : ∀ t ∈ uv, (∀ x ∈ t.1, x ≤ 1) ∧ t.2 = 1 := by
    intro t hmem
    refine ⟨(huv t hmem).2.1, ?_⟩
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hmem
    rfl
  constructor
  · apply Shape.append
    · apply Shape.append
      · exact (Shape.constant _ _ _).mono le_rfl le_rfl
          ((rat_four_bits I.epsilon).trans (by omega))
      · exact ((Shape.mul_one hu huv).neg).mono le_rfl (by omega) (by
          change 6 ≤ 4 * bits + 8
          omega)
    · exact ht.neg.mono le_rfl le_rfl (by omega)
  · simpa only [residual, List.length_append, constant, scale, List.length_map,
      List.length_cons, List.length_nil, mul_length, List.length_range, pow_two] using
      Nat.add_le_add_left htl (1 + I.family.dimension * I.family.dimension)

private theorem split_shape {p : RawPoly} {v E b : ℕ} (hp : Shape p v E b)
    (d : ℕ) (μ : List ℕ) :
    Shape (Rounding.splitCoeffsRaw d μ p) v E b ∧
      (Rounding.splitCoeffsRaw d μ p).length ≤ p.length := by
  constructor
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ht
    obtain ⟨hl, he, hb⟩ := hp s (List.mem_filter.1 hs).1
    exact ⟨(by simp only [List.length_drop]; omega),
      fun x hx ↦ he x (List.mem_of_mem_drop hx), hb⟩
  · simpa only [Rounding.splitCoeffsRaw, List.length_map] using
      List.length_filter_le (fun t ↦ decide (SoS.Poly.expo d t.1 = μ)) p

private theorem constraints_bound (I : Rounding.RawInput) (support bits : ℕ)
    (hS : I.family.slots = [])
    (hfuel : (Rounding.nestedVars I.family.real I.degree + 2) ^
      (2 * I.degree + 2) ≤ I.fuel)
    (hp : ∀ p ∈ I.family.plain, p.length ≤ support ∧
      ∀ t ∈ p, t.1.sum ≤ I.degree ∧ (encRat t.2).length ≤ bits)
    (hε : (encRat I.epsilon).length ≤ bits) (hB : (encRat I.ball).length ≤ bits) :
    (constraints I).length ≤ 2 * (I.family.dimension + 1) ^ I.degree + 3 ∧
    ∀ p ∈ constraints I,
      Shape p (I.family.dimension + numVars I) (4 * (I.degree + 1)) (4 * bits + 8) ∧
      p.length ≤ 2 + numVars I + I.family.dimension ^ 2 +
        (I.family.plain.length + 1) * (support + 1) *
          ((I.family.dimension + 1) ^ I.degree) ^ 3 := by
  have hd : I.family.dimension ≤ numVars I := by
    rw [vars_agree I hfuel]
    exact Rounding.RawAux.dimension_le_vars _ _
  obtain ⟨hr, hrl⟩ := residual_bound I support bits hS hfuel hp hε
  have hs : Shape (normRaw (numVars I) I.family.dimension ++ constant (-1))
      (I.family.dimension + numVars I) (4 * (I.degree + 1)) (4 * bits + 8) := by
    apply Shape.append
    · exact (norm_shape _ _).1.mono (by omega) (by omega) (by change 6 ≤ _; omega)
    · exact (Shape.constant _ _ _).mono le_rfl le_rfl (by change 6 ≤ _; omega)
  have hb : Shape (constant I.ball ++ scale (-1) (normRaw (numVars I) (numVars I)))
      (I.family.dimension + numVars I) (4 * (I.degree + 1)) (4 * bits + 8) := by
    apply Shape.append
    · exact (Shape.constant _ _ _).mono le_rfl le_rfl (by omega)
    · exact (norm_shape _ _).1.neg.mono (by omega) (by omega) (by change 6 ≤ _; omega)
  constructor
  · have hl (M : List (List ℕ)) :
        (M.flatMap fun μ ↦ [Rounding.splitCoeffsRaw I.family.dimension μ (residual I),
          scale (-1) (Rounding.splitCoeffsRaw I.family.dimension μ (residual I))]).length =
            2 * M.length := by
      simp [List.length_flatMap, List.map_const', List.sum_replicate, Nat.mul_comm]
    simp only [constraints, List.length_append, List.length_cons, List.length_nil, hl]
    rw [bases_uncapped I hfuel _ le_rfl]
    have hm := SoS.Mono.length_all_le I.family.dimension I.degree
    omega
  · intro p hp'
    simp only [constraints, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, List.mem_flatMap] at hp'
    rcases hp' with ((rfl | rfl) | ⟨μ, _, rfl | rfl⟩) | rfl
    · exact ⟨hs, by simp [normRaw, constant]; omega⟩
    · exact ⟨hs.neg, by simp [scale, normRaw, constant]; omega⟩
    · exact ⟨(split_shape hr _ _).1, ((split_shape hr _ _).2.trans hrl).trans (by omega)⟩
    · exact ⟨(split_shape hr _ _).1.neg, by
        simpa only [scale, List.length_map] using
          ((split_shape hr I.family.dimension μ).2.trans hrl).trans (by omega)⟩
    · exact ⟨hb, by simp [constant, scale, normRaw]; omega⟩

private theorem storage_factors (M S B A : ℕ) (hM : 2 ≤ M) (hS : 2 ≤ S)
    (hB : 2 ≤ B) (hA : 2 ≤ A) :
    16 ≤ M * S * B * A ^ 8 ∧ M * A ≤ M * S * B * A ^ 8 ∧
      2 * B ≤ M * S * B * A ^ 8 ∧ 2 * A + 3 ≤ M * S * B * A ^ 8 ∧
      4 * (M * S * A ^ 3) ≤ M * S * B * A ^ 8 ∧
      100 * M * B * A ≤ M * S * B * A ^ 8 := by
  have hpow (k : ℕ) : 2 ^ k ≤ A ^ k := Nat.pow_le_pow_left hA k
  have hlinear : A ≤ A ^ 8 := Nat.le_self_pow (by omega) _
  have hprod : 4 ≤ M * S := by
    calc 4 = 2 * 2 := by norm_num
         _ ≤ M * S := Nat.mul_le_mul hM hS
  have hcoeff : M ≤ M * S * B := by
    calc M ≤ M * S := Nat.le_mul_of_pos_right _ (by omega)
         _ ≤ M * S * B := Nat.le_mul_of_pos_right _ (by omega)
  refine ⟨?_, Nat.mul_le_mul hcoeff hlinear, ?_, ?_, ?_, ?_⟩
  · calc
      16 ≤ 2 * 2 * 2 * 2 ^ 8 := by norm_num
      _ ≤ M * S * B * A ^ 8 := by gcongr
  · calc
      2 * B ≤ (M * S) * B * A ^ 8 := by
        have h1 : 2 * B ≤ (M * S) * B := Nat.mul_le_mul_right _ (by omega)
        exact h1.trans (Nat.le_mul_of_pos_right _ (by positivity))
      _ = _ := rfl
  · calc
      2 * A + 3 ≤ 4 * A := by omega
      _ ≤ (M * S * B) * A ^ 8 := by
        apply Nat.mul_le_mul _ hlinear
        exact hprod.trans (Nat.le_mul_of_pos_right _ (by omega))
  · have h : 4 ≤ B * A ^ 5 := by
      calc 4 ≤ 2 * 2 ^ 5 := by norm_num
           _ ≤ B * A ^ 5 := Nat.mul_le_mul hB (hpow 5)
    calc
      4 * (M * S * A ^ 3) ≤ (B * A ^ 5) * (M * S * A ^ 3) :=
        Nat.mul_le_mul_right _ h
      _ = M * S * B * A ^ 8 := by rw [show A ^ 8 = A ^ 3 * A ^ 5 by ring]; ring
  · have h : 100 ≤ S * A ^ 7 := by
      calc 100 ≤ 2 * 2 ^ 7 := by norm_num
           _ ≤ S * A ^ 7 := Nat.mul_le_mul hS (hpow 7)
    calc
      100 * M * B * A ≤ (S * A ^ 7) * M * B * A := by gcongr
      _ = M * S * B * A ^ 8 := by rw [show A ^ 8 = A * A ^ 7 by ring]; ring

private theorem term_storage (v E b M B A : ℕ) (hM : 2 ≤ M) (hB : 2 ≤ B)
    (hA : 2 ≤ A) (hv : v ≤ 2 * M * A) (he : E ≤ 9 * B) (hb : b ≤ 4 * B) :
    2 * v * E + 1 + b ≤ 100 * M * B * A := by
  have hMA : 4 ≤ M * A := by
    calc 4 = 2 * 2 := by norm_num
         _ ≤ M * A := Nat.mul_le_mul hM hA
  calc
    2 * v * E + 1 + b ≤ 2 * (2 * M * A) * (9 * B) + 1 + 4 * B := by gcongr
    _ = (36 * (M * A) + 4) * B + 1 := by ring
    _ ≤ 100 * (M * A) * B := by nlinarith only [hMA, hB]
    _ = _ := by ring

private theorem term_count_storage (d n m support R M S A : ℕ)
    (hM : 2 ≤ M) (hS : 2 ≤ S) (hA : 2 ≤ A) (hd : d ≤ A) (hR : R ≤ A)
    (hm : m + 1 ≤ M) (hs : support + 1 ≤ S) (hn : n ≤ M * A) :
    2 + n + d ^ 2 + (m + 1) * (support + 1) * R ^ 3 ≤ 4 * (M * S * A ^ 3) := by
  have hA3 : A ≤ A ^ 3 := Nat.le_self_pow (by omega) _
  have htemp : (m + 1) * (support + 1) * R ^ 3 ≤ M * S * A ^ 3 := by gcongr
  have hdim : d ^ 2 ≤ M * S * A ^ 3 := by
    have h1 : d ^ 2 ≤ A ^ 2 := Nat.pow_le_pow_left hd _
    have h2 : A ^ 2 ≤ A ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    exact (h1.trans h2).trans (Nat.le_mul_of_pos_left _ (by positivity))
  have hnum : n ≤ M * S * A ^ 3 := by
    apply hn.trans
    calc M * A ≤ M * A ^ 3 := Nat.mul_le_mul_left _ hA3
         _ ≤ M * S * A ^ 3 := Nat.mul_le_mul_right _
           (Nat.le_mul_of_pos_right _ (by omega))
  have htwo : 2 ≤ M * S * A ^ 3 := by
    calc 2 ≤ A ^ 3 := hA.trans hA3
         _ ≤ M * S * A ^ 3 := Nat.le_mul_of_pos_left _ (by positivity)
  omega

private theorem storage_margins (W : ℕ) (hW : 16 ≤ W) :
    W * (2 * W + 1) ≤ 3 * W ^ 2 ∧ W * (6 * W ^ 2 + 1) ≤ 7 * W ^ 3 ∧
      4 * W + 14 * W ^ 3 + 4 ≤ W ^ 4 := by
  have hcube : W ≤ W ^ 3 := Nat.le_self_pow (by omega) _
  have hpow : 16 * W ^ 3 ≤ W ^ 4 := by
    calc 16 * W ^ 3 ≤ W * W ^ 3 := Nat.mul_le_mul_right _ hW
         _ = W ^ 4 := by ring
  have hs : 4 ≤ W ^ 2 := by
    exact (by norm_num : 4 ≤ 2 ^ 2).trans (Nat.pow_le_pow_left (by omega) _)
  have h := Nat.mul_le_mul_left (2 * W) hs
  refine ⟨by nlinarith only [hW], by nlinarith only [hcube], ?_⟩
  nlinarith only [hW, h, hpow]

private theorem problem_storage (n deg v E b W : ℕ) (ps : List RawPoly)
    (hW : 16 ≤ W) (hn : (encNat n).length ≤ W) (hd : (encNat deg).length ≤ W)
    (hc : ps.length ≤ W)
    (hp : ∀ p ∈ ps, Shape p v E b ∧ p.length ≤ W)
    (ht : 2 * v * (2 * E + 1) + 1 + b ≤ W) :
    (encProblem (n, deg, ps, [], [])).length ≤ W ^ 4 := by
  obtain ⟨hm1, hm2, hm3⟩ := storage_margins W hW
  have hpoly : ∀ p ∈ ps, (encRawPoly p).length ≤ 3 * W ^ 2 := by
    intro p hp'
    obtain ⟨hs, hl⟩ := hp p hp'
    have he := shape_encoding hs
    have hrow : 2 * (2 * (v * (2 * E + 1)) + 1 + b) + 1 ≤ 2 * W + 1 := by
      nlinarith only [ht]
    exact he.trans ((Nat.mul_le_mul hl hrow).trans hm1)
  have hconstraints : (encList encRawPoly ps).length ≤ 7 * W ^ 3 := by
    have h := Rounding.RawAux.length_list_le encRawPoly ps hpoly
    exact h.trans ((Nat.mul_le_mul_right _ hc).trans (by
      simpa only [← Nat.mul_assoc, Nat.reduceMul] using hm2))
  rw [SoS.Correct.length_encProblem]
  change 2 * (encNat n).length + 1 + (2 * (encNat deg).length + 1 +
    (2 * (encList encRawPoly ps).length + 1 + (0 + 1 + 0))) ≤ W ^ 4
  omega

private theorem fourth_bound (d K m support bits : ℕ) :
    ((m + 2) * (support + 2) * (bits + K + 2) * ((d + 2) ^ (K + 1)) ^ 8) ^ 4 =
      sparseBound d K m support bits := by
  unfold sparseBound
  rw [mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul]
  rw [show (K + 1) * (8 * 4) = 32 * (K + 1) by ring]

private theorem plain_storage_numeric (n deg d K m support bits : ℕ) (ps : List RawPoly)
    (hn : n ≤ (m + 2) * (d + 2) ^ (K + 1)) (hdeg : deg ≤ 2 * K + 4)
    (hcount : ps.length ≤ 2 * (d + 1) ^ K + 3)
    (hpolys : ∀ p ∈ ps, Shape p (d + n) (4 * (K + 1)) (4 * bits + 8) ∧
      p.length ≤ 2 + n + d ^ 2 + (m + 1) * (support + 1) * ((d + 1) ^ K) ^ 3) :
    (encProblem (n, deg, ps, [], [])).length ≤ sparseBound d K m support bits := by
  let A := (d + 2) ^ (K + 1)
  let M := m + 2
  let S := support + 2
  let B := bits + K + 2
  let W := M * S * B * A ^ 8
  change n ≤ M * A at hn
  have hA : 2 ≤ A := by
    dsimp [A]
    exact (show 2 ≤ d + 2 by omega).trans
      (Nat.le_self_pow (by omega) _)
  have hM : 2 ≤ M := by omega
  have hS' : 2 ≤ S := by omega
  have hB' : 2 ≤ B := by omega
  have hd : d ≤ A := by
    have h := Nat.le_self_pow (show K + 1 ≠ 0 by omega) (d + 2)
    exact (by omega : d ≤ d + 2).trans h
  have hR : (d + 1) ^ K ≤ A :=
    (Nat.pow_le_pow_left (by omega) _).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  obtain ⟨hW, hsmall, h2B, h2A, hfour, hhundred⟩ := storage_factors M S B A hM hS' hB' hA
  have hdbits : (encNat (deg)).length ≤ W := by
    have h1 : 2 * K + 4 ≤ 2 * B := by omega
    exact (Rounding.RawAux.length_nat_le _).trans (hdeg.trans (h1.trans h2B))
  have hnbits := (Rounding.RawAux.length_nat_le (n)).trans (hn.trans hsmall)
  have hcountW : (ps).length ≤ W := by
    apply hcount.trans
    exact (by omega : 2 * (d + 1) ^ K + 3 ≤ 2 * A + 3).trans h2A
  have hterms : 2 + n + d ^ 2 +
      (m + 1) * (support + 1) *
        ((d + 1) ^ K) ^ 3 ≤ W := by
    exact (term_count_storage _ _ _ _ _ _ _ _ hM hS' hA hd hR (by omega)
      (by omega) hn).trans hfour
  have hterm : 2 * (d + n) *
      (2 * (4 * (K + 1)) + 1) + 1 + (4 * bits + 8) ≤ W := by
    have hv : d + n ≤ 2 * M * A := by
      have h := Nat.le_mul_of_pos_left A (show 0 < M by omega)
      calc
        d + n ≤ A + M * A := Nat.add_le_add hd hn
        _ ≤ M * A + M * A := Nat.add_le_add_right h _
        _ = _ := by ring
    have he : 2 * (4 * (K + 1)) + 1 ≤ 9 * B := by omega
    have hb : 4 * bits + 8 ≤ 4 * B := by omega
    exact (term_storage _ _ _ _ _ _ hM hB' hA hv he hb).trans hhundred
  have hproblem := problem_storage _ _ _ _ _ W (ps) hW hnbits hdbits hcountW
    (fun p hp' ↦ ⟨(hpolys p hp').1, (hpolys p hp').2.trans hterms⟩) hterm
  exact hproblem.trans_eq (fourth_bound d K m support bits)

/-- A direct count of sparse terms gives the stated linear dimension exponent. -/
theorem concrete_plain_size (I : Rounding.RawInput) (support bits : ℕ)
    (hF : I.family.families = []) (hS : I.family.slots = [])
    (_hI : I.family.real.Valid I.degree)
    (hfuel : (Rounding.nestedVars I.family.real I.degree + 2) ^
      (2 * I.degree + 2) ≤ I.fuel)
    (hp : ∀ p ∈ I.family.plain, p.length ≤ support ∧
      ∀ t ∈ p, t.1.sum ≤ I.degree ∧ (encRat t.2).length ≤ bits)
    (hε : (encRat I.epsilon).length ≤ bits) (hB : (encRat I.ball).length ≤ bits) :
    (encProblem (numVars I, degree I, constraints I, [], [])).length ≤
      sparseBound I.family.dimension I.degree I.family.plain.length support bits := by
  obtain ⟨hcount, hpolys⟩ := constraints_bound I support bits hS hfuel hp hε hB
  apply plain_storage_numeric _ _ _ _ _ _ _ _ ?_ ?_ hcount hpolys
  · rw [vars_agree I hfuel]
    have h := (Rounding.nested_size I.family.real I.degree I.epsilon I.ball).1
    have hl : I.family.real.plain.length = I.family.plain.length := by
      simp [Rounding.RawFamily.real]
    have hs : I.family.real.slots = [] := by simp [Rounding.RawFamily.real, hS]
    rw [hs, List.length_nil, hl] at h
    simp only [add_zero, zero_mul] at h
    apply h.trans
    have hd : I.family.dimension ≤ (I.family.dimension + 2) ^ (I.degree + 1) :=
      (by omega : I.family.dimension ≤ I.family.dimension + 2).trans
        (Nat.le_self_pow (by omega) _)
    have hR : (I.family.dimension + 1) ^ I.degree ≤
        (I.family.dimension + 2) ^ (I.degree + 1) :=
      (Nat.pow_le_pow_left (by omega) _).trans
        (Nat.pow_le_pow_right (by omega) (by omega))
    calc
      _ ≤ (I.family.dimension + 2) ^ (I.degree + 1) + (I.family.plain.length + 1) *
          (I.family.dimension + 2) ^ (I.degree + 1) := by gcongr
      _ = _ := by ring
  · simp only [degree, hF, List.map_nil, List.foldl_nil]
    omega

end ABBKS26.Assembly.Exec.NestedProgram
