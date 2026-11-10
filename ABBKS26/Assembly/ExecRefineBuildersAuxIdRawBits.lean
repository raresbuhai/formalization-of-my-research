module

public import ABBKS26.Assembly.ExecRefineBuildersAuxIdBits

/-! Sparse term counts, degrees, and rational bits before nested SUB reification. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.IdRawBits

open Common _root_.ABBKS26.Tree Sources Builders
open _root_.ABBKS26.Schedule.EncodingBounds
open SoS.Solver (RawPoly encRawPoly)
open scoped BigOperators

noncomputable section

structure Bound (d r L b : ℕ) (p : RawPoly) : Prop where
  length : p.length ≤ L
  terms : ∀ t ∈ p, t.1.length ≤ d ∧ t.1.sum ≤ r ∧ RatBound b t.2

theorem Bound.mono {d r R L M b c : ℕ} {p : RawPoly} (h : Bound d r L b p)
    (hr : r ≤ R) (hL : L ≤ M) (hb : b ≤ c) : Bound d R M c p :=
  ⟨h.length.trans hL, fun t ht ↦ ⟨(h.terms t ht).1, (h.terms t ht).2.1.trans hr,
    (h.terms t ht).2.2.mono hb⟩⟩

theorem Bound.append {d r s L M b c : ℕ} {p q : RawPoly}
    (hp : Bound d r L b p) (hq : Bound d s M c q) :
    Bound d (max r s) (L + M) (max b c) (p ++ q) := by
  refine ⟨by simpa only [List.length_append] using Nat.add_le_add hp.length hq.length, ?_⟩
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · exact ⟨(hp.terms t ht).1, (hp.terms t ht).2.1.trans (le_max_left _ _),
      (hp.terms t ht).2.2.mono (le_max_left _ _)⟩
  · exact ⟨(hq.terms t ht).1, (hq.terms t ht).2.1.trans (le_max_right _ _),
      (hq.terms t ht).2.2.mono (le_max_right _ _)⟩

theorem Bound.scale {d r L b c : ℕ} {p : RawPoly} (hp : Bound d r L b p)
    (v : ℚ) (hv : RatBound c v) : Bound d r L (c + b) (NestedProgram.scale v p) := by
  refine ⟨by simpa only [NestedProgram.scale, List.length_map] using hp.length, ?_⟩
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact ⟨(hp.terms s hs).1, (hp.terms s hs).2.1, hv.mul (hp.terms s hs).2.2⟩

theorem constant (d : ℕ) (c : ℚ) (b : ℕ) (hc : RatBound b c) :
    Bound d 0 1 b (NestedProgram.constant c) := by
  refine ⟨by simp [NestedProgram.constant], ?_⟩
  intro t ht
  have he : t = ([], c) := by simpa only [NestedProgram.constant,
    List.mem_cons, List.not_mem_nil, or_false] using ht
  subst t
  exact ⟨Nat.zero_le _, le_rfl, hc⟩

theorem sum_getD_le (d : ℕ) (xs : List ℕ) :
    (∑ i : Fin d, xs.getD i.val 0) ≤ xs.sum := by
  induction d generalizing xs with
  | zero => simp
  | succ d ih =>
    cases xs with
    | nil => simp
    | cons x xs => simpa [Fin.sum_univ_succ] using Nat.add_le_add_left (ih xs) x

theorem sum_range {d : ℕ} (f : ℕ → ℕ) :
    ((List.range d).map f).sum = ∑ i : Fin d, f i.val := by
  induction d with
  | zero => simp
  | succ d ih => simp [List.range_succ, ih, Fin.sum_univ_castSucc]

theorem addE_sum (d : ℕ) (xs ys : List ℕ) :
    (SoS.Poly.addE d xs ys).sum ≤ xs.sum + ys.sum := by
  rw [SoS.Poly.addE, sum_range, Finset.sum_add_distrib]
  exact Nat.add_le_add (sum_getD_le d xs) (sum_getD_le d ys)

theorem Bound.mul {d r s L M b c : ℕ} {p q : RawPoly}
    (hp : Bound d r L b p) (hq : Bound d s M c q) :
    Bound d (r + s) (L * M) (b + c) (SoS.Coords.mulRaw d p q) := by
  refine ⟨?_, ?_⟩
  · have he : (SoS.Coords.mulRaw d p q).length = p.length * q.length := by
      simp [SoS.Coords.mulRaw, List.length_flatMap]
    rw [he]
    exact Nat.mul_le_mul hp.length hq.length
  · intro t ht
    obtain ⟨s, hs, ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    exact ⟨by simp, (addE_sum d s.1 u.1).trans
      (Nat.add_le_add (hp.terms s hs).2.1 (hq.terms u hu).2.1),
      (hp.terms s hs).2.2.mul (hq.terms u hu).2.2⟩

theorem sections (fuel s : ℕ) (p : RawPoly) :
    (SoS.Poly.sectB fuel (List.replicate s p)).length ≤ p.length ^ s ∧
      ∀ xs ∈ SoS.Poly.sectB fuel (List.replicate s p),
        xs.length = s ∧ ∀ t ∈ xs, t ∈ p := by
  induction s with
  | zero => simp [SoS.Poly.sectB]
  | succ s ih =>
    have he : SoS.Poly.sectB fuel (List.replicate (s + 1) p) =
        SoS.Poly.sectStep fuel (SoS.Poly.sectB fuel (List.replicate s p)) p := by
      rw [show List.replicate (s + 1) p = List.replicate s p ++ [p] by
        simp [List.replicate_add]]
      simp only [SoS.Poly.sectB, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [he]
    refine ⟨?_, ?_⟩
    · unfold SoS.Poly.sectStep
      have hl : ((SoS.Poly.sectB fuel (List.replicate s p)).flatMap
          fun xs ↦ p.map fun a ↦ xs ++ [a]).length =
            (SoS.Poly.sectB fuel (List.replicate s p)).length * p.length := by
        simp [List.length_flatMap]
      rw [List.length_take, hl, pow_succ]
      exact (Nat.min_le_right _ _).trans (Nat.mul_le_mul_right _ ih.1)
    · intro xs hxs
      obtain ⟨ys, hys, hxs⟩ := List.mem_flatMap.mp (List.mem_of_mem_take hxs)
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hxs
      refine ⟨by simp [(ih.2 ys hys).1], ?_⟩
      intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · exact (ih.2 ys hys).2 u hu
      · have he : u = t := by simpa using hu
        simpa only [he] using ht

theorem prod_bound {b : ℕ} (xs : List ℚ) (h : ∀ x ∈ xs, RatBound b x) :
    RatBound (xs.length * b) xs.prod := by
  induction xs with
  | nil => simpa using RatBound.one
  | cons x xs ih =>
    simpa only [List.prod_cons, List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm]
      using (h x List.mem_cons_self).mul (ih (fun y hy ↦ h y (List.mem_cons_of_mem _ hy)))

theorem sumE_sum (d : ℕ) (xs : RawPoly) :
    (SoS.Poly.sumE d xs).sum ≤ (xs.map fun t ↦ t.1.sum).sum := by
  induction xs with
  | nil => simp [SoS.Poly.sumE]
  | cons t xs ih =>
    have he : (SoS.Poly.sumE d (t :: xs)).sum =
        (∑ i : Fin d, t.1.getD i.val 0) + (SoS.Poly.sumE d xs).sum := by
      simp only [SoS.Poly.sumE, List.map_cons, List.sum_cons, sum_range,
        Finset.sum_add_distrib]
    rw [he, List.map_cons, List.sum_cons]
    exact Nat.add_le_add (sum_getD_le d t.1) ih

theorem Bound.power {d r L b : ℕ} {p : RawPoly} (hp : Bound d r L b p)
    (fuel s : ℕ) : Bound d (s * r) ((L + 1) ^ s) (s * b)
      (IdSystem.power d fuel s p) := by
  have hz : RatBound b 0 := RatBound.zero b
  have hp' := hp.append (constant d 0 b hz)
  have hlen := (sections fuel s (p ++ NestedProgram.constant 0)).1
  refine ⟨?_, ?_⟩
  · calc
      _ ≤ (p ++ NestedProgram.constant 0).length ^ s := by
        simpa only [IdSystem.power, SoS.Poly.prodRaw, List.length_map] using hlen
      _ ≤ _ := Nat.pow_le_pow_left hp'.length s
  · intro t ht
    obtain ⟨xs, hxs, rfl⟩ := List.mem_map.mp ht
    obtain ⟨hlen, hmem⟩ := (sections fuel s (p ++ NestedProgram.constant 0)).2 xs hxs
    refine ⟨by simp [SoS.Poly.prodTerm, SoS.Poly.sumE], ?_, ?_⟩
    · apply (sumE_sum d xs).trans
      calc
        _ ≤ (xs.map fun _ ↦ r).sum := by
          apply List.sum_le_sum
          intro u hu
          exact (hp'.terms u (hmem u hu)).2.1.trans (by omega)
        _ = _ := by simp [hlen]
    · have hb := prod_bound (b := b) (xs.map Prod.snd) (by
        intro q hq
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hq
        exact (hp'.terms u (hmem u hu)).2.2.mono (by omega))
      simpa only [SoS.Poly.prodTerm, List.length_map, hlen] using hb


theorem normSq (d : ℕ) : Bound d 2 d 0 (MomentProgram.normSq d) := by
  refine ⟨by simp [MomentProgram.normSq], ?_⟩
  intro t ht
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
  have hi : i < d := List.mem_range.mp hi
  refine ⟨by simp [MomentProgram.unitExp], ?_, RatBound.one⟩
  rw [MomentProgram.unitExp, sum_range]
  have he : (fun j : Fin d ↦ if j.val = i then (2 : ℕ) else 0) =
      fun j ↦ if j = ⟨i, hi⟩ then 2 else 0 := by
    funext j
    simp only [Fin.ext_iff]
  rw [he]
  simp

theorem alpha (s B : ℕ) (hB : 100 ≤ B) (hs : s ≤ 2 * B) :
    RatBound (B ^ 4) (IdSystem.alpha s) := by
  have hb : RatBound (s * (4 * B + 1)) (IdSystem.alpha s) := by
    simpa only [IdSystem.alpha, List.length_map, List.length_range] using
      prod_bound ((List.range s).map fun j : ℕ ↦ 2 * (j : ℚ) + 1) (by
        intro q hq
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
        have hj : j < s := List.mem_range.mp hj
        simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
          IdBits.nat_coarse (2 * j + 1) (4 * B + 1) (by omega))
  apply hb.mono
  have hp : 100 * B ^ 2 ≤ B ^ 3 := IdBits.hundred_pow B 2 hB
  have hp' : 100 * B ^ 3 ≤ B ^ 4 := IdBits.hundred_pow B 3 hB
  have hm : s * B ≤ 2 * B ^ 2 := by nlinarith only [Nat.mul_le_mul_right B hs]
  nlinarith only [hB, hs, hp, hp', hm]

theorem deviation (d fuel s B : ℕ) (moments : ℕ → RawPoly) (hB : 100 ≤ B)
    (hs : s ≤ 2 * B)
    (hm : Bound d (2 * s) ((d + 1) ^ (2 * s)) (B ^ 11 * (d + 2)) (moments (2 * s)))
    (h2 : Bound d 2 ((d + 1) ^ 2) (B ^ 11 * (d + 2)) (moments 2)) :
    Bound d (2 * s) ((d + 2) ^ (3 * s + 1)) (B ^ 13 * (d + 2))
      (IdSystem.deviation d fuel s moments) := by
  have hb := hm.append ((h2.power fuel s).scale _ (alpha s B hB hs).neg)
  apply hb.mono (by omega) _ _
  · have hfirst : (d + 1) ^ (2 * s) ≤ (d + 2) ^ (3 * s) :=
      (Nat.pow_le_pow_left (by omega) _).trans
        (Nat.pow_le_pow_right (by omega) (by omega))
    have hsecond : ((d + 1) ^ 2 + 1) ^ s ≤ (d + 2) ^ (3 * s) := by
      calc
        _ ≤ ((d + 2) ^ 3) ^ s := Nat.pow_le_pow_left (by ring_nf; omega) s
        _ = _ := (pow_mul _ _ _).symm
    calc
      _ ≤ (d + 2) ^ (3 * s) + (d + 2) ^ (3 * s) := Nat.add_le_add hfirst hsecond
      _ = 2 * (d + 2) ^ (3 * s) := by omega
      _ ≤ (d + 2) * (d + 2) ^ (3 * s) := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' (d + 2) (3 * s)).symm
  · apply max_le
    · exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by norm_num))
    · have hp : 100 * B ^ 12 * (d + 2) ≤ B ^ 13 * (d + 2) :=
        Nat.mul_le_mul_right _ (IdBits.hundred_pow B 12 hB)
      have hB4 := IdBits.power_linear B d 4 12 (by omega) (by norm_num)
      have hm : B ^ 11 * s ≤ 2 * B ^ 12 := by
        nlinarith only [Nat.mul_le_mul_left (B ^ 11) hs]
      have hm' := Nat.mul_le_mul_right (d + 2) hm
      have he : s * (B ^ 11 * (d + 2)) ≤ 2 * (B ^ 12 * (d + 2)) := by
        convert hm' using 1 <;> ring
      calc
        _ ≤ 3 * (B ^ 12 * (d + 2)) := by omega
        _ ≤ 100 * (B ^ 12 * (d + 2)) := Nat.mul_le_mul_right _ (by norm_num)
        _ ≤ _ := by simpa only [Nat.mul_assoc] using hp

theorem constraint (d t fuel s B : ℕ) (ε : ℚ) (moments : ℕ → RawPoly)
    (hB : 100 ≤ B) (ht : 3 ≤ t ∧ t ≤ B) (hs : s ≤ 2 * t)
    (hε : RatBound (B ^ 3) ε)
    (hm : Bound d (2 * s) ((d + 1) ^ (2 * s)) (B ^ 11 * (d + 2)) (moments (2 * s)))
    (h2 : Bound d 2 ((d + 1) ^ 2) (B ^ 11 * (d + 2)) (moments 2)) :
    Bound d (8 * t) ((d + 2) ^ (16 * t)) (B ^ 14 * (d + 2))
      (IdSystem.constraint d fuel s ε moments) := by
  have hdev := deviation d fuel s B moments hB (by omega) hm h2
  have hneg : RatBound 0 (-1) := RatBound.one.neg
  have hb := (((normSq d).power fuel (2 * s)).scale ε hε).append
    ((hdev.mul hdev).scale (-1) hneg)
  apply hb.mono (by omega) _ _
  · have hfirst : (d + 1) ^ (2 * s) ≤ (d + 2) ^ (6 * s + 2) :=
      (Nat.pow_le_pow_left (by omega) _).trans
        (Nat.pow_le_pow_right (by omega) (by omega))
    have hsecond : (d + 2) ^ (3 * s + 1) * (d + 2) ^ (3 * s + 1) =
        (d + 2) ^ (6 * s + 2) := by rw [← pow_add]; congr 1; omega
    apply le_trans _ (Nat.pow_le_pow_right (by omega : 1 ≤ d + 2)
      (show 6 * s + 3 ≤ 16 * t by omega))
    rw [hsecond]
    calc
      _ ≤ 2 * (d + 2) ^ (6 * s + 2) := by omega
      _ ≤ (d + 2) * (d + 2) ^ (6 * s + 2) := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' (d + 2) (6 * s + 2)).symm
  · apply max_le
    · have he : B ^ 3 ≤ B ^ 14 := Nat.pow_le_pow_right (by omega) (by norm_num)
      simpa only [mul_zero, add_zero] using
        he.trans (Nat.le_mul_of_pos_right _ (by omega : 0 < d + 2))
    · have hp : 100 * B ^ 13 * (d + 2) ≤ B ^ 14 * (d + 2) :=
        Nat.mul_le_mul_right _ (IdBits.hundred_pow B 13 hB)
      calc
        _ = 2 * (B ^ 13 * (d + 2)) := by omega
        _ ≤ 100 * (B ^ 13 * (d + 2)) := Nat.mul_le_mul_right _ (by norm_num)
        _ ≤ _ := by simpa only [Nat.mul_assoc] using hp

theorem system (d t fuel B : ℕ) (ε : ℚ) (moments : ℕ → RawPoly)
    (hB : 100 ≤ B) (ht : 3 ≤ t ∧ t ≤ B) (hε : RatBound (B ^ 3) ε)
    (hm : ∀ s, 1 ≤ s → s ≤ 2 * t →
      Bound d (2 * s) ((d + 1) ^ (2 * s)) (B ^ 11 * (d + 2)) (moments (2 * s))) :
    ∀ p ∈ IdSystem.run d t fuel ε moments,
      Bound d (8 * t) ((d + 2) ^ (16 * t)) (B ^ 14 * (d + 2)) p := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · have he : p = NestedProgram.constant 1 ++
        NestedProgram.scale (-1) (MomentProgram.normSq d) := by simpa using hp
    rw [he]
    have hb := (constant d 1 0 RatBound.one).append
      ((normSq d).scale (-1) RatBound.one.neg)
    apply hb.mono (by omega) _ (by omega)
    have hbase : 1 + d ≤ d + 2 := by omega
    exact hbase.trans (le_self_pow₀ (by omega) (by omega))
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hp).1
    have hj : j < 2 * t - 1 := List.mem_range.mp hj
    exact constraint d t fuel (j + 2) B ε moments hB ht (by omega) hε
      (hm (j + 2) (by omega) (by omega)) (by simpa using hm 1 (by omega) (by omega))


/-- Magnitude clamping, canonical enumeration, and raw products give a sparse envelope
independent of the sample coordinates and of excessive external fuel. -/
theorem prepared {n k d : ℕ} (MC : MomentCode)
    (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ) (fuel h : ℕ) (P : Finset (Fin n))
    (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ) (ω : Fin n → Triple k d)
    (r : Rounding k d) (hp : Prepared .identical M ε w η Δ D ω r ps)
    (hf : localBudget .identical k n d ps ≤ fuel) (hh : h < k - 1) :
    let a := (args k ps x h P, fuel)
    let B := idReserve k (ps h)
    ∀ p ∈ IdReify.system MC a,
      Bound d (8 * IdInput.degree a) ((d + 2) ^ (16 * IdInput.degree a))
        (B ^ 14 * (d + 2)) p := by
  let a := (args k ps x h P, fuel)
  let B := idReserve k (ps h)
  have hs := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h hh
  have hβ : 0 ≤ (ps h).subspaceAccuracy ∧ (ps h).subspaceAccuracy ≤ 1 :=
    ⟨hs.2.2.1.le, hs.2.2.2.1.trans (by norm_num)⟩
  obtain ⟨hB, ht, hA, hβ, hden, _⟩ := IdBits.inputs k ps x fuel h P (by omega) hβ
  have ht3 : 3 ≤ IdInput.degree a := by unfold IdInput.degree IdCov.tDegree; omega
  have hε := IdBits.systemError a B hB ht hβ hden
  have hprec := IdBits.precision a B hB ht hβ hden
  have hexp := IdBits.exponent a B hB ht hA hβ hden
  change IdPayload.precision a ≤ B ^ 5 * (d + 2) at hprec
  change IdPayload.exponent a ≤ B ^ 9 * (d + 2) at hexp
  have hm (s : ℕ) (hs1 : 1 ≤ s) (hs : s ≤ 2 * IdInput.degree a) :
      Bound d (2 * s) ((d + 1) ^ (2 * s)) (B ^ 11 * (d + 2))
        (IdPayload.moment MC a (2 * s)) := by
    have hfields := (IdReify.fields k ps x fuel h P (by omega)).1
    change IdInput.degree a = IdCov.tDegree (ps h).w at hfields
    obtain ⟨hr, he⟩ := IdPrepared.enumeration ps fuel h M ε w η Δ D ω r hp hf hh
      (2 * s) (by rw [← hfields]; omega)
    refine ⟨IdRound.length_run d (2 * s) fuel _ _ _ hr he, ?_⟩
    intro t ht'
    obtain ⟨hlen, hsum, hbits⟩ := IdRound.term_bounds d (2 * s) fuel _ _ _ hr he t ht'
    refine ⟨hlen.le, hsum, (of_encoding hbits).mono ?_⟩
    have h59 : B ^ 5 ≤ B ^ 9 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have hp9 := hprec.trans (Nat.mul_le_mul_right (d + 2) h59)
    have h0 : 1 ≤ B ^ 9 * (d + 2) := Nat.mul_pos (Nat.pow_pos (by omega)) (by omega)
    calc
      _ ≤ 100 * B ^ 9 * (d + 2) := by nlinarith only [hexp, hp9, h0]
      _ ≤ B ^ 10 * (d + 2) := Nat.mul_le_mul_right _ (IdBits.hundred_pow B 9 hB)
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by norm_num))
  exact system d (IdInput.degree a) fuel B (IdPayload.systemError a)
    (IdPayload.moment MC a) hB ⟨ht3, ht⟩ hε hm


end

end ABBKS26.Assembly.Exec.RefineSynth.IdRawBits
