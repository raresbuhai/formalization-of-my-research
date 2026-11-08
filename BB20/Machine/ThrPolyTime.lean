module

public import BB20.Machine.ThrDef
public import Background.PolyTime.Rat
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Option
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Choose
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Factorial
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option

/-!
# The thresholds are computable in polynomial time

Certificates (`Turing.MultiTapeTM.ComputableInPolyTime`) for `BB20.Machine.thr6`
(`BB20.Machine.Thr.thr6_polytime`) and `BB20.Machine.thr11` (`BB20.Machine.Thr.thr11_polytime`).

The capped parameters `d`, `D`, `2^s`, `N` and `K` (`BB20/Machine/ThrDef.lean`) are computed in
unary: they are at most the cap `Λ`, which is computed in unary from the lengths of the numerator
of `α`, of the denominator of `γ` and of the list of samples. The exponents and the lengths of the
Taylor sums are polynomials in them, also in unary; so powers of rationals (by their numerators and
denominators, `BB20.Machine.Thr.rat_pow'`), factorials and binomial coefficients are
polynomial-time.
-/

@[expose] public section

namespace BB20.Machine.Thr

open Finset Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)

variable {α : Type} {input : α ↪ List Bool}

/-! ### Powers and sums of rationals -/

/-- A power of a computed rational to a computed unary exponent. -/
theorem rat_pow' {f : α → ℚ} {k : α → ℕ} (hf : ComputableInPolyTime f input encRat)
    (hk : ComputableInPolyTime k input encUnary) :
    ComputableInPolyTime (fun a => f a ^ k a) input encRat :=
  rat_of_numDen (g := fun a => ((f a).num ^ k a, (f a).den ^ k a))
    ((ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.intBin_pow'
      (rat_num' hf).tidy hk.tidy)).prod (binary_pow' (rat_den' hf) hk))
    fun a => by rw [Rat.num_pow, Rat.den_pow]

/-- A natural number in unary, as a rational. -/
theorem rat_ofUnary' {k : α → ℕ} (hk : ComputableInPolyTime k input encUnary) :
    ComputableInPolyTime (fun a => (k a : ℚ)) input encRat :=
  rat_natCast' (unary_to_binary.comp hk)

theorem sum_range_eq_list (f : ℕ → ℚ) (m : ℕ) :
    ∑ i ∈ range m, f i = ((List.range m).map f).sum := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]
    simp

/-! ### The fields of the input -/

/-- The encoding of the fields of an input. -/
abbrev encFields : ℕ × List (List Bool) × ℚ × ℚ × ℕ × ℕ × ℕ ↪ List Bool :=
  encPair encNat (encPair (encList encBits) (encPair encRat (encPair encRat
    (encPair encNat (encPair encNat encNat)))))

theorem fields_polytime : ComputableInPolyTime
    (fun x : Input ↦ (x.n, x.samples, x.coeff, x.gamma, x.d, x.D, x.s)) encInput encFields :=
  of_eq fun _ ↦ rfl

theorem samples_polytime :
    ComputableInPolyTime (fun x : Input ↦ x.samples) encInput (encList encBits) :=
  ((fst _ _).comp (snd _ _)).comp fields_polytime

theorem coeff_polytime : ComputableInPolyTime (fun x : Input ↦ x.coeff) encInput encRat :=
  ((fst _ _).comp ((snd _ _).comp (snd _ _))).comp fields_polytime

theorem gamma_polytime : ComputableInPolyTime (fun x : Input ↦ x.gamma) encInput encRat :=
  ((fst _ _).comp ((snd _ _).comp ((snd _ _).comp (snd _ _)))).comp fields_polytime

theorem d_polytime : ComputableInPolyTime (fun x : Input ↦ x.d) encInput encNat :=
  ((fst _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp (snd _ _))))).comp
    fields_polytime

theorem D_polytime : ComputableInPolyTime (fun x : Input ↦ x.D) encInput encNat :=
  ((fst _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp
    (snd _ _)))))).comp fields_polytime

theorem s_polytime : ComputableInPolyTime (fun x : Input ↦ x.s) encInput encNat :=
  ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp
    (snd _ _)))))).comp fields_polytime

/-! ### The capped parameters, in unary -/

theorem cap_polytime : ComputableInPolyTime cap encInput encUnary := by
  have hnum : ComputableInPolyTime (fun x : Input ↦ x.coeff.num.natAbs) encInput encNat :=
    (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.intBin_natAbs).comp
      (rat_num' coeff_polytime)
  exact unary_add' (unary_add' (unary_mul' (const 2) (binary_size.comp hnum))
    (binary_size.comp (rat_den' gamma_polytime))) ((length_list _).comp samples_polytime)

theorem dc_polytime : ComputableInPolyTime dc encInput encUnary :=
  binary_min_unary' cap_polytime d_polytime

theorem Dc_polytime : ComputableInPolyTime Dc encInput encUnary :=
  binary_min_unary' cap_polytime D_polytime

theorem pc_polytime : ComputableInPolyTime pc encInput encUnary :=
  binary_min_unary' cap_polytime (binary_two_pow.comp (binary_min_unary' cap_polytime s_polytime))

theorem floor_polytime :
    ComputableInPolyTime (fun x : Input ↦ ⌊2 * x.gamma⌋₊) encInput encNat := by
  have h := intBin_toNat.comp (rat_floor' (rat_mul' (const 2) gamma_polytime))
  refine h.of_enc_eq fun x ↦ ?_
  simp only [Function.comp_apply, Int.floor_toNat]

theorem Nc_polytime : ComputableInPolyTime Nc encInput encUnary :=
  unary_add' (binary_min_unary' cap_polytime floor_polytime) (const 1)

theorem Kc_polytime : ComputableInPolyTime Kc encInput encUnary :=
  unary_sub' (unary_add' dc_polytime Dc_polytime) (const 1)

/-! ### The factors -/

theorem facP_polytime : ComputableInPolyTime (fun t : ℕ × ℕ × ℕ ↦ facP t.1 t.2.1 t.2.2)
    (encPair encUnary (encPair encUnary encUnary)) encNat := by
  have hd : ComputableInPolyTime (fun t : ℕ × ℕ × ℕ ↦ t.1)
      (encPair encUnary (encPair encUnary encUnary)) encUnary := fst _ _
  have hD : ComputableInPolyTime (fun t : ℕ × ℕ × ℕ ↦ t.2.1)
      (encPair encUnary (encPair encUnary encUnary)) encUnary := (fst _ _).comp (snd _ _)
  have hp : ComputableInPolyTime (fun t : ℕ × ℕ × ℕ ↦ t.2.2)
      (encPair encUnary (encPair encUnary encUnary)) encUnary := (snd _ _).comp (snd _ _)
  have hdb := unary_to_binary.comp hd
  have hc := binary_choose' hD (unary_sub' hd (const 1))
  have hmax : ComputableInPolyTime (fun t : ℕ × ℕ × ℕ ↦ max 1 (t.2.1.choose (t.1 - 1)))
      (encPair encUnary (encPair encUnary encUnary)) encNat := by
    refine (binary_add.comp (hc.prod (binary_sub' (const 1) hc))).of_enc_eq fun t ↦ ?_
    simp only [Function.comp_apply]
    congr 1
    omega
  exact binary_mul' (binary_mul' (binary_mul' (binary_mul'
    (binary_pow' hdb (unary_mul' (const 4) hd))
    (binary_two_pow.comp (unary_add' hd (const 1)))) hmax)
    (binary_pow' (binary_mul' (const 4) hdb) hp))
    (binary_pow' hdb (unary_mul' hp (unary_add' hp (const 1))))

theorem facQ_polytime : ComputableInPolyTime (fun t : ℕ × ℕ ↦ facQ t.1 t.2)
    (encPair encUnary encUnary) encNat := by
  have hD : ComputableInPolyTime (fun t : ℕ × ℕ ↦ t.1) (encPair encUnary encUnary) encUnary :=
    fst _ _
  have hp : ComputableInPolyTime (fun t : ℕ × ℕ ↦ t.2) (encPair encUnary encUnary) encUnary :=
    snd _ _
  exact binary_mul' (binary_mul' (const 6)
    (binary_two_pow.comp (unary_add' hD (unary_mul' (const 2) hp))))
    (binary_pow' (unary_to_binary.comp hD) (unary_mul' hp (unary_add' hp (const 2))))

theorem base_polytime : ComputableInPolyTime base encInput encRat := by
  have hP := facP_polytime.comp' (dc_polytime.prod (Dc_polytime.prod pc_polytime))
  have h := rat_div' (rat_sq' coeff_polytime)
    (rat_mul' (rat_mul' (const (2 : ℚ)) gamma_polytime) (rat_natCast' hP))
  exact h

/-! ### The approximation of `e^{2γ}` -/

theorem expUp_polytime : ComputableInPolyTime (fun p : ℚ × ℕ ↦ expUp p.1 p.2)
    (encPair encRat encUnary) encRat := by
  have hy : ComputableInPolyTime (fun p : ℚ × ℕ ↦ p.1) (encPair encRat encUnary) encRat :=
    fst _ _
  have hm : ComputableInPolyTime (fun p : ℚ × ℕ ↦ p.2) (encPair encRat encUnary) encUnary :=
    snd _ _
  have hterm : ComputableInPolyTime (fun q : (ℚ × ℕ) × ℕ ↦ q.1.1 ^ q.2 / (q.2.factorial : ℚ))
      (encPair (encPair encRat encUnary) encUnary) encRat :=
    rat_div' (rat_pow' (hy.comp (fst _ _)) (snd _ _))
      (rat_natCast' (binary_factorial.comp (snd _ _)))
  have hsum : ComputableInPolyTime
      (fun p : ℚ × ℕ ↦ ((List.range p.2).map fun i ↦ p.1 ^ i / (i.factorial : ℚ)).sum)
      (encPair encRat encUnary) encRat :=
    rat_sum' (mapWithInput (f := fun (p : ℚ × ℕ) (i : ℕ) ↦ p.1 ^ i / (i.factorial : ℚ))
      (unary_range' hm) hterm)
  have hrem : ComputableInPolyTime
      (fun p : ℚ × ℕ ↦ p.1 ^ p.2 * ((p.2 : ℚ) + 1) / ((p.2.factorial : ℚ) * (p.2 : ℚ)))
      (encPair encRat encUnary) encRat :=
    rat_div' (rat_mul' (rat_pow' hy hm) (rat_add' (rat_ofUnary' hm) (const 1)))
      (rat_mul' (rat_natCast' (binary_factorial.comp hm)) (rat_ofUnary' hm))
  refine (rat_add' hsum hrem).of_enc_eq fun p ↦ ?_
  unfold expUp
  rw [sum_range_eq_list]

theorem expHi_polytime {γ : α → ℚ} {N m : α → ℕ} (hγ : ComputableInPolyTime γ input encRat)
    (hN : ComputableInPolyTime N input encUnary) (hm : ComputableInPolyTime m input encUnary) :
    ComputableInPolyTime (fun a ↦ expHi (γ a) (N a) (m a)) input encRat := by
  have hy := rat_div' (rat_mul' (const (2 : ℚ)) hγ) (rat_ofUnary' hN)
  have he := expUp_polytime.comp' (hy.prod hm)
  have h := rat_pow' he hN
  exact h

theorem val_polytime {R E : α → ℚ} {K : α → ℕ} (hR : ComputableInPolyTime R input encRat)
    (hE : ComputableInPolyTime E input encRat) (hK : ComputableInPolyTime K input encUnary) :
    ComputableInPolyTime (fun a ↦ val (R a) (E a) (K a)) input encRat := by
  have h := rat_div' hR (rat_mul' hE (rat_pow' (rat_add' (const (1 : ℚ)) hE) hK))
  exact h

theorem expHi6_polytime : ComputableInPolyTime expHi6 encInput encRat := by
  have h := expHi_polytime gamma_polytime Nc_polytime
    (unary_mul' (unary_mul' (const 20) Nc_polytime) (unary_add' Kc_polytime (const 1)))
  exact h

theorem expHi11_polytime : ComputableInPolyTime expHi11 encInput encRat := by
  have h := expHi_polytime gamma_polytime Nc_polytime
    (unary_mul' (unary_mul' (const 20) Nc_polytime)
      (unary_add' (unary_add' Kc_polytime Dc_polytime) (const 1)))
  exact h

/-! ### The thresholds -/

/-- **`thr6` is computable in polynomial time.** -/
theorem thr6_polytime : ComputableInPolyTime thr6 encInput (encOption encRat) := by
  have h := (optionSome encRat).comp' (val_polytime base_polytime expHi6_polytime Kc_polytime)
  exact h

/-- **`thr11` is computable in polynomial time.** -/
theorem thr11_polytime :
    ComputableInPolyTime thr11 encInput (encOption (encPair encRat encRat)) := by
  have hQ := rat_natCast' (facQ_polytime.comp' (Dc_polytime.prod pc_polytime))
  have h₂ := val_polytime (rat_div' base_polytime hQ) expHi11_polytime
    (unary_add' Kc_polytime Dc_polytime)
  have h₃ := val_polytime base_polytime expHi11_polytime Kc_polytime
  have h := (optionSome (encPair encRat encRat)).comp' (h₂.prod h₃)
  exact h

end BB20.Machine.Thr
