module

public import ABBKS26.Assembly.ExecRefineBuildersAuxSpecPayload

/-! Bounded substitution for the centered polynomial family. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.SpecPoly

open Common MvPolynomial
open SoS.Solver (RawPoly encRawPoly)
open Turing.MultiTapeTM ComputableInPolyTime

/-- Cap each binary exponent before constructing its list of replacement factors. -/
def substitute (d n e L : ℕ) (p : RawPoly) (images : List RawPoly) : RawPoly :=
  p.flatMap fun t ↦ NestedProgram.scale t.2 (SoS.Poly.prodRaw n L
    ((List.range d).flatMap fun i ↦
      List.replicate (min e (t.1.getD i 0)) (images.getD i [])))

theorem substitute_polytime_of {α : Type} {enc : α ↪ List Bool}
    {d n e L : α → ℕ} {p : α → RawPoly} {images : α → List RawPoly}
    (hd : ComputableInPolyTime d enc encUnary)
    (hn : ComputableInPolyTime n enc encUnary)
    (he : ComputableInPolyTime e enc encUnary)
    (hL : ComputableInPolyTime L enc encUnary)
    (hp : ComputableInPolyTime p enc encRawPoly)
    (hi : ComputableInPolyTime images enc (encList encRawPoly)) :
    ComputableInPolyTime (fun a ↦ substitute (d a) (n a) (e a) (L a) (p a)
      (images a)) enc encRawPoly := by
  unfold substitute
  apply flatMapWithInput hp
  apply NestedProgram.scale_polytime
  · fun_prop
  · apply SoS.Poly.prodRaw' (hn.comp (fst _ _)) (hL.comp (fst _ _))
    apply flatMapWithInput ((range.comp hd).comp (fst _ _))
    apply replicate
    · apply binary_min_unary' ((he.comp (fst _ _)).comp (fst _ _))
      fun_prop
    · fun_prop

private theorem getD_le_sum (l : List ℕ) (i : ℕ) : l.getD i 0 ≤ l.sum := by
  by_cases hi : i < l.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact List.single_le_sum (fun _ _ ↦ Nat.zero_le _) _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Nat.zero_le _

private theorem prod_flatMap {α M : Type} [CommMonoid M]
    (l : List α) (f : α → List M) :
    (l.flatMap f).prod = (l.map fun a ↦ (f a).prod).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

private theorem prod_range {M : Type} [CommMonoid M] (d : ℕ) (f : ℕ → M) :
    ((List.range d).map f).prod = ∏ i : Fin d, f i.val := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih,
      Fin.prod_univ_castSucc]
    simp

/-- The cap is sufficient for every term of a polynomial of the advertised degree.
The premises concern raw terms, so repeated or cancelling terms cause no difficulty. -/
theorem substitute_agrees (d n e L q : ℕ) (p : RawPoly) (images : List RawPoly)
    (hq : 1 ≤ q) (hL : q ^ e ≤ L)
    (hp : ∀ t ∈ p, (SoS.Poly.expo d t.1).sum ≤ e)
    (hi : ∀ i, i < d → images.getD i [] ≠ [] ∧ (images.getD i []).length ≤ q) :
    (substitute d n e L p images).toPoly n =
      aeval (fun i : Fin d ↦ (images.getD i.val []).toPoly n) (p.toPoly d) := by
  have hflat {α : Type} (l : List α) (f : α → RawPoly) :
      RawPoly.toPoly n (l.flatMap f) = (l.map fun a ↦ (f a).toPoly n).sum := by
    induction l with
    | nil => simp [SoS.Solver.RawPoly.toPoly]
    | cons a l ih => simp only [List.flatMap_cons, SoS.Poly.toPoly_append,
        ih, List.map_cons, List.sum_cons]
  unfold substitute
  rw [hflat, SoS.Solver.RawPoly.toPoly, map_list_sum, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  have hcap (i : ℕ) (hid : i < d) : min e (t.1.getD i 0) = t.1.getD i 0 := by
    apply min_eq_right
    rw [← SoS.Poly.getD_expo t.1 hid]
    exact (getD_le_sum _ i).trans (hp t ht)
  have hfs : (List.range d).flatMap (fun i ↦
      List.replicate (min e (t.1.getD i 0)) (images.getD i [])) =
      (List.range d).flatMap (fun i ↦
        List.replicate (t.1.getD i 0) (images.getD i [])) := by
    apply congrArg List.flatten
    apply List.map_congr_left
    intro i hid
    rw [hcap i (List.mem_range.mp hid)]
  rw [hfs]
  let fs := (List.range d).flatMap fun i ↦
    List.replicate (t.1.getD i 0) (images.getD i [])
  have hlen : fs.length = (SoS.Poly.expo d t.1).sum := by
    simp only [fs, List.length_flatMap, List.length_replicate, SoS.Poly.expo]
  have hne : ∀ f ∈ fs, f ≠ [] := by
    intro f hf
    obtain ⟨i, hid, hf⟩ := List.mem_flatMap.mp hf
    rw [(List.mem_replicate.mp hf).2]
    exact (hi i (List.mem_range.mp hid)).1
  have hbound : (fs.map List.length).prod ≤ L := by
    calc
      _ ≤ q ^ (fs.map List.length).length := List.prod_le_pow_length _ _ (by
        intro s hs
        obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hs
        obtain ⟨i, hid, hf⟩ := List.mem_flatMap.mp hf
        rw [(List.mem_replicate.mp hf).2]
        exact (hi i (List.mem_range.mp hid)).2)
      _ ≤ q ^ e := by
        simp only [List.length_map, hlen]
        exact Nat.pow_le_pow_right hq (hp t ht)
      _ ≤ L := hL
  rw [NestedProgram.scale_toPoly, SoS.Poly.toPoly_prodRaw hne hbound]
  simp only [fs, List.map_flatMap, List.map_replicate, prod_flatMap,
    List.prod_replicate, Function.comp_apply, map_mul, map_prod, map_pow, aeval_C,
    aeval_X]
  rw [prod_range]
  rfl

theorem power_polytime_of {α : Type} {enc : α ↪ List Bool}
    {d : α → ℕ} {p : α → RawPoly} (r : ℕ)
    (hd : ComputableInPolyTime d enc encUnary)
    (hp : ComputableInPolyTime p enc encRawPoly) :
    ComputableInPolyTime (fun a ↦ MomentProgram.power (d a) (p a) r)
      enc encRawPoly := by
  induction r with
  | zero => exact const _
  | succ r ih =>
    exact (SoS.PolyTime.mulRaw' hd ih hp).of_enc_eq fun a ↦ by
      rw [MomentProgram.power, Function.iterate_succ_apply']
      rfl

theorem normSq_polytime_of {α : Type} {enc : α ↪ List Bool} {d : α → ℕ}
    (hd : ComputableInPolyTime d enc encUnary) :
    ComputableInPolyTime (fun a ↦ MomentProgram.normSq (d a)) enc encRawPoly := by
  unfold MomentProgram.normSq
  apply mapWithInput (range.comp hd)
  exact (NestedProgram.unitExp_polytime (hd.comp (fst _ _)) (snd _ _)
    (const 2)).prod (const 1)

end ABBKS26.Assembly.Exec.RefineSynth.SpecPoly
