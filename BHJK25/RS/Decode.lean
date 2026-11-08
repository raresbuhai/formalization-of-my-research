module

public import BHJK25.RS.Defs
public import BHJK25.RS.Decode.Agree
public import BHJK25.RS.Decode.Field
public import BHJK25.RS.Decode.Frontier
public import BHJK25.RS.Decode.Interp
public import BHJK25.RS.Decode.PolyTimeInterp
public import BHJK25.RS.Decode.PolyTimeRR
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime

/-!
# The per-guess decoder

`BHJK25.RS.decodeL` decides, on coefficient lists, whether some polynomial with `m` coefficients
over `F_q` agrees with the given points `(x, y)` at `W + 1` distinct values `x`: Sudan's
interpolation (a nonzero `Q(X, Y) = Σ q_{ab} X^a Y^b` with `a + (m - 1) b ≤ W` vanishing at all
points, found by Gaussian elimination over `F_q` since it has more coefficients than there are
points), the roots `Y = p(X)` of `Q` of degree `< m` (Roth–Ruckenstein, with the roots of
univariate polynomials found by trying all `q` field elements), and a check of the agreement of
each root. The field is given by the lower coefficients `fl` of its modulus, and the list `elts`
of all its elements; `m` and `W` are given in unary. The list program is
`BHJK25.RS.DecodeAux.decode` (`BHJK25/RS/Decode/Algo.lean`).

**Correctness** (`BHJK25.RS.decodeL_spec`), for at most `n` points, `m ≥ 2` and
`W = ⌊√(2 n m)⌋ + 1`. If some `p` of degree `< m` agrees with the points at `W + 1` distinct `x`,
then the interpolant `Q` (`BHJK25.RS.DecodeAux.Sem.interp_spec`) has `Q(X, p(X)) = 0` (Sudan's
lemma, `BHJK25.RS.Sudan.eval_eq_zero`), so Roth–Ruckenstein lists `p`
(`BHJK25.RS.DecodeAux.Sem.rrRoots_complete`) and the decoder accepts. Conversely, every listed
candidate is a polynomial of degree `< m`, and the decoder counts its agreement exactly
(`BHJK25.RS.DecodeAux.Sem.agree_eq`).
-/

@[expose] public section

namespace BHJK25.RS

open Encoding

/-- The coefficient list of a field element: its `r` bits as `0`s and `1`s. -/
noncomputable def eltList {T n : ℕ} (x : Fld T n) : List ℕ :=
  List.ofFn fun i ↦ ((bitEquiv T n).symm x i).toNat

/-- The coefficient list of `x` has the value `x`. -/
theorem val_eltList {T n : ℕ} (x : Fld T n) :
    Cslib.GaloisRingArith.val 1 (irrPoly (rbits T n)) (eltList x) = x :=
  (bitEquiv T n).apply_symm_apply x

/-- **The per-guess decoder** on coefficient lists: the list program
`BHJK25.RS.DecodeAux.decode`. -/
def decodeL (fl : List ℕ) (elts : List (List ℕ)) (m W : ℕ) (pts : List (List ℕ × List ℕ)) :
    Bool :=
  DecodeAux.decode fl elts m W pts

open Classical in
/-- **The decoder is correct**: on the coefficient lists of at most `n` points, it decides
whether some polynomial of degree `< m` agrees with them at `W + 1` distinct values. -/
theorem decodeL_spec (T n : ℕ) (hm : 2 ≤ mdeg T n) (pts : List (Fld T n × Fld T n))
    (hpts : pts.length ≤ n) :
    decodeL (irrPoly (rbits T n)) ((List.range (2 ^ rbits T n)).map (bitsOf (rbits T n)))
        (mdeg T n) (wdeg T n) (pts.map fun xy ↦ (eltList xy.1, eltList xy.2)) =
      decide (∃ p : Polynomial (Fld T n), p.natDegree < mdeg T n ∧
        thr T n ≤ ((pts.filter fun xy ↦ p.eval xy.1 = xy.2).map Prod.fst).toFinset.card) := by
  set S := DecodeAux.fldSem T n
  have henc : ∀ x, S.ev (eltList x) = x := val_eltList
  have hagree := fun pre ↦ S.agree_eq eltList henc pts pre
  rw [decodeL, DecodeAux.decode, Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff]
  constructor
  · rintro ⟨pre, hpre, hW⟩
    have hlen := DecodeAux.Sem.length_of_mem_rrRoots _ _ _ _ pre hpre
    refine ⟨S.toP (mdeg T n) pre, S.natDegree_toP_lt (by omega) pre, ?_⟩
    rw [decide_eq_true_iff, hagree, hlen] at hW
    exact hW
  · rintro ⟨p, hp, hcard⟩
    have hW : 2 * n * mdeg T n < wdeg T n * wdeg T n := Nat.lt_succ_sqrt _
    obtain ⟨hQ, hdeg, hwt, hvan⟩ := S.interp_spec hm hW
      (L := (mdeg T n + 1) * (wdeg T n + 1)) (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
      (pts.map fun xy ↦ (eltList xy.1, eltList xy.2)) (by rw [List.length_map]; exact hpts)
    have hcard' : wdeg T n < ((pts.filter fun xy ↦ p.eval xy.1 = xy.2).map
        Prod.fst).toFinset.card := hcard
    have hroot := Sudan.eval_eq_zero hwt hp _ (fun x hx ↦ by
        obtain ⟨xy, hxy, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
        obtain ⟨hmem, heq⟩ := List.mem_filter.mp hxy
        rw [decide_eq_true_iff] at heq
        have h := hvan (eltList xy.1, eltList xy.2) (List.mem_map_of_mem hmem)
        rwa [henc, henc, ← heq] at h) hcard'
    obtain ⟨pre, hpre, hcoef⟩ := S.rrRoots_complete DecodeAux.exists_mem_elts
      (DecodeAux.nodup_map_val_elts T n) hQ hdeg hroot
    have hlen := DecodeAux.Sem.length_of_mem_rrRoots _ _ _ _ pre hpre
    have hpoly : S.toP pre.length pre = p := by
      rw [hlen]
      ext i
      rw [S.coeff_toP]
      split_ifs with hi
      · exact hcoef i hi
      · exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm
    refine ⟨pre, hpre, ?_⟩
    rw [decide_eq_true_iff, hagree, hpoly]
    exact hcard

open Turing.MultiTapeTM.ComputableInPolyTime in
/-- **The decoder runs in polynomial time**, with `m` and `W` in unary. -/
theorem decodeL_polytime : Turing.MultiTapeTM.ComputableInPolyTime
    (fun x : List ℕ × List (List ℕ) × ℕ × ℕ × List (List ℕ × List ℕ) ↦
      decodeL x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
    (encPair (encList encNat) (encPair (encList (encList encNat)) (encPair encUnary
      (encPair encUnary (encList (encPair (encList encNat) (encList encNat)))))))
    encBool := by
  have hfl := fst (encList encNat) (encPair (encList (encList encNat)) (encPair encUnary
    (encPair encUnary (encList (encPair (encList encNat) (encList encNat))))))
  have h2 := snd (encList encNat) (encPair (encList (encList encNat)) (encPair encUnary
    (encPair encUnary (encList (encPair (encList encNat) (encList encNat))))))
  have helts := (fst _ _).comp h2
  have h3 := (snd _ _).comp h2
  have hm := (fst _ _).comp h3
  have h4 := (snd _ _).comp h3
  have hW := (fst _ _).comp h4
  have hpts := (snd _ _).comp h4
  exact DecodeAux.PT.decode' hfl helts hm hW hpts (DecodeAux.PT.interp' hfl hm hW hpts)

end BHJK25.RS
