///|
/// ht_weights.mbt — 59. 霍奇-泰特權重 (Hodge–Tate weights)
///
/// For a p-adic representation V: HT weights of V = eigenvalue multiset of
/// the Sen operator = jumps of Fil on D_dR; of Sym^n V = all sums of n
/// weights (with multiplicity); of V(i) = shifted by −i (Tate twist).
/// Newton slopes of the φ-module realize the same multiset in the
/// crystalline case. Fontaine–Mazur: V de Rham ⟺ HT weights ∈ Z.
///
/// Theorem engine:
///   T59a (對稱冪): HT(Sym² V) = {0, 1, 2} for HT(V) = {0, 1} — verified via
///       Newton 多邊形 of the Sym²特徵多項式 x³ − (t²−p)x² + p(t²−p)x − p³
///   T59b (Tate 扭): φ 乘 p^{-1} ⇒ 全坡位移 −1（權重 −i 規約）
///   T59c (Sen 維數): Σ 重數 = dim V（Sym²: 3 = C(2+2−1, 2)）
///   T59d (整數譜 ⟺ 德拉姆): 普通/超奇 E 的 HT 權重全為整數或半整數坡
///       由 Newton 多邊形精確給出

///|
/// Generic Newton polygon root valuations for a monic polynomial given by
/// coefficients a[0..n] (ascending powers): points (i, v(a_i)); lower convex
/// hull; root valuations = negated hull slopes. Returns valuations sorted
/// ascending. Zero coefficients get valuation 1000000 (∞).
pub fn newton_slopes_poly(coeffs : Array[Int64], p : Int32) -> Array[Double] {
  let n = coeffs.length() - 1
  // points (i, v_i)
  let px : Array[Double] = []
  let py : Array[Double] = []
  let mut i = 0
  while i <= n {
    px.push(i.to_double())
    py.push(vp(coeffs[i], p).to_double())
    i = i + 1
  }
  // lower hull (monotone chain): keep points where successive slopes increase
  let hull : Array[Int32] = []
  let mut k = 0
  while k <= n {
    // skip infinite points unless endpoints
    while hull.length() >= 2 {
      let a = hull[hull.length() - 2]
      let b = hull[hull.length() - 1]
      // cross((b−a),(k−b)) ≤ 0 keeps lower hull: slope(a,b) ≤ slope(b,k)?
      let s1 = (py[b] - py[a]) * (px[k] - px[b])
      let s2 = (py[k] - py[b]) * (px[b] - px[a])
      if s1 > s2 {
        let _popped = hull.pop()
      } else {
        break
      }
    }
    hull.push(k)
    k = k + 1
  }
  // slopes between hull points: negated = root valuations
  let res : Array[Double] = []
  let mut h = 0
  while h + 1 < hull.length() {
    let a = hull[h]
    let b = hull[h + 1]
    let slope = (py[b] - py[a]) / (px[b] - px[a])
    let mult = b - a
    let mut m = 0
    while m < mult {
      res.push(-slope)
      m = m + 1
    }
    h = h + 1
  }
  // insertion sort ascending
  let mut i2 = 1
  while i2 < res.length() {
    let key = res[i2]
    let mut j = i2
    while j > 0 && res[j - 1] > key {
      res[j] = res[j - 1]
      j = j - 1
    }
    res[j] = key
    i2 = i2 + 1
  }
  res
}

///|
/// Sym² char poly coefficients of x² − t x + p: eigenvalues α², αβ, β²:
/// e₁ = t² − p, e₂ = p(t² − p), e₃ = p³.
/// Returns ascending-power coeffs [−e₃, e₂, −e₁, 1].
pub fn sym2_charpoly(t : Int64, p : Int64) -> Array[Int64] {
  let e1 = t * t - p
  let e2 = p * e1
  let e3 = p * p * p
  [-e3, e2, -e1, 1L]
}

///|
/// T59a: HT weights of Sym² of ordinary E (t = 1, p = 5): slopes = {0, 1, 2}.
pub fn sym2_ht_weights_ok(t : Int64, p : Int32) -> Bool {
  let cp = sym2_charpoly(t, p.to_int64())
  let slopes = newton_slopes_poly(cp, p)
  slopes.length() == 3 &&
  (slopes[0] - 0.0).abs() < 0.0001 &&
  (slopes[1] - 1.0).abs() < 0.0001 &&
  (slopes[2] - 2.0).abs() < 0.0001
}

///|
/// T59b: Tate twist shifts slopes by −1: char poly of p·φ^{-1}-twist:
/// slopes(V(1)) = slopes(V) − 1: verify: newton slopes of (p x − 1)-roots...
/// direct: for ordinary (0, 1): twist gives (−1, 0) = subtract 1 ✓:
/// verify via the polynomial x² − t·p^{-1}·x·p... simplest concrete: the
/// twist of φ = diag(1, p) by (1): φ' = p^{-1}φ = diag(p^{-1}, 1):
/// char poly x² − (p^{-1}+1)x + p^{-1}: scale to integral: p x² − (1+p)x + 1:
/// monic form x² − ((1+p)/p)x + 1/p — compute slopes via the reciprocal trick:
/// slopes of p·x² − (p+1)x + 1 (non-monic handled by using the polynomial
/// with a_n = p at x² — newton_slopes_poly assumes monic; use ascending
/// coeffs [1, −(p+1), p]: valuations v(1) = 0, v(p+1) = 0, v(p) = 1:
/// hull (0,0)→(1,0)→(2,1): slopes 0, 1/2: negated: (−0, −1/2)?? hmm roots:
/// p x² − (p+1)x + 1 = (px − 1)(x − 1): roots 1/p (v = −1) and 1 (v = 0):
/// valuations {−1, 0} ✓ = ordinary slopes − 1 ✓. Newton with ascending
/// coeffs [1, −(p+1), p]: points (0, 0), (1, 0), (2, 1): lower hull:
/// (0,0)→(1,0)→(2,1): slopes 0 and 1: negated: 0, −1: sorted (−1, 0) ✓✓.
pub fn tate_twist_slope_shift_ok(p : Int32) -> Bool {
  let cp = [1L, -(p + 1).to_int64(), p.to_int64()]
  let slopes = newton_slopes_poly(cp, p)
  slopes.length() == 2 &&
  (slopes[0] + 1.0).abs() < 0.0001 &&
  (slopes[1] - 0.0).abs() < 0.0001
}

///|
/// T59c: Sym² has 3 weights = C(3, 2)... dim Sym²(V) = n(n+1)/2 = 3 for n = 2;
/// multiset size check.
pub fn sym_multiplicity_ok() -> Bool {
  // Sym² of 2-dim: 3-dim; weights {0,1,2} all distinct: 3 slots
  let cp = sym2_charpoly(1L, 5L)
  let slopes = newton_slopes_poly(cp, 5)
  slopes.length() == 3
}

///|
/// T59d: Sen/HT weights are the Hodge jumps: for E: h = (0, 1) integers ⇒
/// de Rham; verify the total = t_H = Σ weights = 1 = t_N (slope sum).
pub fn sen_integer_spectrum_ok() -> Bool {
  let cp = [5L, -1L, 1L] // x² − x + 5 (ordinary)
  let slopes = newton_slopes_poly(cp, 5)
  let total = slopes[0] + slopes[1]
  let hodge_total = 0.0 + 1.0
  (total - hodge_total).abs() < 0.0001
}
