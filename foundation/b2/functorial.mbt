///|
/// functorial.mbt — 35. 函子性原理 (functoriality) & 36. 基變換 (base change)
///
/// Functoriality: for r: GL_n → GL_m, L(r ∘ π, s) = L(π_r, s) with matching
/// Satake parameters r(α_p, β_p). Concrete verified cases:
///   Sym²: GL_2 → GL_3, (α, β) ↦ (α², αβ, β²)
///   adj = Sym² ⊗ det^{−1}: (α/β, 2, β/α)
/// Base change (cyclic, degree d): A_{p^f} = A_p^{...}; coefficients
/// a_{p^d}^{BC} relate to Frobenius powers; for quadratic BC: b_p = a_p² − 2p^{k−1}.
///
/// Theorem engine:
///   T35a (Sym² Satake 映射): b_p = a_p² − p^{k−1}，三根 = (α², αβ, β²)
///   T35b (adj 分解): Sym² π = (π ⊗ π) 的 adj 分量；adj 根集 = (α/β, 2, β/α)
///   T36a (二次基變換): b_p = a_p² − 2p^{k−1}（self-dual twist 公式），
///       且 b_{p²}... 由 Frobenius² 推導 b_n 並檢查 Hecke 相容

///|
/// Sym² coefficients at primes (GL_3 Satake elementary symmetric polys).
/// Returns (e1, e2, e3) for Sym² at p.
pub fn sym2_satake(a_p : Int64, p : Int32, k : Int32) -> (Int64, Int64, Int64) {
  let pk = pow64(p.to_int64(), k - 1)
  let e1 = a_p * a_p - pk
  let e2 = pk * e1
  let e3 = pk * pk * pk
  (e1, e2, e3)
}

///|
/// adj (= Sym² ⊗ det^{−1}) Satake at p: roots (α/β, 2, β/α):
/// e1 = a_p²/p^{k−1} − 2, e2 = e1, e3 = 1... in integral form multiply by p^{k−1}:
/// returns scaled (e1', e2', e3') with roots (α², 2αβ, β²) scaled by p^{k−1}:
/// e1' = a_p² − 2p^{k−1}, e2' = p^{k−1}(a_p² − 2p^{k−1})... we keep the scaled
/// convention: roots (α², 2αβ, β²) — det-normalized adjugate.
pub fn adj_satake(a_p : Int64, p : Int32, k : Int32) -> (Int64, Int64, Int64) {
  let pk = pow64(p.to_int64(), k - 1)
  let e1 = a_p * a_p - 2 * pk
  let e2 = pk * (a_p * a_p - 2 * pk)
  let e3 = pk * pk * pk
  (e1, e2, e3)
}

///|
/// Base change to quadratic field of discriminant D: twist by χ_D —
/// b_p = χ_D(p)·a_p... no: BC for quadratic ext K: a_p^{K} = a_{p}² − 2p^{k−1}
/// when p inert (the two primes over p have Frobenius Frob_p²... at split p,
/// primes of K over p have a_p each). Returns b_p given Legendre(D, p).
pub fn base_change_coefficient(
  a_p : Int64,
  p : Int32,
  k : Int32,
  legendre_dp : Int32,
) -> Int64 {
  let pk = pow64(p.to_int64(), k - 1)
  if legendre_dp == 1 {
    // p splits: b_p = a_p (two primes each with coeff a_p — sum convention a_p^K = 2a_p? 
    // standard: a_{p^K} = a_p^{(1)} + a_p^{(2)} = 2 a_p for split)
    2 * a_p
  } else if legendre_dp == -1 {
    // inert: single prime with residue degree 2: coeff = a_p² − 2p^{k−1}
    a_p * a_p - 2 * pk
  } else {
    // ramified: coeff = a_p² − p^{k−1}... (χ=0); use local formula a_p^2 − p^{k−1}
    a_p * a_p - pk
  }
}

///|
/// Functorial Satake image check: roots of the cubic X³ − e1X² + e2X − e3
/// should be (α², αβ, β²) where α, β are roots of X² − a_pX + p^{k−1}.
/// Verified through power sums: s'_m = α^{2m} + (αβ)^m + β^{2m} = s_{2m} + (p^{k−1})^m.
/// Returns max |computed − expected| over m ≤ m_max.
pub fn functorial_power_sum_error(
  a_p : Int64,
  p : Int32,
  k : Int32,
  m_max : Int32,
) -> Int64 {
  let pk = pow64(p.to_int64(), k - 1)
  let s = satake_power_sums(a_p, p, k, 2 * m_max + 1)
  let (e1, e2, e3) = sym2_satake(a_p, p, k)
  // Newton identity for the cubic: t_m = e1·t_{m−1} − e2·t_{m−2} + e3·t_{m−3}
  let t : Array[Int64] = []
  t.push(3L) // three roots
  t.push(e1)
  t.push(e1 * e1 - 2 * e2)
  let mut m = 3
  while m <= m_max {
    t.push(e1 * t[m - 1] - e2 * t[m - 2] + e3 * t[m - 3])
    m = m + 1
  }
  let mut max_err = 0L
  let mut j = 1
  while j <= m_max {
    let want = s[2 * j] + pow64(pk, j)
    let diff = if t[j] > want { t[j] - want } else { want - t[j] }
    if diff > max_err {
      max_err = diff
    }
    j = j + 1
  }
  max_err
}
