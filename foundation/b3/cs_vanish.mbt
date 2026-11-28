///|
/// cs_vanish.mbt — 108. 卡拉亞尼-朔爾策消滅定理（玩具模型）
///
/// Caraiani–Scholze: for Shimura varieties, the cohomology H^i(Sh, π) of a
/// cuspidal automorphic π VANISHES outside the middle degree (non-tempered
/// constituents of H⁰ and H² are killed by the cuspidal projector).
/// Toy model verified here: the HECKE RAMANUJAN SIEVE separates cuspidal
/// eigenvalues (Ramanujan-bound) from non-cuspidal ones (Eisenstein/Tate):
///   cuspidal:   |a_p| ≤ 2p^{(k−1)/2}
///   Eisenstein: a_p = 1 + p^{k−1}  (way outside the bound for k > 2)
///   Tate H²:    a_p = p             (outside the weight-2 bound 2√p for p ≥ 5)
/// The "vanishing" = the projector onto the Ramanujan spectrum annihilates
/// the non-middle-degree Hecke modules.
///
/// Theorem engine:
///   T108a (譜分離): |E₁₂(2)| = 2049 vs bound 2·2^{11/2} ≈ 92 vs τ(2) = −24
///   T108b (H⁰/H² 消滅): Tate 譜 p > 2√p（p ≥ 5）故權 2 界外 ⇒ 中間次數外消滅
///   T108c (篩法判定): heuristic Ramanujan filter 正確分類三類特徵值
///       （Eisenstein/cuspidal/Tate 於 p = 2, 3, 5, 7, 11, 13）

///|
/// sqrt via Newton iterations.
pub fn sqrt_d(x : Double) -> Double {
  if x <= 0.0 {
    return 0.0
  }
  let mut r = x
  let mut i = 0
  while i < 40 {
    r = (r + x / r) / 2.0
    i = i + 1
  }
  r
}

///|
/// Integer power of a Double.
fn pow_int_d(base : Double, n : Int32) -> Double {
  let mut acc = 1.0
  let mut i = 0
  while i < n {
    acc = acc * base
    i = i + 1
  }
  acc
}

///|
/// Ramanujan bound for weight k at p: 2·p^{(k−1)/2}.
pub fn ramanujan_bound(p : Int32, k : Int32) -> Double {
  let pd = p.to_double()
  let e = k - 1
  if e % 2 == 0 {
    2.0 * pow_int_d(pd, e / 2)
  } else {
    2.0 * pow_int_d(pd, e / 2) * sqrt_d(pd)
  }
}

///|
/// Eisenstein eigenvalue of T_p on weight k (E_k = 1 + c·Σσ_{k−1}): a_p = 1 + p^{k−1}.
pub fn eisenstein_eigenvalue(p : Int32, k : Int32) -> Int64 {
  pow64(p.to_int64(), k - 1) + 1L
}

///|
/// Cuspidal eigenvalue τ(p) for weight 12 via delta_series.
pub fn cusp_eigenvalue_12(p : Int32) -> Int64 {
  let d = delta_series(16)
  d.0[p]
}

///|
/// The Ramanujan sieve: classification of a Hecke eigenvalue.
pub fn ramanujan_classify(a_p : Int64, p : Int32, k : Int32) -> String {
  let bound = ramanujan_bound(p, k)
  let v = a_p.to_double()
  let mag = if v < 0.0 { -v } else { v }
  if mag <= bound {
    "cuspidal"
  } else {
    "non-cuspidal"
  }
}

///|
/// Weight-12 spectrum table check: for p in [2, 3, 5, 7, 11, 13]:
/// Eisenstein outside, cuspidal inside.
pub fn sieve_weight12_ok() -> Bool {
  let mut ok = true
  for p in [2, 3, 5, 7, 11, 13] {
    let e = eisenstein_eigenvalue(p, 12)
    let c = cusp_eigenvalue_12(p)
    if ramanujan_classify(e, p, 12) != "non-cuspidal" {
      ok = false
    }
    if ramanujan_classify(c, p, 12) != "cuspidal" {
      ok = false
    }
  }
  ok
}

///|
/// H⁰/H² vanishing sieve: weight-0 (H⁰) and weight-2 Tate (H²) eigenvalues
/// fall outside the cuspidal bound of the middle weight → the projector
/// annihilates them. H⁰: a_p = 1 + p^{0}·... use Eisenstein weight 0 shape:
/// trivial rep: a_p = 1 + 1 = 2?? For H⁰(Q) = trivial: T_p = 1... but the
/// Eisenstein series E_2-ish has a_p = 1 + p. Use the weight-2 window:
/// trivial: a_p = 1 + p; Tate twist: a_p = p; both outside |a_p| ≤ 2√p for
/// p ≥ 5 ✓; cuspidal weight-2: |a_p| ≤ 2√p ✓ inside.
pub fn middle_vanish_ok() -> Bool {
  let mut ok = true
  for p in [5, 7, 11, 13, 17, 19] {
    let bound = ramanujan_bound(p, 2)
    // trivial + Tate twist eigenvalues outside
    let e_triv = (1 + p).to_double()
    let e_tate = p.to_double()
    if e_triv <= bound {
      ok = false
    }
    if e_tate <= bound {
      ok = false
    }
    // X₀(11) cuspidal inside
    let nf = newform_level11(20)
    let a = nf[p].to_double()
    let mag = if a < 0.0 { -a } else { a }
    if mag > bound {
      ok = false
    }
  }
  ok
}
