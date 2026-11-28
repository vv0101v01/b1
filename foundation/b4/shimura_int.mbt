///|
/// shimura_int.mbt — 60. 志村簇與施圖卡整數模型 (Shimura varieties &
/// integral canonical models)
///
/// The modular curve X₀(N) has an integral model over Z[1/N] representing
/// (E, C) with E an elliptic curve and C ⊂ E[N] cyclic. At p | N the special
/// fiber is governed by the NÉRON model: for multiplicative reduction the
/// minimal regular model is an N-gon of P¹'s with N = v_p(Δ) (Tate curve);
/// component group Φ ≅ Z/N; arithmetic genus p_a = Σ g_i + b₁(Γ) = 1.
/// Formal smoothness of the Weierstrass moduli: smooth models mod p lift
/// uniquely-ish to mod p² (#lifts = p² per mod-p point).
///
/// Theorem engine:
///   T60a (形式光滑性): 光滑 (A,B) mod p 的提升數 = p²（枚舉 p = 5, 7）
///   T60b (判別式/N-gon): Δ(X₀(11)) = −11⁵：v₁₁(Δ) = 5 ⇒ 特殊纖維 5-gon、
///       Φ = Z/5、p_a = 1（對偶圖圈空間 b₁ = 1）
///   T60c (j-線整模型): 每個 j ∈ F_p 有光滑模型（model_from_j 往返驗證）
///   T60d (志村模數詮釋): p ≥ 5 時 j-映射滿射且判別式非零 ⇒ A₁ 整模型光滑

///|
/// Weierstrass discriminant: b₂ = a1²+4a2, b₄ = 2a4+a1a3, b₆ = a3²+4a6,
/// b₈ = a1²a6+4a2a6−a1a3a4+a2a3²−a4²; Δ = −b₂²b₈ − 8b₄³ − 27b₆² + 9b₂b₄b₆.
pub fn weierstrass_disc(
  a1 : Int64,
  a2 : Int64,
  a3 : Int64,
  a4 : Int64,
  a6 : Int64,
) -> Int64 {
  let b2 = a1 * a1 + 4L * a2
  let b4 = 2L * a4 + a1 * a3
  let b6 = a3 * a3 + 4L * a6
  let b8 = a1 * a1 * a6 + 4L * a2 * a6 - a1 * a3 * a4 + a2 * a3 * a3 - a4 * a4
  -(b2 * b2 * b8) - 8L * b4 * b4 * b4 - 27L * b6 * b6 + 9L * b2 * b4 * b6
}

///|
/// T60b: discriminant of X₀(11) = WCurve(0, −1, 1, −10, −20): Δ = −11⁵.
pub fn disc_x011_ok() -> Bool {
  weierstrass_disc(0L, -1L, 1L, -10L, -20L) == -161051L
}

///|
/// v_p(Δ) = number of components of the Néron N-gon.
pub fn n_gon_components(delta : Int64, p : Int32) -> Int32 {
  vp(delta, p)
}

///|
/// Arithmetic genus of the N-gon: Σ g_i + b₁(Γ) = 0 + 1 = 1 (Γ = N-cycle).
pub fn n_gon_genus(n : Int32) -> Int32 {
  let _ = n
  // dual graph = cycle C_N: b₁ = E − V + 1 = N − N + 1 = 1
  graph_cycle_dim_edges(n, n, 1) + 0
}

///|
/// Graph cycle dim with explicit edge count (for the N-gon: N edges, N
/// vertices, 1 component).
fn graph_cycle_dim_edges(
  n_edges : Int32,
  n_verts : Int32,
  n_comp : Int32,
) -> Int32 {
  n_edges - n_verts + n_comp
}

///|
/// T60a: formal smoothness: # smooth Weierstrass (A, B) over Z/p² =
/// p² · # over F_p (each smooth mod-p point has exactly p² lifts).
pub fn formal_smoothness_check(p : Int32) -> Bool {
  let q = p * p
  let mut count_mod_p = 0
  let mut a = 0
  while a < p {
    let mut b = 0
    while b < p {
      let d = ((4 * a * a * a + 27 * b * b) % p + p) % p
      if d != 0 {
        count_mod_p = count_mod_p + 1
      }
      b = b + 1
    }
    a = a + 1
  }
  let mut count_mod_p2 = 0
  let mut a2 = 0
  while a2 < q {
    let mut b2 = 0
    while b2 < q {
      let d2 = (
          (
            4L * a2.to_int64() * a2.to_int64() * a2.to_int64() +
            27L * b2.to_int64() * b2.to_int64()
          ) %
          q.to_int64() +
          q.to_int64()
        ) %
        q.to_int64()
      // smooth mod p²: disc invertible mod p²: p ∤ disc
      if d2 % p.to_int64() != 0L {
        count_mod_p2 = count_mod_p2 + 1
      }
      b2 = b2 + 1
    }
    a2 = a2 + 1
  }
  count_mod_p2 == count_mod_p * p * p
}

///|
/// T60c: every j ∈ F_p ∪ {∞} has a smooth model: model_from_j roundtrip with
/// nonzero discriminant.
pub fn j_model_surjective_check(p : Int32) -> Bool {
  let mut ok = true
  let mut j = 0
  while j < p {
    let (a, b) = model_from_j(j, p)
    let pm = p.to_int64()
    let d = ((4L * a * a * a + 27L * b * b) % pm + pm) % pm
    if d == 0L {
      ok = false
    }
    // roundtrip: j(a, b) = j (or 1728-case)
    let j2 = j_invariant(a, b, p)
    let jn = ((j.to_int64() % pm + pm) % pm).to_int()
    if j2 != jn {
      ok = false
    }
    j = j + 1
  }
  ok
}

///|
/// T60d: the component group of the Néron model at p = 11 for X₀(11):
/// Φ = Z/N with N = v₁₁(Δ) = 5; and E(F_p)-plane count consistency:
/// p + 1 − a_p = 11 with a_p = 1 (Steinberg) — cross-check with T109.
pub fn component_group_x011() -> (Int32, Int32) {
  let delta = weierstrass_disc(0L, -1L, 1L, -10L, -20L)
  let n = n_gon_components(delta, 11)
  (n, n_gon_genus(n))
}
