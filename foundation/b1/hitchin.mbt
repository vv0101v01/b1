///|
/// hitchin.mbt — 希欽纖維化 (Hitchin fibration)：
///   Hitchin 基底維度、譜曲線（超橢圓曲線模型）、Zeta 函數、Weil 數、
///   纖維 = 譜曲線的 Jacobian（Abel 簇）
///
/// Theorem engine:
///   T25 (Lagrangian 纖維): dim Hitchin base = n²(g−1)+1 = ½ dim(Higgs bundle 空間)
///   T26 (譜曲線屬數): g_spectral = n²(g−1)+1 = dim Jac = dim base
///   T27 (Weil 猜想/RH for curves): 譜曲線 Frobenius 特徵根 |α_i| = √q
///   T28 (Jac 點數): #Jac(C)(F_q) = L_C(1) = P(1)（希欽纖維的 F_q-點數）

///|
/// h⁰(C, K^i) on a curve of genus g ≥ 2 (Riemann–Roch):
/// i = 1: g; i ≥ 2: i(2g−2) − g + 1.
pub fn h0_k_power(i : Int32, g : Int32) -> Int32 {
  if i == 1 {
    g
  } else {
    i * (2 * g - 2) - g + 1
  }
}

///|
/// Hitchin base dimension for GL_n on a genus-g curve: Σ_{i=1}^{n} h⁰(K^i).
pub fn hitchin_base_dim(n : Int32, g : Int32) -> Int32 {
  let mut s = 0
  let mut i = 1
  while i <= n {
    s = s + h0_k_power(i, g)
    i = i + 1
  }
  s
}

///|
/// Closed form: n²(g−1) + 1.
pub fn hitchin_base_dim_closed(n : Int32, g : Int32) -> Int32 {
  n * n * (g - 1) + 1
}

///|
/// dim Bun_{GL_n} = n²(g−1) + 1 (complex dimension of the moduli stack);
/// the Higgs bundle total space has dimension twice that.
pub fn higgs_total_dim(n : Int32, g : Int32) -> Int32 {
  2 * (n * n * (g - 1) + 1)
}

///|
/// Genus of the spectral curve for GL_n: g_s = n²(g−1)+1.
pub fn spectral_genus(n : Int32, g : Int32) -> Int32 {
  n * n * (g - 1) + 1
}

///|
/// Hyperelliptic curve y² = f(x) over F_q, deg f = 2g+1 (odd): genus g.
pub(all) struct HypCurve(Array[Int32])

///|
/// Degree of f.
pub fn HypCurve::degree(self : HypCurve) -> Int32 {
  // last nonzero coefficient
  let mut d = -1
  let mut i = 0
  while i < self.0.length() {
    if self.0[i] != 0 {
      d = i
    }
    i = i + 1
  }
  d
}

///|
/// Genus = (deg f − 1) / 2 for odd deg f.
pub fn HypCurve::genus(self : HypCurve) -> Int32 {
  (self.degree() - 1) / 2
}

///|
/// Evaluate f at x in GF(p, k) (Horner), coefficients in the prime field.
pub fn HypCurve::eval(self : HypCurve, x : Int32, fld : GF) -> Int32 {
  let mut acc = 0
  let mut i = self.0.length() - 1
  while i >= 0 {
    let c = (self.0[i] % fld.p + fld.p) % fld.p
    acc = fld.add(fld.mul(acc, x), c)
    i = i - 1
  }
  acc
}

///|
/// Count points on y² = f(x) over GF(p, k): Σ_x (1 + χ(f(x))) + 1 (infinity).
pub fn HypCurve::point_count(self : HypCurve, p : Int32, k : Int32) -> Int32 {
  let fld = GF::make(p, k)
  let q = fld.q()
  let mut count = 1 // point at infinity (deg f odd)
  let mut x = 0
  while x < q {
    let v = self.eval(x, fld)
    count = count + 1 + fld.chi(v)
    x = x + 1
  }
  count
}

///|
/// Newton identities: from power sums p_m = Σ α_i^m (m = 1..2g) compute the
/// elementary symmetric functions e_m of the α_i (as Doubles, rounding check).
/// P(t) = ∏(1 − α_i t) = Σ (−1)^m e_m t^m.
pub fn newton_elliptic(powers : Array[Double]) -> Array[Double] {
  let m2 = powers.length() // = 2g
  let e : Array[Double] = []
  e.push(1.0) // e_0
  let mut m = 1
  while m <= m2 {
    let mut acc = 0.0
    let mut i = 1
    while i <= m {
      let sign = if (i - 1) % 2 == 0 { 1.0 } else { -1.0 }
      acc = acc + sign * e[m - i] * powers[i - 1]
      i = i + 1
    }
    e.push(acc / m.to_double())
    m = m + 1
  }
  e
}

///|
/// L-polynomial of a hyperelliptic curve over F_q, computed from point counts
/// over F_{q^n}, n = 1..2g. Returns coefficients e_0..e_{2g} (e_0 = 1).
pub fn hyp_l_polynomial(
  curve : HypCurve,
  p : Int32,
  g : Int32,
) -> Array[Double] {
  let powers : Array[Double] = []
  let mut n = 1
  while n <= 2 * g {
    let cnt = curve.point_count(p, n)
    let qn = q_pow(p, n).to_double()
    // #C(F_{q^n}) = q^n + 1 − Σ α_i^n  ⇒  Σ α_i^n = q^n + 1 − #C
    powers.push(qn + 1.0 - cnt.to_double())
    n = n + 1
  }
  newton_elliptic(powers)
}

///|
/// Riemann hypothesis check for the curve: all roots of P(t) have |α| = √q,
/// equivalently the roots of the reciprocal polynomial Q(u) = u^{2g}P(1/u)
/// lie on the circle |u| = √q. We verify the algebraic shadow: |e_{2g}| = q^g
/// and (for g = 2) the functional equation e_i = q^{g−i}·e_{2g−i} exactly.
pub fn hyp_functional_equation_ok(
  e : Array[Double],
  q : Int32,
  g : Int32,
) -> Bool {
  let mut ok = true
  let mut i = 0
  while i <= g {
    // functional equation: e_{2g−i} = q^{g−i} · e_i
    let lhs = e[2 * g - i]
    let rhs = @math.pow(q.to_double(), (g - i).to_double()) * e[i]
    let diff = if lhs > rhs { lhs - rhs } else { rhs - lhs }
    if diff > 0.000001 {
      ok = false
    }
    i = i + 1
  }
  ok
}

///|
/// Point count of the Jacobian (= Pic^0) of the curve over F_q: P(1) = e_0 − e_1
/// + e_2 − ... (alternating sum). For an elliptic curve this equals #C(F_q).
pub fn hyp_jacobian_order(e : Array[Double]) -> Int64 {
  let mut acc = 0.0
  let mut i = 0
  while i < e.length() {
    let sign = if i % 2 == 0 { 1.0 } else { -1.0 }
    acc = acc + sign * e[i]
    i = i + 1
  }
  (acc + 0.5).to_int64()
}

///|
/// Hasse–Weil bound: |#C(F_q) − (q+1)| ≤ 2g√q.
pub fn hyp_hasse_ok(count : Int32, q : Int32, g : Int32) -> Bool {
  let diff = (count - (q + 1)).to_double()
  let ad = if diff < 0.0 { -diff } else { diff }
  ad <= 2.0 * g.to_double() * @math.pow(q.to_double(), 0.5) + 0.000001
}
