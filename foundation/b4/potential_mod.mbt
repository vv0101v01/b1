///|
/// potential_mod.mbt — 54. 潛在模性 (potential modularity)
///
/// Taylor: every odd ρ̄: G_Q → GL₂(F_p) becomes modular over some totally
/// real extension. Concrete mechanism: QUADRATIC BASE CHANGE.
/// For K = Q(√d):
///   L(E/K, s) = L(E, s)·L(E^{(d)}, s)
/// with E^{(d)}: y² = x³ + d²A x + d³B the quadratic twist; coefficient-level:
///   a_p(E^{(d)}) = χ_d(p)·a_p(E)  (p ∤ N·d),
/// and the norm-p coefficient of L(E/K) = a_p(E) + a_p(E^{(d)}) — which
/// vanishes for inert p (= 0 primes of norm p) automatically.
///
/// Theorem engine:
///   T54a (扭曲係數): a_p(E^d) = (d/p)·a_p(E)（雙曲線點數實測 p ≤ 31）
///   T54b (基變換分解): 係數恆等式 L(E/K) = L(E)·L(E^d)（分裂/惰性分情況）
///   T54c (潛在模性顯例): K = Q(√5) 上的 E 由兩個 Q-側模形式資料決定

///|
/// Short Weierstrass y² = x³ + A x + B over GF(p, k): point count via
/// # = 1 + Σ_x (1 + χ(x³ + A x + B)) — O(q).
pub fn count_short_curve(a : Int64, b : Int64, p : Int32, k : Int32) -> Int32 {
  let fld = GF::make(p, k)
  let q = fld.q()
  if p == 2 {
    // y ↦ y² bijective in char 2: every x gives exactly one y
    return 1 + q
  }
  let mut count = 1 // infinity
  let mut x = 0
  while x < q {
    let xx = fld.mul(x, x)
    let xxx = fld.mul(xx, x)
    let fx = fld.add(
      fld.add(
        xxx,
        fld.mul(((a % p.to_int64() + p.to_int64()) % p.to_int64()).to_int(), x),
      ),
      ((b % p.to_int64() + p.to_int64()) % p.to_int64()).to_int(),
    )
    count = count + 1 + fld.chi(fx)
    x = x + 1
  }
  count
}

///|
/// a_p of y² = x³ + A x + B: p + 1 − #E(F_p).
pub fn a_p_short(a : Int64, b : Int64, p : Int32) -> Int64 {
  (p + 1 - count_short_curve(a, b, p, 1)).to_int64()
}

///|
/// Quadratic twist by d: y² = x³ + d²A x + d³B.
pub fn twist_by(a : Int64, b : Int64, d : Int64) -> (Int64, Int64) {
  (d * d * a, d * d * d * b)
}

///|
/// T54a check for the model curve E: y² = x³ − x (A = −1, B = 0) and d = 5:
/// a_p(E^5) = (5/p)·a_p(E) for p ≤ p_max, p ∤ 10.
pub fn twist_coeff_check(
  a : Int64,
  b : Int64,
  d : Int32,
  p_max : Int32,
) -> Int32 {
  let (ta, tb) = twist_by(a, b, d.to_int64())
  let mut ok = 0
  for p in primes_upto(p_max) {
    if p != 2 && p != 5 && p != 3 {
      let lhs = a_p_short(ta, tb, p)
      let chi = legendre(d.to_int64(), p.to_int64())
      let rhs = chi.to_int64() * a_p_short(a, b, p)
      if lhs == rhs {
        ok = ok + 1
      }
    }
  }
  ok
}

///|
/// T54b: base change coefficient identity. For K = Q(√d), the norm-p
/// coefficient of L(E/K) must equal a_p(E) + a_p(E^d):
///   split (χ=1): both primes of norm p, sum = 2a_p = a_p + a_p ✓;
///   inert (χ=−1): no norm-p primes, sum must be 0 = a_p − a_p ✓;
///   ramified (χ=0): skip.
pub fn base_change_identity_check(
  a : Int64,
  b : Int64,
  d : Int32,
  p_max : Int32,
) -> Bool {
  let (ta, tb) = twist_by(a, b, d.to_int64())
  let mut ok = true
  for p in primes_upto(p_max) {
    if p != 2 && p != 5 {
      let chi = legendre(d.to_int64(), p.to_int64()).to_int()
      let aq = a_p_short(a, b, p)
      let ad = a_p_short(ta, tb, p)
      let sum = aq + ad
      if chi == 1 {
        if sum != aq * 2L {
          ok = false
        }
      } else if chi == -1 {
        if sum != 0L {
          ok = false
        }
      }
    }
  }
  ok
}

///|
/// T54c: inert-prime quadratic consistency: for p inert in K,
/// a_{p²}(E) = a_p² − 2p = tr(Frob_p²) and the norm-p² prime contributes
/// this value: verify a_{p²} = a_p² − 2p via point counts over F_{p²}.
pub fn inert_prime_check(
  a : Int64,
  b : Int64,
  d : Int32,
  p_max : Int32,
) -> Bool {
  let mut ok = true
  for p in primes_upto(p_max) {
    if p != 2 && p != 5 {
      let chi = legendre(d.to_int64(), p.to_int64())
      if chi == -1 {
        // a_{p²} from F_{p²} counts
        let c2 = count_short_curve(a, b, p, 2)
        let q2 = p * p
        let a_p2 = (q2 + 1 - c2).to_int64()
        let a1 = a_p_short(a, b, p)
        if a_p2 != a1 * a1 - 2L * p.to_int64() {
          ok = false
        }
      }
    }
  }
  ok
}
