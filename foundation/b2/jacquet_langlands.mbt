///|
/// jacquet_langlands.mbt — 38. 雅克–朗蘭茲對應 (Jacquet–Langlands)
///
/// JL ↔ Deuring: the supersingular elliptic curves in char p correspond to
/// the arithmetic of the definite quaternion algebra B_{p,∞}; their
/// isomorphism classes (j-invariants in F_{p²}) satisfy:
///   T38a (Deuring 質量公式): Σ_{ss j} 1/|Aut(E_j)| = (p−1)/24
///   T38b (Deuring 計數公式): #ss j (F_{p²}) = ⌊p/12⌋ + ε,
///        ε = 0 (p ≡ 1 mod 12), 1 (p ≡ 5, 7), 2 (p ≡ 11)
/// The supersingularity test (p | trace of Frobenius) is Deuring's theorem
/// itself — verified here by brute-force point counting over F_{p²}.

///|
/// Embed F_p constant into GF(p, 2) element index.
pub fn embed_fp(c : Int32, fld : GF) -> Int32 {
  let m = (c % fld.p + fld.p) % fld.p
  fld.encode([m, 0])
}

///|
/// Curve y² = x³ + A·x + B over GF(p, 2) from j (GF element index):
/// j = 0 → (A, B) = (0, 1); j = 1728 → (1, 0); else K = j/(1728−j), (3K, 2K).
pub fn curve_from_j_gf2(j : Int32, fld : GF) -> (Int32, Int32) {
  let one = embed_fp(1, fld)
  let j1728 = embed_fp(1728, fld)
  if j == 0 {
    return (0, one) // y² = x³ + 1
  }
  if j == j1728 {
    return (one, 0) // y² = x³ + x
  }
  let den = fld.sub(j1728, j)
  let k = fld.mul(j, fld.inv(den))
  let three = embed_fp(3, fld)
  let two = embed_fp(2, fld)
  (fld.mul(three, k), fld.mul(two, k))
}

///|
/// Count points of y² = x³ + A x + B over GF(p, 2) (brute force).
pub fn count_points_gf2(a : Int32, b : Int32, fld : GF) -> Int32 {
  let q = fld.q()
  let mut count = 1 // infinity
  let mut x = 0
  while x < q {
    let x2 = fld.mul(x, x)
    let x3 = fld.mul(x2, x)
    let rhs = fld.add(fld.add(x3, fld.mul(a, x)), b)
    let mut y = 0
    while y < q {
      if fld.mul(y, y) == rhs {
        count = count + 1
      }
      y = y + 1
    }
    x = x + 1
  }
  count
}

///|
/// Nonsingular check: 4A³ + 27B² ≠ 0.
pub fn nonsingular_gf2(a : Int32, b : Int32, fld : GF) -> Bool {
  let four = embed_fp(4, fld)
  let t27 = embed_fp(27, fld)
  let a3 = fld.mul(fld.mul(a, a), a)
  let b2 = fld.mul(b, b)
  fld.add(fld.mul(four, a3), fld.mul(t27, b2)) != 0
}

///|
/// Enumerate ALL j ∈ GF(p, 2); return (ss_count, mass) where supersing means
/// trace over F_{p²} ≡ 0 (mod p) (Deuring), mass = Σ 1/|Aut|.
/// |Aut| = 6 for j = 0, 4 for j = 1728, else 2 (geometric).
pub fn ss_j_invariants_gf2(p : Int32) -> (Int32, Double, String) {
  let fld = GF::make(p, 2)
  let q = fld.q()
  let j1728 = embed_fp(1728, fld)
  let mut count = 0
  let mut mass = 0.0
  let mut detail = ""
  let mut j = 0
  while j < q {
    let (a, b) = curve_from_j_gf2(j, fld)
    if nonsingular_gf2(a, b, fld) {
      let npoints = count_points_gf2(a, b, fld)
      let tr = q + 1 - npoints
      if (tr % p + p) % p == 0 {
        count = count + 1
        let aut = if j == 0 { 6 } else if j == j1728 { 4 } else { 2 }
        mass = mass + 1.0 / aut.to_double()
        detail = detail +
          "  j = \{j}: #E(F_p²) = \{npoints}, tr = \{tr} ≡ 0 (mod p), |Aut| = \{aut}\n"
      }
    }
    j = j + 1
  }
  (count, mass, detail)
}

///|
/// Theoretical count: ⌊p/12⌋ + ε.
pub fn deuring_j_count(p : Int32) -> Int32 {
  let r = p % 12
  let eps = if r == 1 { 0 } else if r == 11 { 2 } else { 1 }
  p / 12 + eps
}
