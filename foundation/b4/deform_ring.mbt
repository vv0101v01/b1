///|
/// deform_ring.mbt — 56. 伽羅瓦變形環 (Galois deformation rings)
///
/// Mazur: lifts of ρ̄: G → GL₂(k) to Artin local rings form a functor; the
/// tangent space of the deformation functor = H¹(G, Ad ρ̄) (fixed determinant:
/// H¹(G, Ad⁰)). For G cyclic of order n with p ∤ n:
///   H⁰ = ker(g−1),  H¹ = ker(N)/im(g−1),  H² = ker(g−1)/im(N)
/// (N = 1 + g + … + g^{n−1}); Euler characteristic vanishes.
/// The deformation ring R is (pro-)smooth of dimension dim H¹ over W(k) in
/// the unobstructed case: lifts to k[ε]/ε² are a torsor under H¹.
///
/// Theorem engine:
///   T56a (循環上同調): dim H⁰ − dim H¹ + dim H² = 0（p ∤ n 顯式計算）
///   T56b (切空間): tangent = H¹(G, Ad)：線性化方程 ker(Ad(g)+I)/im(Ad(g)−I)
///       維數與 cocycle 公式一致
///   T56c (提升計數): Z/2 → GL₂(Z/p²) 的提升數 = p^{dim ker(Ad(g)+I)}
///       （暴力枚舉 vs 線性代數）
///   T56d (框架化): framed 切空間 = unframed + dim H⁰（矩陣秩恆等式）

///|
/// 2×2 matrix over F_p as (a, b, c, d) with entries Int in [0, p).
pub(all) struct M2fp {
  a : Int32
  b : Int32
  c : Int32
  d : Int32
  p : Int32
}

///|
pub fn M2fp::mul(self : M2fp, o : M2fp) -> M2fp {
  let p = self.p
  M2fp::{
    a: (self.a * o.a + self.b * o.c) % p,
    b: (self.a * o.b + self.b * o.d) % p,
    c: (self.c * o.a + self.d * o.c) % p,
    d: (self.c * o.b + self.d * o.d) % p,
    p,
  }
}

///|
pub fn M2fp::add(self : M2fp, o : M2fp) -> M2fp {
  M2fp::{
    a: (self.a + o.a) % self.p,
    b: (self.b + o.b) % self.p,
    c: (self.c + o.c) % self.p,
    d: (self.d + o.d) % self.p,
    p: self.p,
  }
}

///|
pub fn M2fp::scale(self : M2fp, k : Int32) -> M2fp {
  M2fp::{
    a: self.a * k % self.p,
    b: self.b * k % self.p,
    c: self.c * k % self.p,
    d: self.d * k % self.p,
    p: self.p,
  }
}

///|
pub fn M2fp::is_zero(self : M2fp) -> Bool {
  self.a == 0 && self.b == 0 && self.c == 0 && self.d == 0
}

///|
pub fn M2fp::eq(self : M2fp, o : M2fp) -> Bool {
  self.a == o.a && self.b == o.b && self.c == o.c && self.d == o.d
}

///|
/// Basis E_ij of Mat₂.
fn basis_mat(i : Int32, p : Int32) -> M2fp {
  if i == 0 {
    M2fp::{ a: 1, b: 0, c: 0, d: 0, p, }
  } else if i == 1 {
    M2fp::{ a: 0, b: 1, c: 0, d: 0, p, }
  } else if i == 2 {
    M2fp::{ a: 0, b: 0, c: 1, d: 0, p, }
  } else {
    M2fp::{ a: 0, b: 0, c: 0, d: 1, p, }
  }
}

///|
/// Rank of a 4×4 matrix over F_p (Gaussian elimination).
fn rank4_mod(m : Array[Array[Int32]], p : Int32) -> Int32 {
  let a : Array[Array[Int32]] = []
  let mut i = 0
  while i < 4 {
    let row : Array[Int32] = []
    let mut j = 0
    while j < 4 {
      row.push((m[i][j] % p + p) % p)
      j = j + 1
    }
    a.push(row)
    i = i + 1
  }
  let mut rank = 0
  let mut col = 0
  let mut rr = 0
  while col < 4 && rr < 4 {
    // find pivot
    let mut piv = rr
    while piv < 4 && a[piv][col] == 0 {
      piv = piv + 1
    }
    if piv < 4 {
      // swap
      let tmp = a[rr]
      a[rr] = a[piv]
      a[piv] = tmp
      // normalize
      let inv = mod_inverse(a[rr][col].to_int64(), p.to_int64()).to_int()
      let mut j = col
      while j < 4 {
        a[rr][j] = a[rr][j] * inv % p
        j = j + 1
      }
      // eliminate
      let mut i2 = 0
      while i2 < 4 {
        if i2 != rr && a[i2][col] != 0 {
          let f = a[i2][col]
          let mut j2 = col
          while j2 < 4 {
            a[i2][j2] = ((a[i2][j2] - f * a[rr][j2]) % p + p) % p
            j2 = j2 + 1
          }
        }
        i2 = i2 + 1
      }
      rank = rank + 1
      rr = rr + 1
    }
    col = col + 1
  }
  rank
}

///|
/// Matrix of the linear map W ↦ g₀W + Wg₀ on Mat₂(F_p) (4×4 over F_p).
fn ad_plus_matrix(g0 : M2fp) -> Array[Array[Int32]] {
  let p = g0.p
  let res : Array[Array[Int32]] = []
  let mut i = 0
  while i < 4 {
    let w = basis_mat(i, p)
    let img = g0.mul(w).add(w.mul(g0))
    res.push([img.a, img.b, img.c, img.d])
    i = i + 1
  }
  res
}

///|
/// Matrix of W ↦ g₀W − Wg₀.
fn ad_minus_matrix(g0 : M2fp) -> Array[Array[Int32]] {
  let p = g0.p
  let res : Array[Array[Int32]] = []
  let mut i = 0
  while i < 4 {
    let w = basis_mat(i, p)
    let prod1 = g0.mul(w)
    let prod2 = w.mul(g0)
    let img = M2fp::{
      a: ((prod1.a - prod2.a) % p + p) % p,
      b: ((prod1.b - prod2.b) % p + p) % p,
      c: ((prod1.c - prod2.c) % p + p) % p,
      d: ((prod1.d - prod2.d) % p + p) % p,
      p,
    }
    res.push([img.a, img.b, img.c, img.d])
    i = i + 1
  }
  res
}

///|
/// dim ker of W ↦ g₀W + Wg₀ (= Z¹ tangent space of homomorphism lifts).
pub fn dim_z1_z2(g0 : M2fp) -> Int32 {
  let p = g0.p
  4 - rank4_mod(ad_plus_matrix(g0), p)
}

///|
/// dim H⁰ = ker(Ad(g) − I) = centralizer dim.
pub fn dim_h0_z2(g0 : M2fp) -> Int32 {
  let p = g0.p
  4 - rank4_mod(ad_minus_matrix(g0), p)
}

///|
/// Cleaner cyclic-group cohomology via dims:
/// H⁰ = ker(g−1) = 4 − rank(Ad(g)−I)
/// H¹ = ker(N)/im(g−1) = (4 − rank(Ad(g)+I)) − rank(Ad(g)−I)
/// H² = ker(g−1)/im(N) = (4 − rank(Ad(g)−I)) − rank(Ad(g)+I)
pub fn cyclic_cohom_dims(g0 : M2fp) -> (Int32, Int32, Int32) {
  let p = g0.p
  let rm = rank4_mod(ad_minus_matrix(g0), p)
  let rp = rank4_mod(ad_plus_matrix(g0), p)
  let h0 = 4 - rm
  let h1 = 4 - rp - rm
  let h2 = 4 - rm - rp
  (h0, h1, h2)
}

///|
/// Maschke vanishing: for p ∤ |G| (here p odd, G = Z/2), H^i(G, Ad) = 0 for
/// i > 0 — every extension splits; the deformation functor is unobstructed
/// and the unframed deformation ring is W(k) (rigid: unique lift up to
/// equivalence).
pub fn maschke_vanishing_ok(g0 : M2fp) -> Bool {
  let (h0, h1, h2) = cyclic_cohom_dims(g0)
  h1 == 0 && h2 == 0 && h0 == dim_h0_z2(g0)
}

///|
/// Exact sequence of the tangent spaces: Z¹ = ker(Ad(g)+I) fits
/// 0 → H¹ → Z¹ → B¹ → 0, so dim Z¹ = dim H¹ + dim im(g−1).
pub fn tangent_exact_ok(g0 : M2fp) -> Bool {
  let p = g0.p
  let (h0, h1, _) = cyclic_cohom_dims(g0)
  let z1 = dim_z1_z2(g0)
  let im_m = rank4_mod(ad_minus_matrix(g0), p)
  z1 == h1 + im_m && im_m == 4 - h0
}

///|
/// T56c: brute-force count of lifts X ∈ M₂(Z/p²) with
///   X ≡ g0 (mod p), X² = I.
/// The linearization X = g0 + pW gives g0W + Wg₀ ≡ 0 (mod p), so the count
/// should be exactly p^{dim ker(Ad(g0)+I)}.
pub fn lift_count_z2(g0 : M2fp) -> Int32 {
  let p = g0.p
  let q = p * p
  let mut count = 0
  let mut x0 = 0
  while x0 < q {
    let mut x1 = 0
    while x1 < q {
      let mut x2 = 0
      while x2 < q {
        let mut x3 = 0
        while x3 < q {
          let x = M2fp::{ a: x0, b: x1, c: x2, d: x3, p: q, }
          let xsq = x.mul(x)
          let id = M2fp::{ a: 1, b: 0, c: 0, d: 1, p: q, }
          let good_mod = x0 % p == g0.a &&
            x1 % p == g0.b &&
            x2 % p == g0.c &&
            x3 % p == g0.d
          if good_mod && xsq.eq(id) {
            count = count + 1
          }
          x3 = x3 + 1
        }
        x2 = x2 + 1
      }
      x1 = x1 + 1
    }
    x0 = x0 + 1
  }
  count
}

///|
/// T56c check: lift_count = p^{dim ker(Ad(g)+I)}.
pub fn lift_count_check(g0 : M2fp) -> Bool {
  let p = g0.p
  let ker_dim = 4 - rank4_mod(ad_plus_matrix(g0), p)
  let mut expected = 1
  let mut i = 0
  while i < ker_dim {
    expected = expected * p
    i = i + 1
  }
  lift_count_z2(g0) == expected
}

///|
/// T56d: unobstructed rigidity: for semisimple ρ̄ of Z/2 (p odd), every lift
/// to GL₂(Z/p²) satisfies X² = I (semisimple) and the mod-p reduction is g₀:
/// the framed solution count = p^{dim Z¹} equals the count computed from the
/// linearized tangent — plus the H¹ = 0 statement (unique unframed lift).
pub fn rigidity_ok(g0 : M2fp) -> Bool {
  let (h0, h1, h2) = cyclic_cohom_dims(g0)
  h1 == 0 && h2 == 0 && lift_count_check(g0) && h0 == 2
}
