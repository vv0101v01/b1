///|
/// autalg.mbt — 102. 代數自守表示 (algebraic automorphic representations)
///
/// A classical modular form of weight k generates an algebraic automorphic
/// representation of GL₂(A_Q); its Hecke eigenvalues are ALGEBRAIC INTEGERS.
/// Concrete model: S_k(SL₂(Z)) = Δ · M_{k−12}(E₄, E₆) with integral basis
/// Δ·E₄^a E₆^b (4a + 6b = k − 12); Hecke acts by integer matrices.
///
/// Theorem engine:
///   T102a (Hecke 代數交換性): [T_m, T_n] = 0（矩陣恆等式，S₂₈ 上驗證）
///   T102b (特徵形式): T_p Δ = τ(p)·Δ；T_2 特徵多項式係數 ∈ Z（代數整性）
///   T102c (權空間維數): dim S₁₂ = 1、dim S₂₈ = 2 = dim M₁₆（單項式計數）
///   T102d (Ramanujan 界): S₂₈ 的 T₂ 特徵值 |λ| ≤ 2·p^{(k−1)/2}

///|
/// Monomial list (a, b) with 4a + 6b = m.
pub fn monomials_e4_e6(m : Int32) -> Array[(Int32, Int32)] {
  let res : Array[(Int32, Int32)] = []
  let mut b = 0
  while 6 * b <= m {
    let rem = m - 6 * b
    if rem % 4 == 0 {
      res.push((rem / 4, b))
    }
    b = b + 1
  }
  res
}

///|
/// E₄^a · E₆^b as coefficient array (truncated).
fn e4a_e6b(a : Int32, b : Int32, n0 : Int32) -> Array[Int64] {
  let e4 = e4_series(n0)
  let e6 = e6_series(n0)
  let mut acc : Array[Int64] = []
  let mut i = 0
  while i <= n0 {
    acc.push(if i == 0 { 1L } else { 0L })
    i = i + 1
  }
  let mut u = 0
  while u < a {
    acc = qs_mul(acc, e4.0, n0)
    u = u + 1
  }
  let mut v = 0
  while v < b {
    acc = qs_mul(acc, e6.0, n0)
    v = v + 1
  }
  acc
}

///|
/// Truncated series product.
pub fn qs_mul(f : Array[Int64], g : Array[Int64], n0 : Int32) -> Array[Int64] {
  let res : Array[Int64] = []
  let mut i = 0
  while i <= n0 {
    res.push(0L)
    i = i + 1
  }
  let fl = if f.length() < n0 + 1 { f.length() } else { n0 + 1 }
  let gl = if g.length() < n0 + 1 { g.length() } else { n0 + 1 }
  let mut j = 0
  while j < fl {
    if f[j] != 0L {
      let mut k = 0
      while k < gl && j + k <= n0 {
        res[j + k] = res[j + k] + f[j] * g[k]
        k = k + 1
      }
    }
    j = j + 1
  }
  res
}

///|
/// Basis of S_k(SL₂(Z)) = Δ·{E₄^a E₆^b : 4a+6b = k−12} (coefficient arrays).
pub fn cusp_basis_sl2(k : Int32) -> Array[Array[Int64]] {
  let n0 = 32
  let d = delta_series(n0)
  let res : Array[Array[Int64]] = []
  for (a, b) in monomials_e4_e6(k - 12) {
    let mono = e4a_e6b(a, b, n0)
    res.push(qs_mul(d.0, mono, n0))
  }
  res
}

///|
/// Express a cusp series in the given basis (Gaussian elimination on the
/// coefficient rows, Double arithmetic). Uses rows 1..n0 of q-expansions.
pub fn coords_in_basis(
  f : Array[Int64],
  basis : Array[Array[Int64]],
) -> Array[Double] {
  let d = basis.length()
  let rows = 2 * d + 2 // enough coefficient rows
  // augmented matrix rows x (d + 1)
  let m : Array[Array[Double]] = []
  let mut r = 1
  while r <= rows {
    let row : Array[Double] = []
    let mut c = 0
    while c < d {
      row.push(basis[c][r].to_double())
      c = c + 1
    }
    row.push(f[r].to_double())
    m.push(row)
    r = r + 1
  }
  // Gaussian elimination
  let mut col = 0
  let pivots : Array[Int32] = []
  let mut rr = 0
  while col < d && rr < m.length() {
    // find pivot
    let mut piv = rr
    let mut best = m[rr][col]
    let mut i = rr + 1
    while i < m.length() {
      let v = m[i][col]
      let av = if v < 0.0 { -v } else { v }
      let ab = if best < 0.0 { -best } else { best }
      if av > ab {
        best = v
        piv = i
      }
      i = i + 1
    }
    if (if best < 0.0 { -best } else { best }) > 0.000000001 {
      // swap
      let tmp = m[rr]
      m[rr] = m[piv]
      m[piv] = tmp
      // eliminate
      let mut i2 = 0
      while i2 < m.length() {
        if i2 != rr {
          let factor = m[i2][col] / m[rr][col]
          let mut j = col
          while j <= d {
            m[i2][j] = m[i2][j] - factor * m[rr][j]
            j = j + 1
          }
        }
        i2 = i2 + 1
      }
      pivots.push(col)
      rr = rr + 1
    }
    col = col + 1
  }
  let res : Array[Double] = []
  let mut c2 = 0
  while c2 < d {
    res.push(0.0)
    c2 = c2 + 1
  }
  // read off solutions (matrix now in reduced form)
  let mut i3 = 0
  while i3 < pivots.length() {
    let pc = pivots[i3]
    res[pc] = m[i3][d] / m[i3][pc]
    i3 = i3 + 1
  }
  res
}

///|
/// Matrix of T_n on the S_k basis (columns = images), as Double.
pub fn hecke_matrix_sl2(
  basis : Array[Array[Int64]],
  n : Int32,
  k : Int32,
) -> Array[Array[Double]] {
  let d = basis.length()
  let res : Array[Array[Double]] = []
  let mut j = 0
  while j < d {
    let img = hecke_operator(basis[j], n, k)
    res.push(coords_in_basis(img, basis))
    j = j + 1
  }
  // transpose to columns-of-images convention: res[i][j] = coeff of basis i
  let out : Array[Array[Double]] = []
  let mut i = 0
  while i < d {
    let row : Array[Double] = []
    let mut jj = 0
    while jj < d {
      row.push(res[jj][i])
      jj = jj + 1
    }
    out.push(row)
    i = i + 1
  }
  out
}

///|
/// 2×2 matrix utilities on Double.
pub fn mat2_eq(
  a : Array[Array[Double]],
  b : Array[Array[Double]],
  tol : Double,
) -> Bool {
  let mut i = 0
  while i < a.length() {
    let mut j = 0
    while j < a.length() {
      let d = a[i][j] - b[i][j]
      if (if d < 0.0 { -d } else { d }) > tol {
        return false
      }
      j = j + 1
    }
    i = i + 1
  }
  true
}

///|
pub fn mat2_mul(
  a : Array[Array[Double]],
  b : Array[Array[Double]],
) -> Array[Array[Double]] {
  let n = a.length()
  let res : Array[Array[Double]] = []
  let mut i = 0
  while i < n {
    let row : Array[Double] = []
    let mut j = 0
    while j < n {
      let mut s = 0.0
      let mut k = 0
      while k < n {
        s = s + a[i][k] * b[k][j]
        k = k + 1
      }
      row.push(s)
      j = j + 1
    }
    res.push(row)
    i = i + 1
  }
  res
}

///|
/// Char poly x² − tr·x + det of a 2×2 Double matrix.
pub fn charpoly_2x2(m : Array[Array[Double]]) -> (Double, Double) {
  (m[0][0] + m[1][1], m[0][0] * m[1][1] - m[0][1] * m[1][0])
}

///|
/// Integrality check: all entries within tol of an integer.
pub fn mat2_integral(m : Array[Array[Double]], tol : Double) -> Bool {
  let mut i = 0
  while i < 2 {
    let mut j = 0
    while j < 2 {
      let x = m[i][j]
      let r = x.round()
      let d = x - r
      if (if d < 0.0 { -d } else { d }) > tol {
        return false
      }
      j = j + 1
    }
    i = i + 1
  }
  true
}
