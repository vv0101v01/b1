///|
/// flag.mbt — 旗簇 (flag varieties) 與仿射格拉斯曼流形 (affine Grassmannian)
///
/// Theorem engine:
///   T11 (旗簇點數): |GL_n(F_q)| = |B(F_q)| · |Fl_n(F_q)|
///   T12 (Gaussian 二項式): Gr(k,n)(F_q) 的點數 = [n k]_q，q-組合恆等式
///   T13 (仿射格拉斯曼/Schubert): Z_p² 中指數 p^m 的子格數 = σ₁(p^m) = Σ_{i=0}^m q^i
///       = Schubert 簇 Gr^{(m)} 的 F_q-點數；頂維度 = ⟨2ρ, λ⟩ = m

///|
/// q^n for small q, n (Int64).
pub fn q_pow(q : Int32, n : Int32) -> Int64 {
  pow64(q.to_int64(), n)
}

///|
/// |GL_n(F_q)| = ∏_{i=0}^{n-1} (q^n - q^i).
pub fn gl_order(n : Int32, q : Int32) -> Int64 {
  let mut acc = 1L
  let mut i = 0
  while i < n {
    acc = acc * (q_pow(q, n) - q_pow(q, i))
    i = i + 1
  }
  acc
}

///|
/// |B(F_q)| = q^{n(n-1)/2} · (q-1)^n (upper triangular invertible).
pub fn b_order(n : Int32, q : Int32) -> Int64 {
  q_pow(q, n * (n - 1) / 2) * q_pow(q - 1, n)
}

///|
/// |Fl_n(F_q)| = |GL_n| / |B|.
pub fn flag_variety_order(n : Int32, q : Int32) -> Int64 {
  gl_order(n, q) / b_order(n, q)
}

///|
/// Row rank of an n×n matrix over F_q (Gaussian elimination), flat array row-major.
pub fn mat_rank(m : Array[Int32], n : Int32, q : Int32) -> Int32 {
  // copy
  let a : Array[Int32] = []
  for x in m {
    let mut y = x % q
    if y < 0 {
      y = y + q
    }
    a.push(y)
  }
  let mut rank = 0
  let mut row = 0
  let mut col = 0
  while row < n && col < n {
    // find pivot
    let mut piv = -1
    let mut r = row
    while r < n {
      if a[r * n + col] != 0 {
        piv = r
        r = n
      } else {
        r = r + 1
      }
    }
    if piv >= 0 {
      // swap rows
      let mut c = 0
      while c < n {
        let t = a[row * n + c]
        a[row * n + c] = a[piv * n + c]
        a[piv * n + c] = t
        c = c + 1
      }
      // scale row
      let inv = mod_inverse(a[row * n + col].to_int64(), q.to_int64()).to_int()
      let mut c2 = 0
      while c2 < n {
        a[row * n + c2] = a[row * n + c2] * inv % q
        c2 = c2 + 1
      }
      // eliminate
      let mut r2 = 0
      while r2 < n {
        if r2 != row && a[r2 * n + col] != 0 {
          let f = a[r2 * n + col]
          let mut c3 = 0
          while c3 < n {
            let mut v = (a[r2 * n + c3] - f * a[row * n + c3]) % q
            if v < 0 {
              v = v + q
            }
            a[r2 * n + c3] = v
            c3 = c3 + 1
          }
        }
        r2 = r2 + 1
      }
      rank = rank + 1
      row = row + 1
      col = col + 1
    } else {
      col = col + 1
    }
  }
  rank
}

///|
/// Count invertible n×n matrices over F_q by brute enumeration (n·q small).
pub fn count_gl_bruteforce(n : Int32, q : Int32) -> Int64 {
  let total = pow_int(q, n * n)
  let mut count = 0L
  let mut idx = 0
  while idx < total {
    let m : Array[Int32] = []
    let mut t = idx
    let mut i = 0
    while i < n * n {
      m.push(t % q)
      t = t / q
      i = i + 1
    }
    if mat_rank(m, n, q) == n {
      count = count + 1L
    }
    idx = idx + 1
  }
  count
}

///|
/// Count invertible upper-triangular matrices over F_q by brute force (small n).
pub fn count_b_bruteforce(n : Int32, q : Int32) -> Int64 {
  // upper triangular positions: n(n+1)/2
  let pos = n * (n + 1) / 2
  let total = pow_int(q, pos)
  let mut count = 0L
  let mut idx = 0
  while idx < total {
    // build matrix
    let m : Array[Int32] = []
    let mut i = 0
    while i < n * n {
      m.push(0)
      i = i + 1
    }
    let mut t = idx
    let mut r = 0
    while r < n {
      let mut c = r
      while c < n {
        m[r * n + c] = t % q
        t = t / q
        c = c + 1
      }
      r = r + 1
    }
    // invertible iff all diagonal nonzero
    let mut ok = true
    let mut r2 = 0
    while r2 < n {
      if m[r2 * n + r2] == 0 {
        ok = false
      }
      r2 = r2 + 1
    }
    if ok {
      count = count + 1L
    }
    idx = idx + 1
  }
  count
}

///|
/// Gaussian binomial [n k]_q as exact integer: ∏_{i=0}^{k-1} (q^{n-i} - 1)/(q^{k-i} - 1).
pub fn gaussian_binom(n : Int32, k : Int32, q : Int32) -> Int64 {
  if k < 0 || k > n {
    return 0L
  }
  let mut num = 1L
  let mut den = 1L
  let mut i = 0
  while i < k {
    num = num * (q_pow(q, n - i) - 1L)
    den = den * (q_pow(q, k - i) - 1L)
    i = i + 1
  }
  num / den
}

///|
/// Count k-dimensional subspaces of F_q^n by enumerating RREF bases (small cases).
/// A subspace is represented by its reduced row echelon form (k×n matrix).
pub fn count_subspaces(n : Int32, k : Int32, q : Int32) -> Int64 {
  if k == 0 {
    return 1L
  }
  if k == 1 {
    // number of 1-dim subspaces = (q^n - 1)/(q - 1)
    return (q_pow(q, n) - 1L) / (q_pow(q, 1) - 1L)
  }
  // recursive: count by first pivot position
  count_subspaces_rec(n, k, q, 0)
}

///|
/// Recursion: count RREF forms with k rows in n columns, pivots starting at col.
fn count_subspaces_rec(n : Int32, k : Int32, q : Int32, col : Int32) -> Int64 {
  if k == 0 {
    return 1L
  }
  if n - col < k {
    return 0L
  }
  let mut total = 0L
  // choose pivot column pc ≥ col
  let mut pc = col
  while pc <= n - k {
    // entries above-pivot row: free in columns before next pivot; here we fix
    // RREF: pivot row has 1 at pc and free entries in columns col..pc-1? no:
    // in RREF the pivot row has zeros before pc, ones at pivots, free entries
    // only in non-pivot columns after pc.
    // number of free entries in this pivot row: columns from pc+1..n-1 minus
    // (k-1) future pivot columns — counted recursively by choosing next pivots.
    // Simplify: free entries at row are q^{(#free cols assigned in recursion)}.
    // We count: sum over next pivot positions of q^{free before next pivot}.
    let rest = count_subspaces_free(n, k, q, pc)
    total = total + rest
    pc = pc + 1
  }
  total
}

///|
/// Count RREF matrices with k rows, current pivot at column pc (already fixed).
/// Free entries of the current pivot row: all non-pivot columns after pc,
/// i.e. (n - pc - 1) columns minus the (k-1) later pivot columns = n - pc - k.
fn count_subspaces_free(n : Int32, k : Int32, q : Int32, pc : Int32) -> Int64 {
  let free_here = n - pc - k
  if k == 1 {
    return q_pow(q, free_here)
  }
  let mut total = 0L
  let mut npc = pc + 1
  while npc <= n - (k - 1) {
    total = total + count_subspaces_free(n, k - 1, q, npc)
    npc = npc + 1
  }
  q_pow(q, free_here) * total
}

///|
/// q-binomial theorem check: coefficient arrays of
/// ∏_{i=0}^{n-1} (1 + q^i t) and Σ_k q^{k(k-1)/2} [n k]_q t^k (as Int64 arrays).
pub fn q_binom_theorem_lhs(n : Int32, q : Int32) -> Array[Int64] {
  // poly in t, coefficients Int64
  let acc : Array[Int64] = []
  acc.push(1L)
  let mut i = 0
  while i < n {
    // multiply by (1 + q^i t)
    let factor = q_pow(q, i)
    let len = acc.length()
    let mut j = len
    while j >= 1 {
      let add = acc[j - 1] * factor
      if j < acc.length() {
        acc[j] = acc[j] + add
      } else {
        acc.push(add)
      }
      j = j - 1
    }
    i = i + 1
  }
  acc
}

///|
pub fn q_binom_theorem_rhs(n : Int32, q : Int32) -> Array[Int64] {
  let acc : Array[Int64] = []
  let mut k = 0
  while k <= n {
    let c = q_pow(q, k * (k - 1) / 2) * gaussian_binom(n, k, q)
    acc.push(c)
    k = k + 1
  }
  acc
}

///|
/// Sublattices of Z_p² of index p^m in Hermite normal form:
/// L = ⟨(a, b), (0, c)⟩ with a·c = p^m, 0 ≤ b < c. Count = Σ_{c | p^m} c = σ₁(p^m).
pub fn sublattice_count(p : Int32, m : Int32) -> Int64 {
  // enumerate HNF
  let mut count = 0L
  let mut c_exp = 0
  while c_exp <= m {
    let c = q_pow(p, c_exp)
    // a·c = p^m with a = p^{m−c_exp}; b ranges 0..c−1
    count = count + c
    c_exp = c_exp + 1
  }
  count
}

///|
/// Closed form σ₁(p^m) = (p^{m+1} - 1)/(p - 1).
pub fn sigma1_pm(p : Int32, m : Int32) -> Int64 {
  (q_pow(p, m + 1) - 1L) / (p.to_int64() - 1L)
}

///|
/// ⟨2ρ, λ⟩ for GL_n with dominant coweight λ = (λ_1 ≥ λ_2 ≥ ... ≥ λ_n):
/// dim of Schubert variety = Σ_i (n + 1 - 2i) λ_i.
pub fn two_rho_pairing(lambda : Array[Int32], n : Int32) -> Int32 {
  let mut s = 0
  let mut i = 0
  while i < n && i < lambda.length() {
    s = s + (n + 1 - 2 * (i + 1)) * lambda[i]
    i = i + 1
  }
  s
}

///|
/// Poincaré polynomial of the SL_2 affine Grassmannian Schubert variety Gr^{(m)}:
/// Σ_{i=0}^{m} q^i (cells of every dimension 0..m).
pub fn schubert_poincare_sl2(m : Int32, q : Int32) -> Int64 {
  sigma1_pm(q, m)
}
