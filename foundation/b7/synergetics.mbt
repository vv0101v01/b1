///|
/// synergetics.mbt — 批次七·模組 3：哈肯–茲萬齊格快慢變數分離協同學
///
/// 線性協同學模型：x = (x_s, x_f)，慢變數 x_s ∈ R^m、快變數 x_f ∈ R^f
///   ẋ_s = A_ss x_s + A_sf x_f
///   ẋ_f = A_fs x_s + A_ff x_f
/// 假設譜分離 |λ(A_ff)| ≫ |λ(A_ss)|，ε := |λ_slow|/|λ_fast| ≪ 1。
///
/// 三個層次的「壓縮」：
///  (1) 絕熱消去（Haken 1977，零階）：x_f ≈ Γ x_s，Γ = −A_ff⁻¹A_fs
///      慢方程：ẋ_s = S x_s，S = A_ss − A_sf A_ff⁻¹ A_fs = 舒爾補（Schur complement）
///  (2) 不變流形（精確線性情形）：解 Sylvester 方程
///      A_ss X − X A_ff + A_sf − X A_fs X = 0
///      的精確解 X，使圖 graph(X) 為不變子空間 ⇒ x_f(t) = X x_s(t) 永真
///  (3) 森–茲萬齊格（Mori–Zwanzig）廣義朗之萬方程：
///      ẋ_s(t) = A_ss x_s(t) + ∫₀ᵗ K(t−s) x_s(s) ds + A_sf e^{A_ff t} x_f(0)，
///      K(τ) = A_sf e^{A_ff τ} A_fs
///      而 Markov 極限 ∫₀^∞ K dτ = −A_sf A_ff⁻¹ A_fs，正值 S − A_ss：
///      **絕熱消去 = 記憶核的零階 Markov 截斷**（本模組用數值積分驗證）。
/// 模組同時量出壓縮誤差的 ε 標度指數（預期 2）。

// ───────────────────────── 密集矩陣工具 ─────────────────────────

///|
/// n×m 零矩陣。
pub fn b7_mat_zeros(n : Int32, m : Int32) -> Array[Array[Double]] {
  let a : Array[Array[Double]] = []
  for _ in 0..<n {
    let row : Array[Double] = []
    for _ in 0..<m {
      row.push(0.0)
    }
    a.push(row)
  }
  a
}

///|
/// 單位矩陣。
pub fn b7_mat_identity(n : Int32) -> Array[Array[Double]] {
  let a = b7_mat_zeros(n, n)
  for i in 0..<n {
    a[i][i] = 1.0
  }
  a
}

///|
/// 由平坦陣列與維度建矩陣。
pub fn b7_mat_of(
  n : Int32,
  m : Int32,
  vals : Array[Double],
) -> Array[Array[Double]] {
  let a = b7_mat_zeros(n, m)
  for i in 0..<n {
    for j in 0..<m {
      a[i][j] = vals[i * m + j]
    }
  }
  a
}

///|
/// 矩陣乘法。
pub fn b7_mat_mul(
  a : Array[Array[Double]],
  b : Array[Array[Double]],
) -> Array[Array[Double]] {
  let n = a.length()
  let k = b.length()
  let m = b[0].length()
  let c = b7_mat_zeros(n, m)
  for i in 0..<n {
    for j in 0..<m {
      let mut s = 0.0
      for t in 0..<k {
        s = s + a[i][t] * b[t][j]
      }
      c[i][j] = s
    }
  }
  c
}

///|
/// 矩陣加法。
pub fn b7_mat_add(
  a : Array[Array[Double]],
  b : Array[Array[Double]],
) -> Array[Array[Double]] {
  let n = a.length()
  let m = a[0].length()
  let c = b7_mat_zeros(n, m)
  for i in 0..<n {
    for j in 0..<m {
      c[i][j] = a[i][j] + b[i][j]
    }
  }
  c
}

///|
/// 矩陣減法。
pub fn b7_mat_sub(
  a : Array[Array[Double]],
  b : Array[Array[Double]],
) -> Array[Array[Double]] {
  let n = a.length()
  let m = a[0].length()
  let c = b7_mat_zeros(n, m)
  for i in 0..<n {
    for j in 0..<m {
      c[i][j] = a[i][j] - b[i][j]
    }
  }
  c
}

///|
/// 純量乘。
pub fn b7_mat_scale(
  a : Array[Array[Double]],
  s : Double,
) -> Array[Array[Double]] {
  let n = a.length()
  let m = a[0].length()
  let c = b7_mat_zeros(n, m)
  for i in 0..<n {
    for j in 0..<m {
      c[i][j] = a[i][j] * s
    }
  }
  c
}

///|
/// Frobenius 範數。
pub fn b7_mat_frob(a : Array[Array[Double]]) -> Double {
  let mut s = 0.0
  for row in a {
    for v in row {
      s = s + v * v
    }
  }
  s.sqrt()
}

///|
/// 高斯–約當反矩陣（部分主元）。
pub fn b7_mat_inverse(a : Array[Array[Double]]) -> Array[Array[Double]] {
  let n = a.length()
  let w = b7_mat_zeros(n, 2 * n)
  for i in 0..<n {
    for j in 0..<n {
      w[i][j] = a[i][j]
    }
    w[i][n + i] = 1.0
  }
  for col in 0..<n {
    // 主元
    let mut piv = col
    for r in col..<n {
      if w[r][col].abs() > w[piv][col].abs() {
        piv = r
      }
    }
    if piv != col {
      for j in 0..<(2 * n) {
        let t = w[col][j]
        w[col][j] = w[piv][j]
        w[piv][j] = t
      }
    }
    let d = w[col][col]
    for j in 0..<(2 * n) {
      w[col][j] = w[col][j] / d
    }
    for r in 0..<n {
      if r != col {
        let f = w[r][col]
        if f.abs() > 0.0 {
          for j in 0..<(2 * n) {
            w[r][j] = w[r][j] - f * w[col][j]
          }
        }
      }
    }
  }
  let out = b7_mat_zeros(n, n)
  for i in 0..<n {
    for j in 0..<n {
      out[i][j] = w[i][n + j]
    }
  }
  out
}

///|
/// 解 A X = B。
pub fn b7_mat_solve(
  a : Array[Array[Double]],
  b : Array[Array[Double]],
) -> Array[Array[Double]] {
  b7_mat_mul(b7_mat_inverse(a), b)
}

///|
/// 取子矩陣（行 r0..r1、列 c0..c1，不含上界）。
pub fn b7_mat_block(
  a : Array[Array[Double]],
  r0 : Int32,
  r1 : Int32,
  c0 : Int32,
  c1 : Int32,
) -> Array[Array[Double]] {
  let c = b7_mat_zeros(r1 - r0, c1 - c0)
  for i in 0..<(r1 - r0) {
    for j in 0..<(c1 - c0) {
      c[i][j] = a[r0 + i][c0 + j]
    }
  }
  c
}

///|
/// n×n 對稱矩陣的 Jacobi 特徵分解。回傳 (特徵值, 特徵向量矩陣（行 = 向量）)。
pub fn b7_jacobi_eigen(
  a : Array[Array[Double]],
) -> (Array[Double], Array[Array[Double]]) {
  let n = a.length()
  let w = b7_mat_zeros(n, n)
  for i in 0..<n {
    for j in 0..<n {
      w[i][j] = a[i][j]
    }
  }
  let v = b7_mat_identity(n)
  for _sweep in 0..<60 {
    let mut off = 0.0
    for i in 0..<n {
      for j in 0..<n {
        if i != j {
          off = off + w[i][j] * w[i][j]
        }
      }
    }
    if off.sqrt() < 1.0e-14 {
      break
    }
    for p in 0..<n {
      for q in (p + 1)..<n {
        if w[p][q].abs() > 1.0e-18 {
          let theta = (w[q][q] - w[p][p]) / (2.0 * w[p][q])
          let t = if theta >= 0.0 {
            1.0 / (theta + (1.0 + theta * theta).sqrt())
          } else {
            -1.0 / (-theta + (1.0 + theta * theta).sqrt())
          }
          let c = 1.0 / (1.0 + t * t).sqrt()
          let s = t * c
          for k in 0..<n {
            let akp = w[k][p]
            let akq = w[k][q]
            w[k][p] = c * akp - s * akq
            w[k][q] = s * akp + c * akq
          }
          for k in 0..<n {
            let apk = w[p][k]
            let aqk = w[q][k]
            w[p][k] = c * apk - s * aqk
            w[q][k] = s * apk + c * aqk
          }
          for k in 0..<n {
            let vkp = v[k][p]
            let vkq = v[k][q]
            v[k][p] = c * vkp - s * vkq
            v[k][q] = s * vkp + c * vkq
          }
        }
      }
    }
  }
  let vals : Array[Double] = []
  for i in 0..<n {
    vals.push(w[i][i])
  }
  (vals, v)
}

// ───────────────────────── 分塊與舒爾補 ─────────────────────────

///|
/// 分塊：回傳 (A_ss, A_sf, A_fs, A_ff)。
pub fn b7_partition(
  a : Array[Array[Double]],
  m : Int32,
) -> (
  Array[Array[Double]],
  Array[Array[Double]],
  Array[Array[Double]],
  Array[Array[Double]],
) {
  let n = a.length()
  let ss = b7_mat_block(a, 0, m, 0, m)
  let sf = b7_mat_block(a, 0, m, m, n)
  let fs = b7_mat_block(a, m, n, 0, m)
  let ff = b7_mat_block(a, m, n, m, n)
  (ss, sf, fs, ff)
}

///|
/// 舒爾補 S = A_ss − A_sf A_ff⁻¹ A_fs。
pub fn b7_schur_complement(
  a : Array[Array[Double]],
  m : Int32,
) -> Array[Array[Double]] {
  let (ss, sf, fs, ff) = b7_partition(a, m)
  b7_mat_sub(ss, b7_mat_mul(b7_mat_mul(sf, b7_mat_inverse(ff)), fs))
}

///|
/// 絕熱消去映射 Γ = −A_ff⁻¹ A_fs（快變數的壓縮座標）。
pub fn b7_adiabatic_map(
  a : Array[Array[Double]],
  m : Int32,
) -> Array[Array[Double]] {
  let (_, _, fs, ff) = b7_partition(a, m)
  b7_mat_scale(b7_mat_mul(b7_mat_inverse(ff), fs), -1.0)
}

// ───────────────────────── Sylvester 方程與不變流形 ─────────────────────────

///|
/// 解 A X − X B = C（Kronecker 向量化： (I⊗A − Bᵀ⊗I) vec X = vec C）。
pub fn b7_sylvester(
  a : Array[Array[Double]],
  b : Array[Array[Double]],
  c : Array[Array[Double]],
) -> Array[Array[Double]] {
  let m = a.length()
  let f = b.length()
  let n = m * f
  let big = b7_mat_zeros(n, n)
  for i in 0..<m {
    for j in 0..<m {
      for col in 0..<f {
        // (I_f ⊗ A)：列指標 = col*m + i，行指標 = col*m + j
        big[col * m + i][col * m + j] = a[i][j]
      }
    }
  }
  for p in 0..<f {
    for q in 0..<f {
      for row in 0..<m {
        // (Bᵀ ⊗ I_m)：列指標 = p*m + row，行指標 = q*m + row
        big[p * m + row][q * m + row] = big[p * m + row][q * m + row] - b[q][p]
      }
    }
  }
  let rhs = b7_mat_zeros(n, 1)
  for i in 0..<m {
    for j in 0..<f {
      rhs[j * m + i][0] = c[i][j]
    }
  }
  let sol = b7_mat_solve(big, rhs)
  let x = b7_mat_zeros(m, f)
  for i in 0..<m {
    for j in 0..<f {
      x[i][j] = sol[j * m + i][0]
    }
  }
  x
}

///|
/// 不變流形迭代。以圖座標 X : R^m → R^f（size f×m，x_f = X x_s）表示，
/// 不變性條件為
///   X A_ss − A_ff X + X A_sf X − A_fs = 0
/// 迭代 X_{k+1} = Sylvester(−A_ff, −A_ss, A_fs − X_k A_sf X_k)。
/// 收斂時 graph(X) 為精確不變子空間，且 X → Γ（絕熱映射）當 ε → 0。
/// 回傳 (X, 最終殘差, 迭代次數)。
pub fn b7_invariant_manifold(
  a : Array[Array[Double]],
  m : Int32,
  iters : Int32,
) -> (Array[Array[Double]], Double, Int32) {
  let (ss, sf, fs, ff) = b7_partition(a, m)
  let negss = b7_mat_scale(ss, -1.0)
  let negff = b7_mat_scale(ff, -1.0)
  let mut x = b7_adiabatic_map(a, m)
  let mut res = 1.0e9
  let mut used = 0
  for it in 0..<iters {
    let c = b7_mat_sub(fs, b7_mat_mul(b7_mat_mul(x, sf), x))
    let xnew = b7_sylvester(negff, negss, c)
    let r = b7_mat_sub(
      b7_mat_add(
        b7_mat_sub(b7_mat_mul(xnew, ss), b7_mat_mul(ff, xnew)),
        b7_mat_mul(b7_mat_mul(xnew, sf), xnew),
      ),
      fs,
    )
    res = b7_mat_frob(r)
    x = xnew
    used = it + 1
    if res < 1.0e-13 {
      break
    }
  }
  (x, res, used)
}

// ───────────────────────── 譜分離與誤差標度 ─────────────────────────

///|
/// 以對稱矩陣驗證：eig(S) ≈ A 的 m 個「最慢」特徵值（|λ| 最小者）。
/// 回傳最大偏差。
pub fn b7_schur_spectrum_error(a : Array[Array[Double]], m : Int32) -> Double {
  let (vals, _) = b7_jacobi_eigen(a)
  let s = b7_schur_complement(a, m)
  let (sv, _) = b7_jacobi_eigen(s)
  // 取 |λ| 最小的 m 個
  let n = vals.length()
  let idx : Array[Int32] = []
  for i in 0..<n {
    idx.push(i)
  }
  for i in 0..<n {
    let mut j = i + 1
    while j < n {
      if vals[idx[j]].abs() < vals[idx[i]].abs() {
        let t = idx[i]
        idx[i] = idx[j]
        idx[j] = t
      }
      j = j + 1
    }
  }
  let slow : Array[Double] = []
  for i in 0..<m {
    slow.push(vals[idx[i]])
  }
  // 兩邊皆排序後比較
  for i in 0..<m {
    let mut j = i + 1
    while j < m {
      if slow[j] < slow[i] {
        let t = slow[i]
        slow[i] = slow[j]
        slow[j] = t
      }
      j = j + 1
    }
  }
  let svs : Array[Double] = []
  for v in sv {
    svs.push(v)
  }
  for i in 0..<m {
    let mut j = i + 1
    while j < m {
      if svs[j] < svs[i] {
        let t = svs[i]
        svs[i] = svs[j]
        svs[j] = t
      }
      j = j + 1
    }
  }
  let mut err = 0.0
  for i in 0..<m {
    let d = (slow[i] - svs[i]).abs()
    if d > err {
      err = d
    }
  }
  err
}

///|
/// 協同學標準二維快慢模型：
///   A = [[−1, κ], [κ, −1/ε]]
/// 回傳 (ε, |eig(S) − λ_slow|)。
pub fn b7_two_mode_error(eps : Double, kappa : Double) -> (Double, Double) {
  let a = b7_mat_of(2, 2, [-1.0, kappa, kappa, -1.0 / eps])
  (eps, b7_schur_spectrum_error(a, 1))
}

///|
/// 以 log-log 最小二乘擬合誤差標度指數：err ≈ C ε^p，回傳 p。
pub fn b7_fit_exponent(epss : Array[Double], errs : Array[Double]) -> Double {
  let n = epss.length().to_double()
  let mut sx = 0.0
  let mut sy = 0.0
  let mut sxx = 0.0
  let mut sxy = 0.0
  for i in 0..<epss.length() {
    let x = @math.ln(epss[i])
    let y = @math.ln(errs[i])
    sx = sx + x
    sy = sy + y
    sxx = sxx + x * x
    sxy = sxy + x * y
  }
  (n * sxy - sx * sy) / (n * sxx - sx * sx)
}

// ───────────────────────── 森–茲萬齊格記憶核 ─────────────────────────

///|
/// e^{Bt}：Taylor 級數 + 縮放平方（scaling & squaring），避免大範數時的溢位。
pub fn b7_mat_expm(
  b : Array[Array[Double]],
  t : Double,
) -> Array[Array[Double]] {
  let n = b.length()
  let norm = b7_mat_frob(b) * t.abs()
  let mut s = 0
  let mut scaled = 1.0
  while norm / scaled > 0.25 && s < 40 {
    scaled = scaled * 2.0
    s = s + 1
  }
  let bs = b7_mat_scale(b, t / scaled)
  let mut acc = b7_mat_identity(n)
  let mut term = b7_mat_identity(n)
  for k in 1..<20 {
    term = b7_mat_scale(b7_mat_mul(term, bs), 1.0 / k.to_double())
    acc = b7_mat_add(acc, term)
  }
  for _ in 0..<s {
    acc = b7_mat_mul(acc, acc)
  }
  acc
}

///|
/// 記憶核 K(τ) = A_sf e^{A_ff τ} A_fs（回傳 m×m 矩陣）。
pub fn b7_memory_kernel(
  a : Array[Array[Double]],
  m : Int32,
  tau : Double,
) -> Array[Array[Double]] {
  let (_, sf, fs, ff) = b7_partition(a, m)
  b7_mat_mul(b7_mat_mul(sf, b7_mat_expm(ff, tau)), fs)
}

///|
/// Markov 極限：以數值積分 ∫₀^T K dτ 逼近，與 −A_sf A_ff⁻¹ A_fs 比較。
/// 回傳 (數值積分矩陣, 解析矩陣) 的差的 Frobenius 範數。
pub fn b7_markov_limit_error(
  a : Array[Array[Double]],
  m : Int32,
  tmax : Double,
  steps : Int32,
) -> Double {
  let h = tmax / steps.to_double()
  let num = b7_mat_zeros(m, m)
  for i in 0..<steps {
    let tau = (i.to_double() + 0.5) * h
    let k = b7_memory_kernel(a, m, tau)
    for r in 0..<m {
      for c in 0..<m {
        num[r][c] = num[r][c] + k[r][c] * h
      }
    }
  }
  let (ss, _, _, _) = b7_partition(a, m)
  let ana = b7_mat_sub(b7_schur_complement(a, m), ss)
  let mut e = 0.0
  for r in 0..<m {
    for c in 0..<m {
      e = e + (num[r][c] - ana[r][c]) * (num[r][c] - ana[r][c])
    }
  }
  // 忽略 A_sf A_ff⁻¹ A_fs 項的整體符號（此處兩者應同號：皆為 −A_sf A_ff⁻¹ A_fs）
  e.sqrt()
}

///|
/// 直接驗證廣義朗之萬方程：比較 (a) 全系統 RK4 解的慢分量；
/// (b) 以記憶積分計算的 GLE 右端之累積解。回傳最終偏差。
pub fn b7_gle_check(
  a : Array[Array[Double]],
  m : Int32,
  horizon : Double,
  steps : Int32,
) -> Double {
  let n = a.length()
  let f = n - m
  let (ss, sf, _, ff) = b7_partition(a, m)
  let dt = horizon / steps.to_double()
  // 初值
  let xs = b7_mat_zeros(m, 1)
  let xf = b7_mat_zeros(f, 1)
  for i in 0..<m {
    xs[i][0] = 1.0
  }
  for i in 0..<f {
    xf[i][0] = 0.3
  }
  // (a) 全系統
  let full = b7_mat_zeros(n, 1)
  for i in 0..<m {
    full[i][0] = xs[i][0]
  }
  for i in 0..<f {
    full[m + i][0] = xf[i][0]
  }
  let traj : Array[Array[Array[Double]]] = []
  for _ in 0..<(steps + 1) {
    traj.push(b7_mat_zeros(m, 1))
  }
  for i in 0..<m {
    traj[0][i][0] = full[i][0]
  }
  let mut cur = full
  for s in 0..<steps {
    cur = b7_rk4_linear(a, cur, dt)
    for i in 0..<m {
      traj[s + 1][i][0] = cur[i][0]
    }
  }
  // (b) GLE：ẋ_s = A_ss x_s + ∫₀ᵗ K(t−s)x_s(s)ds + A_sf e^{A_ff t} x_f(0)
  let mut xs2 = b7_mat_zeros(m, 1)
  for i in 0..<m {
    xs2[i][0] = xs[i][0]
  }
  let hist : Array[Array[Array[Double]]] = []
  hist.push(xs2)
  let mut t = 0.0
  for _ in 0..<steps {
    // 記憶積分（梯形）
    let mem = b7_mat_zeros(m, 1)
    let steps_so_far = hist.length() - 1
    if steps_so_far > 0 {
      for j in 0..<(steps_so_far + 1) {
        let sj = j.to_double() * dt
        let k = b7_memory_kernel(a, m, t - sj)
        let w = if j == 0 || j == steps_so_far { dt * 0.5 } else { dt }
        let kx = b7_mat_mul(k, hist[j])
        for r in 0..<m {
          mem[r][0] = mem[r][0] + kx[r][0] * w
        }
      }
    }
    let drift = b7_mat_mul(b7_mat_mul(sf, b7_mat_expm(ff, t)), xf)
    let ssx = b7_mat_mul(ss, xs2)
    let dx = b7_mat_zeros(m, 1)
    for r in 0..<m {
      dx[r][0] = ssx[r][0] + mem[r][0] + drift[r][0]
    }
    xs2 = b7_mat_add(xs2, b7_mat_scale(dx, dt))
    hist.push(xs2)
    t = t + dt
  }
  let mut err = 0.0
  for i in 0..<m {
    let d = xs2[i][0] - traj[steps][i][0]
    err = err + d * d
  }
  err.sqrt()
}

///|
/// 線性系統的 RK4 單步。
fn b7_rk4_linear(
  a : Array[Array[Double]],
  x : Array[Array[Double]],
  dt : Double,
) -> Array[Array[Double]] {
  let k1 = b7_mat_mul(a, x)
  let k2 = b7_mat_mul(a, b7_mat_add(x, b7_mat_scale(k1, dt * 0.5)))
  let k3 = b7_mat_mul(a, b7_mat_add(x, b7_mat_scale(k2, dt * 0.5)))
  let k4 = b7_mat_mul(a, b7_mat_add(x, b7_mat_scale(k3, dt)))
  let inc = b7_mat_add(
    b7_mat_add(k1, b7_mat_scale(k2, 2.0)),
    b7_mat_add(b7_mat_scale(k3, 2.0), k4),
  )
  b7_mat_add(x, b7_mat_scale(inc, dt / 6.0))
}

// ───────────────────────── 非線性中心流形展開 ─────────────────────────

///|
/// 非線性快慢系統（1 慢 / 1 快）：
///   ẋ = ass·x + κy + qx²,  ẏ = κx + aff·y + ry²   （ass = −1，aff = −1/ε）
/// 不變流形 y = h(x) = h₁x + h₂x² + h₃x³ 的係數逐階求得：
///   x¹: κh₁² + (ass − aff)h₁ − κ = 0                （二次代數方程！）
///   x²: h₂ = (r h₁² − q h₁)/(3κh₁ + 2ass − aff)
///   x³: h₃ = (2r h₁h₂ − 2h₂(κh₂ + q))/(4κh₁ + 3ass − aff)
/// 注意絕熱消去只給 h₁ ≈ −κ/aff = κε（拋物線的線性化），非精確根。
/// 回傳 (h₁, h₂, h₃)。
pub fn b7_cm_coefficients(
  kappa : Double,
  eps : Double,
  q : Double,
  r : Double,
) -> (Double, Double, Double) {
  let aff = -1.0 / eps
  let ass = -1.0
  // h₁ 取趨近 0 的小根
  let bcoef = ass - aff
  let disc = bcoef * bcoef + 4.0 * kappa * kappa
  let h1 = if kappa.abs() < 1.0e-14 {
    kappa / bcoef
  } else {
    let r1 = (-bcoef + disc.sqrt()) / (2.0 * kappa)
    let r2 = (-bcoef - disc.sqrt()) / (2.0 * kappa)
    if r1.abs() < r2.abs() {
      r1
    } else {
      r2
    }
  }
  let h2 = (r * h1 * h1 - q * h1) / (3.0 * kappa * h1 + 2.0 * ass - aff)
  let h3 = (2.0 * r * h1 * h2 - 2.0 * h2 * (kappa * h2 + q)) /
    (4.0 * kappa * h1 + 3.0 * ass - aff)
  (h1, h2, h3)
}

///|
/// 不變性殘差：R(x) = h'(x)·ẋ(x, h(x)) − ẏ(x, h(x))，
/// 其中 ẋ = ass·x + κh + qx²、ẏ = κx + aff·h + rh²。
/// 回傳 x ∈ [−0.5, 0.5] 上 41 點的最大絕對殘差。
pub fn b7_cm_residual(
  kappa : Double,
  eps : Double,
  q : Double,
  r : Double,
  nterms : Int32,
) -> Double {
  let aff = -1.0 / eps
  let ass = -1.0
  let (h1, h2, h3) = b7_cm_coefficients(kappa, eps, q, r)
  let mut worst = 0.0
  for step in 0..<41 {
    let x = -0.5 + step.to_double() * 0.025
    let mut h = h1 * x
    let mut dh = h1
    if nterms >= 2 {
      h = h + h2 * x * x
      dh = dh + 2.0 * h2 * x
    }
    if nterms >= 3 {
      h = h + h3 * x * x * x
      dh = dh + 3.0 * h3 * x * x
    }
    let xdot = ass * x + kappa * h + q * x * x
    let ydot = kappa * x + aff * h + r * h * h
    let res = (dh * xdot - ydot).abs()
    if res > worst {
      worst = res
    }
  }
  worst
}
