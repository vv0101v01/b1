///|
/// cp4.mbt — 批次七·模組 4：4⁶⁴ 維張量網路的 CP 分解
///
/// 4⁶⁴ = 2¹²⁸ = 340282366920938463463374607431768211456，恰為「64 個量子四元
/// （ququart）模」的希爾伯特空間維度。顯式儲存不可能，故必須以張量網路壓縮：
///   CP 分解：  T(i₁..i_N) = Σ_{a=1}^{r} ∏_{n} A^{(n)}_{i_n, a}      參數量 N·d·r
///   TT/MPS ：  T(i₁..i_N) = B₁[i₁]·B₂[i₂]⋯B_N[i_N]               參數量 2dr + (N−2)dr²
/// 本模組：
///   (1) 以 BigInt 精確處理 4⁶⁴（39 位十進位、129 位元）；
///   (2) 求參數量的「CP vs TT 交叉秩」（d = 4、N = 64）；
///   (3) 以 CP-ALS（交替最小平方）在真實張量上執行分解並量測殘差；
///   (4) 對 GHZ 型張量 T = Σ_{a=0}^{3} e_a^{⊗N} 用**展開矩陣秩**給出 CP 秩的
///       嚴格下界（= 4），並與上界（顯式 4 項分解）夾擠 → CP 秩 = 4。

// ───────────────────────── BigInt：4⁶⁴ 與參數量 ─────────────────────────

///|
/// 4⁶⁴ 的精確十進位字串。
pub fn b7_big_4_64() -> String {
  @bigint.BigInt::from_int(4).pow(@bigint.BigInt::from_int(64)).to_string()
}

///|
/// 4⁶⁴ 的位元長度（應為 129）。
pub fn b7_big_4_64_bits() -> Int32 {
  @bigint.BigInt::from_int(4).pow(@bigint.BigInt::from_int(64)).bit_length()
}

///|
/// CP 分解參數量 N·d·r（BigInt）。
pub fn b7_cp_params(n_modes : Int32, d : Int32, r : Int32) -> @bigint.BigInt {
  @bigint.BigInt::from_int(n_modes * d * r)
}

///|
/// 4⁶⁴ 對 CP（r = 4）的壓縮比（BigInt 商）：4⁶⁴ / (64·4·4)。
pub fn b7_cp_compression_ratio(r : Int32) -> String {
  let total = @bigint.BigInt::from_int(4).pow(@bigint.BigInt::from_int(64))
  let p = b7_cp_params(64, 4, r)
  (total / p).to_string()
}

///|
/// CP 與 TT 的參數量表（N = 64、d = 4），r = 1..8：回傳每秩的 (CP, TT)。
pub fn b7_cp_vs_tt_table() -> Array[(Int32, Int64, Int64)] {
  let out : Array[(Int32, Int64, Int64)] = []
  for r in 1..<9 {
    let cp = (64 * 4 * r).to_int64()
    let tt = (2 * 4 * r + 62 * 4 * r * r).to_int64()
    out.push((r, cp, tt))
  }
  out
}

///|
/// 交叉秩：TT 參數量首次不小於 CP 的最小 r（無則回傳 0）。
pub fn b7_tt_crossover_rank() -> Int32 {
  for r in 1..<200 {
    let cp = 64 * 4 * r
    let tt = 2 * 4 * r + 62 * 4 * r * r
    if tt >= cp {
      return r
    }
  }
  0
}

// ───────────────────────── 展開矩陣秩（CP 秩下界） ─────────────────────────

///|
/// 把 3 模張量以 mode-μ 展開成矩陣（回傳 n_μ × (其餘乘積) 的平坦陣列與維度）。
pub fn b7_unfold3(
  x : Array[Double],
  n1 : Int32,
  n2 : Int32,
  n3 : Int32,
  mu : Int32,
) -> (Array[Double], Int32, Int32) {
  if mu == 1 {
    let rows = n1
    let cols = n2 * n3
    let m : Array[Double] = []
    for i in 0..<n1 {
      for j in 0..<n2 {
        for k in 0..<n3 {
          m.push(x[(i * n2 + j) * n3 + k])
        }
      }
    }
    (m, rows, cols)
  } else if mu == 2 {
    let rows = n2
    let cols = n1 * n3
    let m : Array[Double] = []
    for j in 0..<n2 {
      for i in 0..<n1 {
        for k in 0..<n3 {
          m.push(x[(i * n2 + j) * n3 + k])
        }
      }
    }
    (m, rows, cols)
  } else {
    let rows = n3
    let cols = n1 * n2
    let m : Array[Double] = []
    for k in 0..<n3 {
      for i in 0..<n1 {
        for j in 0..<n2 {
          m.push(x[(i * n2 + j) * n3 + k])
        }
      }
    }
    (m, rows, cols)
  }
}

///|
/// 高斯消去求矩陣秩（部分主元、容忍 1e-9）。
pub fn b7_mat_rank(m : Array[Double], rows : Int32, cols : Int32) -> Int32 {
  let a : Array[Double] = []
  for v in m {
    a.push(v)
  }
  let mut row = 0
  let mut col = 0
  while row < rows && col < cols {
    let mut piv = row
    for r in row..<rows {
      if a[r * cols + col].abs() > a[piv * cols + col].abs() {
        piv = r
      }
    }
    if a[piv * cols + col].abs() < 1.0e-9 {
      col = col + 1
      continue
    }
    if piv != row {
      for j in 0..<cols {
        let t = a[row * cols + j]
        a[row * cols + j] = a[piv * cols + j]
        a[piv * cols + j] = t
      }
    }
    let p = a[row * cols + col]
    for r in (row + 1)..<rows {
      let f = a[r * cols + col] / p
      if f.abs() > 0.0 {
        for j in col..<cols {
          a[r * cols + j] = a[r * cols + j] - f * a[row * cols + j]
        }
      }
    }
    row = row + 1
    col = col + 1
  }
  row
}

///|
/// 3 模張量的三重展開秩（= CP 秩的下界）。
pub fn b7_multirank_lower_bound(
  x : Array[Double],
  n1 : Int32,
  n2 : Int32,
  n3 : Int32,
) -> Int32 {
  let (m1, r1, c1) = b7_unfold3(x, n1, n2, n3, 1)
  let (m2, r2, c2) = b7_unfold3(x, n1, n2, n3, 2)
  let (m3, r3, c3) = b7_unfold3(x, n1, n2, n3, 3)
  let a = b7_mat_rank(m1, r1, c1)
  let b = b7_mat_rank(m2, r2, c2)
  let c = b7_mat_rank(m3, r3, c3)
  let mut best = a
  if b > best {
    best = b
  }
  if c > best {
    best = c
  }
  best
}

// ───────────────────────── CP-ALS ─────────────────────────

///|
/// 3 模張量的 CP-ALS。x 為平坦陣列（n1·n2·n3），r 為目標秩。
/// 回傳 (A, B, C, 相對殘差)。
pub fn b7_cp_als3(
  x : Array[Double],
  n1 : Int32,
  n2 : Int32,
  n3 : Int32,
  r : Int32,
  iters : Int32,
  seed : Int64,
) -> (Array[Array[Double]], Array[Array[Double]], Array[Array[Double]], Double) {
  let a = b7_cp_rand_factor(n1, r, seed)
  let mut b = b7_cp_rand_factor(n2, r, seed + 101L)
  let mut c = b7_cp_rand_factor(n3, r, seed + 211L)
  let mut am = a
  for _ in 0..<iters {
    // 更新 A
    am = b7_cp_update_mode(x, n1, n2, n3, 1, b, c, r)
    // 更新 B
    b = b7_cp_update_mode(x, n1, n2, n3, 2, am, c, r)
    // 更新 C
    c = b7_cp_update_mode(x, n1, n2, n3, 3, am, b, r)
    // 尺度再平衡（不可獨立歸一化！否則乘積被改動）
    b7_cp_rebalance(am, b, c)
  }
  let res = b7_cp_residual(x, n1, n2, n3, am, b, c)
  (am, b, c, res)
}

///|
/// 隨機因子矩陣（LCG）。
pub fn b7_cp_rand_factor(
  n : Int32,
  r : Int32,
  seed : Int64,
) -> Array[Array[Double]] {
  let m : Array[Array[Double]] = []
  let mut s = seed
  for _ in 0..<n {
    let row : Array[Double] = []
    for _ in 0..<r {
      s = s * 6364136223846793005L + 1442695040888963407L
      row.push(((s >> 33).to_int() % 1000).to_double() / 1000.0 + 0.05)
    }
    m.push(row)
  }
  m
}

///|
/// 對第 mu 模做最小平方更新。other1/other2 為另兩個因子。
pub fn b7_cp_update_mode(
  x : Array[Double],
  n1 : Int32,
  n2 : Int32,
  n3 : Int32,
  mu : Int32,
  other1 : Array[Array[Double]],
  other2 : Array[Array[Double]],
  r : Int32,
) -> Array[Array[Double]] {
  // 另外兩模的 Gram 矩陣之 Hadamard 積
  let g1 = b7_cp_gram(other1)
  let g2 = b7_cp_gram(other2)
  let m = b7_mat_zeros(r, r)
  for i in 0..<r {
    for j in 0..<r {
      m[i][j] = g1[i][j] * g2[i][j]
    }
  }
  let minv = b7_mat_inverse(m)
  // 依 mu 建立 RHS
  let n_mu = if mu == 1 { n1 } else if mu == 2 { n2 } else { n3 }
  let rhs = b7_mat_zeros(n_mu, r)
  // 逐「纖維」累加：對 (i,j,k) 三元組
  for i in 0..<n1 {
    for j in 0..<n2 {
      for k in 0..<n3 {
        let v = x[(i * n2 + j) * n3 + k]
        let row = if mu == 1 { i } else if mu == 2 { j } else { k }
        // 另外兩模的索引
        let (o1, o2) = if mu == 1 {
          (j, k)
        } else if mu == 2 {
          (i, k)
        } else {
          (i, j)
        }
        for t in 0..<r {
          rhs[row][t] = rhs[row][t] + v * other1[o1][t] * other2[o2][t]
        }
      }
    }
  }
  // new = rhs · (M⁻¹)ᵀ
  let out = b7_mat_zeros(n_mu, r)
  for i in 0..<n_mu {
    for t in 0..<r {
      let mut s = 0.0
      for u in 0..<r {
        s = s + rhs[i][u] * minv[t][u]
      }
      out[i][t] = s
    }
  }
  out
}

///|
/// FᵀF。
fn b7_cp_gram(f : Array[Array[Double]]) -> Array[Array[Double]] {
  let n = f.length()
  let r = f[0].length()
  let g = b7_mat_zeros(r, r)
  for i in 0..<r {
    for j in 0..<r {
      let mut s = 0.0
      for t in 0..<n {
        s = s + f[t][i] * f[t][j]
      }
      g[i][j] = s
    }
  }
  g
}

///|
/// 把因子矩陣的行歸一化，回傳原本的各行範數（尺度可再吸收到別的因子）。
fn b7_cp_normalize(f : Array[Array[Double]]) -> Array[Double] {
  let n = f.length()
  let r = f[0].length()
  let norms : Array[Double] = []
  for t in 0..<r {
    let mut s = 0.0
    for i in 0..<n {
      s = s + f[i][t] * f[i][t]
    }
    s = s.sqrt()
    norms.push(s)
    if s > 1.0e-12 {
      for i in 0..<n {
        f[i][t] = f[i][t] / s
      }
    }
  }
  norms
}

///|
/// 尺度再平衡：A、B 行歸一化，把總尺度 n_a·n_b·n_c 併入 C，保持乘積不變。
fn b7_cp_rebalance(
  a : Array[Array[Double]],
  b : Array[Array[Double]],
  c : Array[Array[Double]],
) -> Unit {
  let r = a[0].length()
  let na = b7_cp_normalize(a)
  let nb = b7_cp_normalize(b)
  let nc = b7_cp_normalize(c)
  for t in 0..<r {
    let f = na[t] * nb[t] * nc[t]
    for i in 0..<c.length() {
      c[i][t] = c[i][t] * f
    }
  }
}

///|
/// CP 重建的相對殘差 ||X − Σ A∘B∘C||_F / ||X||_F。
pub fn b7_cp_residual(
  x : Array[Double],
  n1 : Int32,
  n2 : Int32,
  n3 : Int32,
  a : Array[Array[Double]],
  b : Array[Array[Double]],
  c : Array[Array[Double]],
) -> Double {
  let r = a[0].length()
  let mut num = 0.0
  let mut den = 0.0
  for i in 0..<n1 {
    for j in 0..<n2 {
      for k in 0..<n3 {
        let mut acc = 0.0
        for t in 0..<r {
          acc = acc + a[i][t] * b[j][t] * c[k][t]
        }
        let d = x[(i * n2 + j) * n3 + k] - acc
        num = num + d * d
        den = den + x[(i * n2 + j) * n3 + k] * x[(i * n2 + j) * n3 + k]
      }
    }
  }
  (num / den).sqrt()
}

///|
/// 由 LCG 產生 3 模隨機張量。
pub fn b7_cp_rand_tensor(
  n1 : Int32,
  n2 : Int32,
  n3 : Int32,
  seed : Int64,
) -> Array[Double] {
  let out : Array[Double] = []
  let mut s = seed
  for _ in 0..<(n1 * n2 * n3) {
    s = s * 6364136223846793005L + 1442695040888963407L
    out.push(((s >> 33).to_int() % 2000).to_double() / 1000.0 - 1.0)
  }
  out
}

// ───────────────────────── GHZ 張量與 CP 秩 ─────────────────────────

///|
/// GHZ 型張量 T(i₁..i_N) = 1（若全部相等）否則 0，維度 d^N（平坦）。
pub fn b7_ghz_tensor(d : Int32, n_modes : Int32) -> Array[Double] {
  let total = b7_pow_int32(d, n_modes)
  let out : Array[Double] = []
  for idx in 0..<total {
    let mut same = true
    let first = idx % d
    let mut m = idx
    for _ in 0..<n_modes {
      if m % d != first {
        same = false
      }
      m = m / d
    }
    out.push(if same { 1.0 } else { 0.0 })
  }
  out
}

///|
/// 整數冪。
pub fn b7_pow_int32(base : Int32, exp : Int32) -> Int32 {
  let mut r = 1
  for _ in 0..<exp {
    r = r * base
  }
  r
}

///|
/// GHZ 的 CP 秩夾擠：下界 = 展開矩陣秩（mode 1），上界 = d（顯式 d 項分解）。
/// 回傳 (n_modes, d, 下界, 上界)。
pub fn b7_ghz_rank_squeeze(
  d : Int32,
  n_modes : Int32,
) -> (Int32, Int32, Int32, Int32) {
  let t = b7_ghz_tensor(d, n_modes)
  // 以 3 模展開（僅支援 n_modes = 3）
  let lb = b7_multirank_lower_bound(t, d, d, d)
  (n_modes, d, lb, d)
}

///|
/// GHZ₃ 的 CP-ALS 實測：秩 r = 3、4 時的相對殘差。
pub fn b7_ghz_als_residuals(r : Int32, iters : Int32) -> Double {
  let t = b7_ghz_tensor(4, 3)
  let (_, _, _, res) = b7_cp_als3(t, 4, 4, 4, r, iters, 7L)
  res
}

///|
/// 隨機 4×4×4 張量在各秩的 CP-ALS 相對殘差表：Array[(r, residual)]。
pub fn b7_cp_rank_sweep(iters : Int32) -> Array[(Int32, Double)] {
  let t = b7_cp_rand_tensor(4, 4, 4, 99L)
  let out : Array[(Int32, Double)] = []
  for r in 1..<9 {
    let (_, _, _, res) = b7_cp_als3(t, 4, 4, 4, r, iters, 31L)
    out.push((r, res))
  }
  out
}
