///|
/// tprod.mbt — 批次七·模組 2：快葉射影 t-Product 與循環卷積
///
/// 三階張量 A ∈ R^{n₁×n₂×n₃}，其「管（tube）」A(i,j,:) 為長度 n₃ 的向量。
/// Kilmer–Martin 的 t-product 定義為**管方向的循環卷積**：
///   (A * B)(i,j,k) = Σ_m Σ_l A(i,m,l)·B(m,j,(k−l) mod n₃)
/// 由於循環卷積被 DFT 對角化，t-product 可「快葉」計算：
///   bcirc(A) = (F_{n₃} ⊗ I_{n₁}) · blockdiag(Â_1..Â_{n₃}) · (F_{n₃}^* ⊗ I_{n₂})
/// 即：對第 3 模做 DFT（「葉變換」），逐頻率做矩陣乘法，再逆變換。
///
/// 射影化的關鍵觀察：頻域每個切片只由「乘積」進入 t-product，
/// 故對任意單位相位 λ_f ∈ S¹，
///   (λ_f Â_f) · (λ̄_f B̂_f) = Â_f B̂_f
/// 即 t-product 只依賴 A 在「射影頻率叢」P^{n₃−1} 上的點 [A]。
/// 本模組把這兩件事都**數值驗證**，並據此導出 t-SVD 與張量核範數。

// ───────────────────────── 複數 ─────────────────────────

///|
/// 複數。
#derive(Debug)
pub(all) struct Cx7 {
  re : Double
  im : Double
}

///|
/// 建構複數。
pub fn b7_cx(re : Double, im : Double) -> Cx7 {
  { re, im, }
}

///|
/// 複數加法。
pub fn b7_cx_add(a : Cx7, b : Cx7) -> Cx7 {
  { re: a.re + b.re, im: a.im + b.im, }
}

///|
/// 複數乘法。
pub fn b7_cx_mul(a : Cx7, b : Cx7) -> Cx7 {
  { re: a.re * b.re - a.im * b.im, im: a.re * b.im + a.im * b.re, }
}

///|
/// 複數共軛。
pub fn b7_cx_conj(a : Cx7) -> Cx7 {
  { re: a.re, im: -a.im, }
}

///|
/// 模長平方。
pub fn b7_cx_norm2(a : Cx7) -> Double {
  a.re * a.re + a.im * a.im
}

///|
/// exp(iθ)。
pub fn b7_cx_phase(theta : Double) -> Cx7 {
  { re: @math.cos(theta), im: @math.sin(theta), }
}

// ───────────────────────── 三階張量 ─────────────────────────

///|
/// 三階實張量（row-major 平坦儲存）。
pub(all) struct T3 {
  n1 : Int32
  n2 : Int32
  n3 : Int32
  d : Array[Double]
}

///|
/// 配置 n₁×n₂×n₃ 的零張量。
pub fn b7_t3_new(n1 : Int32, n2 : Int32, n3 : Int32) -> T3 {
  let d : Array[Double] = []
  for _ in 0..<(n1 * n2 * n3) {
    d.push(0.0)
  }
  { n1, n2, n3, d, }
}

///|
/// 索引。
pub fn b7_ten3_idx(t : T3, i : Int32, j : Int32, k : Int32) -> Int32 {
  (i * t.n2 + j) * t.n3 + k
}

///|
/// 取值。
pub fn b7_ten3_get(t : T3, i : Int32, j : Int32, k : Int32) -> Double {
  t.d[b7_ten3_idx(t, i, j, k)]
}

///|
/// 設值。
pub fn b7_ten3_set(t : T3, i : Int32, j : Int32, k : Int32, v : Double) -> Unit {
  t.d[b7_ten3_idx(t, i, j, k)] = v
}

///|
/// 由 LCG 產生「隨機」張量（確定性種子，保證可重現）。
pub fn b7_ten3_rand(n1 : Int32, n2 : Int32, n3 : Int32, seed : Int64) -> T3 {
  let t = b7_t3_new(n1, n2, n3)
  let mut s = seed
  for idx in 0..<(n1 * n2 * n3) {
    s = s * 6364136223846793005L + 1442695040888963407L
    let r = ((s >> 33).to_int() % 2000).to_double() / 1000.0 - 1.0
    t.d[idx] = r
  }
  t
}

///|
/// Frobenius 範數。
pub fn b7_ten3_frob(t : T3) -> Double {
  let mut s = 0.0
  for v in t.d {
    s = s + v * v
  }
  s.sqrt()
}

///|
/// 逐元素差之 Frobenius 範數。
pub fn b7_ten3_dist(a : T3, b : T3) -> Double {
  let mut s = 0.0
  for idx in 0..<a.d.length() {
    let e = a.d[idx] - b.d[idx]
    s = s + e * e
  }
  s.sqrt()
}

// ───────────────────────── DFT / FFT（葉變換） ─────────────────────────

///|
/// 樸素 DFT（可帶逆變換，逆變換含 1/n 歸一化）。
pub fn b7_dft(a : Array[Cx7], inv : Bool) -> Array[Cx7] {
  let n = a.length()
  let out : Array[Cx7] = []
  for k in 0..<n {
    let mut acc = b7_cx(0.0, 0.0)
    for t in 0..<n {
      let ang = 2.0 *
        3.141592653589793 *
        (t.to_double() * k.to_double() / n.to_double())
      let w = if inv { b7_cx_phase(ang) } else { b7_cx_phase(-ang) }
      acc = b7_cx_add(acc, b7_cx_mul(a[t], w))
    }
    if inv {
      acc = b7_cx(acc.re / n.to_double(), acc.im / n.to_double())
    }
    out.push(acc)
  }
  out
}

///|
/// 基 2 遞迴 FFT（n 必須為 2 的冪）。回傳 (結果, 蝶形運算次數)。
pub fn b7_fft(a : Array[Cx7], inv : Bool) -> Array[Cx7] {
  let n = a.length()
  let out : Array[Cx7] = []
  for v in a {
    out.push(v)
  }
  // 位元反轉排序
  let bits = b7_log2i(n)
  for i in 0..<n {
    let j = b7_bit_reverse(i, bits)
    if j > i {
      let tmp = out[i]
      out[i] = out[j]
      out[j] = tmp
    }
  }
  let mut len = 2
  while len <= n {
    let half = len / 2
    for k in 0..<half {
      let ang = 2.0 * 3.141592653589793 * k.to_double() / len.to_double()
      let w = if inv { b7_cx_phase(ang) } else { b7_cx_phase(-ang) }
      let mut i = 0
      while i < n {
        let u = out[i + k]
        let v = b7_cx_mul(out[i + k + half], w)
        out[i + k] = b7_cx_add(u, v)
        out[i + k + half] = b7_cx(u.re - v.re, u.im - v.im)
        i = i + len
      }
    }
    len = len * 2
  }
  if inv {
    for i in 0..<n {
      out[i] = b7_cx(out[i].re / n.to_double(), out[i].im / n.to_double())
    }
  }
  out
}

///|
/// log2（整數，n 為 2 的冪）。
fn b7_log2i(n : Int32) -> Int32 {
  let mut k = 0
  let mut m = n
  while m > 1 {
    m = m / 2
    k = k + 1
  }
  k
}

///|
/// 位元反轉（固定 bits 位）。
fn b7_bit_reverse(x : Int32, bits : Int32) -> Int32 {
  let mut r = 0
  let mut xv = x
  for _ in 0..<bits {
    r = r * 2 + xv % 2
    xv = xv / 2
  }
  r
}

///|
/// 兩者是否一致（用於核對 FFT 與 DFT）。
pub fn b7_dft_matches_fft(n : Int32) -> Bool {
  let a : Array[Cx7] = []
  let mut s = 12345L
  for _ in 0..<n {
    s = s * 6364136223846793005L + 1442695040888963407L
    a.push(b7_cx(((s >> 33).to_int() % 200).to_double() / 100.0 - 1.0, 0.0))
  }
  let x = b7_dft(a, false)
  let y = b7_fft(a, false)
  let mut err = 0.0
  for i in 0..<n {
    let d = b7_cx_add(x[i], b7_cx(-y[i].re, -y[i].im))
    err = err + b7_cx_norm2(d)
  }
  err.sqrt() < 1.0e-9
}

///|
/// n₁×n₂ 零複矩陣。
pub fn b7_cmat_zeros(n1 : Int32, n2 : Int32) -> Array[Array[Cx7]] {
  let m : Array[Array[Cx7]] = []
  for _ in 0..<n1 {
    let row : Array[Cx7] = []
    for _ in 0..<n2 {
      row.push(b7_cx(0.0, 0.0))
    }
    m.push(row)
  }
  m
}

///|
/// 「葉變換」：對第 3 模做 DFT，得到 n₃ 個 n₁×n₂ 複數切片。
pub fn b7_leaf_transform(t : T3, fast : Bool) -> Array[Array[Array[Cx7]]] {
  let slices : Array[Array[Array[Cx7]]] = []
  for _ in 0..<t.n3 {
    slices.push(b7_cmat_zeros(t.n1, t.n2))
  }
  for i in 0..<t.n1 {
    for j in 0..<t.n2 {
      let tube : Array[Cx7] = []
      for k in 0..<t.n3 {
        tube.push(b7_cx(b7_ten3_get(t, i, j, k), 0.0))
      }
      let spec = if fast { b7_fft(tube, false) } else { b7_dft(tube, false) }
      for f in 0..<t.n3 {
        slices[f][i][j] = spec[f]
      }
    }
  }
  slices
}

///|
/// 由頻域切片逆葉變換回實張量。
pub fn b7_leaf_inverse(
  slices : Array[Array[Array[Cx7]]],
  n1 : Int32,
  n2 : Int32,
  n3 : Int32,
) -> T3 {
  let out = b7_t3_new(n1, n2, n3)
  for i in 0..<n1 {
    for j in 0..<n2 {
      let spec : Array[Cx7] = []
      for f in 0..<n3 {
        spec.push(slices[f][i][j])
      }
      let tube = b7_dft(spec, true)
      for k in 0..<n3 {
        b7_ten3_set(out, i, j, k, tube[k].re)
      }
    }
  }
  out
}

// ───────────────────────── t-product ─────────────────────────

///|
/// 逐頻率矩陣乘法：Ĉ_f = Â_f · B̂_f（皆為 n₁×n₂ 與 n₂×n₃ 的複矩陣）。
fn b7_freq_matmul(
  a : Array[Array[Cx7]],
  b : Array[Array[Cx7]],
) -> Array[Array[Cx7]] {
  let n1 = a.length()
  let n2 = b.length()
  let n3 = b[0].length()
  let c : Array[Array[Cx7]] = []
  for i in 0..<n1 {
    let row : Array[Cx7] = []
    for j in 0..<n3 {
      let mut acc = b7_cx(0.0, 0.0)
      for m in 0..<n2 {
        acc = b7_cx_add(acc, b7_cx_mul(a[i][m], b[m][j]))
      }
      row.push(acc)
    }
    c.push(row)
  }
  c
}

///|
/// 譜（快葉）t-product。
pub fn b7_tprod_spectral(a : T3, b : T3) -> T3 {
  let sa = b7_leaf_transform(a, true)
  let sb = b7_leaf_transform(b, true)
  let cs : Array[Array[Array[Cx7]]] = []
  for f in 0..<a.n3 {
    cs.push(b7_freq_matmul(sa[f], sb[f]))
  }
  b7_leaf_inverse(cs, a.n1, b.n2, a.n3)
}

///|
/// 直接定義的 t-product（管方向循環卷積），O(n₃²) 逐項求和。
pub fn b7_tprod_direct(a : T3, b : T3) -> T3 {
  let out = b7_t3_new(a.n1, b.n2, a.n3)
  for i in 0..<a.n1 {
    for j in 0..<b.n2 {
      for k in 0..<a.n3 {
        let mut acc = 0.0
        for m in 0..<a.n2 {
          for l in 0..<a.n3 {
            let kk = (k - l + a.n3) % a.n3
            acc = acc + b7_ten3_get(a, i, m, l) * b7_ten3_get(b, m, j, kk)
          }
        }
        b7_ten3_set(out, i, j, k, acc)
      }
    }
  }
  out
}

///|
/// t-product 的單位張量：第一正面切片 = I_n，其餘為 0。
pub fn b7_ten3_identity(n : Int32, n3 : Int32) -> T3 {
  let t = b7_t3_new(n, n, n3)
  for i in 0..<n {
    b7_ten3_set(t, i, i, 0, 1.0)
  }
  t
}
// ───────────────────────── 射影不變性 ─────────────────────────

///|
/// 在頻域乘上相位 λ_f（|λ_f| = 1）後逆變換 —— 「葉扭轉」。
pub fn b7_ten3_phase_twist(
  t : T3,
  phases : Array[Double],
  conjugate : Bool,
) -> T3 {
  let s = b7_leaf_transform(t, false)
  for f in 0..<t.n3 {
    let lam = b7_cx_phase(if conjugate { -phases[f] } else { phases[f] })
    for i in 0..<t.n1 {
      for j in 0..<t.n2 {
        s[f][i][j] = b7_cx_mul(s[f][i][j], lam)
      }
    }
  }
  b7_leaf_inverse(s, t.n1, t.n2, t.n3)
}

///|
/// 射影 t-product 的不變性：對任意 Hermitian 對稱相位 λ（λ_{n₃−f} = λ̄_f），
///   (λ⊙A) * (λ̄⊙B) = A * B
/// 回傳 (是否在 1e-9 內相等, 最大偏差)。
pub fn b7_projective_invariance_check(seed : Int64) -> (Bool, Double) {
  let a = b7_ten3_rand(2, 2, 4, seed)
  let b = b7_ten3_rand(2, 2, 4, seed + 7L)
  let c0 = b7_tprod_spectral(a, b)
  // 相位必須 Hermitian 對稱：λ_{n₃−f} = λ̄_f（否則逆變換不落在實張量內）
  let phases = [0.0, 0.7, 0.0, -0.7]
  let a2 = b7_ten3_phase_twist(a, phases, false)
  let b2 = b7_ten3_phase_twist(b, phases, true)
  let c1 = b7_tprod_spectral(a2, b2)
  let err = b7_ten3_dist(c0, c1)
  (err < 1.0e-9, err)
}

// ───────────────────────── 複 Hermitian 特徵分解（冪迭代 + 消去） ─────────────────────────

///|
/// Hermitian（此處僅需 PSD）矩陣的前 k 個特徵對，以冪迭代 + 收縮求得。
/// 回傳 (特徵值陣列（遞減）, 特徵向量矩陣（行向量）)。
pub fn b7_psd_eigen(
  a : Array[Array[Cx7]],
  k : Int32,
  iters : Int32,
) -> (Array[Double], Array[Array[Cx7]]) {
  let n = a.length()
  // 工作矩陣
  let w : Array[Array[Cx7]] = []
  for i in 0..<n {
    let row : Array[Cx7] = []
    for j in 0..<n {
      row.push(a[i][j])
    }
    w.push(row)
  }
  let vals : Array[Double] = []
  let vecs : Array[Array[Cx7]] = []
  for _ in 0..<k {
    // 初始向量
    let v : Array[Cx7] = []
    for i in 0..<n {
      v.push(b7_cx(1.0 + i.to_double() * 0.13, 0.37 - i.to_double() * 0.11))
    }
    // 對已收縮向量正交化
    for u in vecs {
      let mut proj = b7_cx(0.0, 0.0)
      for i in 0..<n {
        proj = b7_cx_add(proj, b7_cx_mul(b7_cx_conj(u[i]), v[i]))
      }
      for i in 0..<n {
        v[i] = b7_cx_add(
          v[i],
          b7_cx(-b7_cx_mul(proj, u[i]).re, -b7_cx_mul(proj, u[i]).im),
        )
      }
    }
    for _ in 0..<iters {
      let nv : Array[Cx7] = []
      for i in 0..<n {
        let mut acc = b7_cx(0.0, 0.0)
        for j in 0..<n {
          acc = b7_cx_add(acc, b7_cx_mul(w[i][j], v[j]))
        }
        nv.push(acc)
      }
      let mut nn = 0.0
      for z in nv {
        nn = nn + b7_cx_norm2(z)
      }
      nn = nn.sqrt()
      if nn < 1.0e-300 {
        break
      }
      for i in 0..<n {
        v[i] = b7_cx(nv[i].re / nn, nv[i].im / nn)
      }
    }
    // Rayleigh 商
    let mut num = b7_cx(0.0, 0.0)
    for i in 0..<n {
      let mut acc = b7_cx(0.0, 0.0)
      for j in 0..<n {
        acc = b7_cx_add(acc, b7_cx_mul(w[i][j], v[j]))
      }
      num = b7_cx_add(num, b7_cx_mul(b7_cx_conj(v[i]), acc))
    }
    let lam = num.re
    vals.push(lam)
    vecs.push(v)
    // 收縮
    for i in 0..<n {
      for j in 0..<n {
        w[i][j] = b7_cx_add(
          w[i][j],
          b7_cx(-lam * v[i].re * v[j].re - lam * v[i].im * v[j].im, 0.0),
        )
        // −λ v vᴴ 的虛部：−(λ (v_i conj(v_j))) 的虛部
        let vij = b7_cx_mul(v[i], b7_cx_conj(v[j]))
        w[i][j] = b7_cx(w[i][j].re, w[i][j].im - lam * vij.im)
      }
    }
  }
  (vals, vecs)
}

///|
/// 複矩陣乘法。
fn b7_cmat_mul(
  a : Array[Array[Cx7]],
  b : Array[Array[Cx7]],
) -> Array[Array[Cx7]] {
  let n = a.length()
  let m = b.length()
  let p = b[0].length()
  let c : Array[Array[Cx7]] = []
  for i in 0..<n {
    let row : Array[Cx7] = []
    for j in 0..<p {
      let mut acc = b7_cx(0.0, 0.0)
      for t in 0..<m {
        acc = b7_cx_add(acc, b7_cx_mul(a[i][t], b[t][j]))
      }
      row.push(acc)
    }
    c.push(row)
  }
  c
}

///|
/// 共軛轉置。
fn b7_cmat_h(a : Array[Array[Cx7]]) -> Array[Array[Cx7]] {
  let n = a.length()
  let m = a[0].length()
  let c : Array[Array[Cx7]] = []
  for j in 0..<m {
    let row : Array[Cx7] = []
    for i in 0..<n {
      row.push(b7_cx_conj(a[i][j]))
    }
    c.push(row)
  }
  c
}

///|
/// 單一切片的奇異值分解（thin SVD）：A = U Σ Vᴴ。
/// 以 AᴴA 的 PSD 特徵分解實現。回傳 (U, σ, V)。
pub fn b7_csvd(
  a : Array[Array[Cx7]],
) -> (Array[Array[Cx7]], Array[Double], Array[Array[Cx7]]) {
  let n1 = a.length()
  let n2 = a[0].length()
  let ah = b7_cmat_h(a)
  let aha = b7_cmat_mul(ah, a)
  let r = if n1 < n2 { n1 } else { n2 }
  let (vals, vcols) = b7_psd_eigen(aha, r, 300)
  // 排序（遞減）
  let idx : Array[Int32] = []
  for i in 0..<r {
    idx.push(i)
  }
  for i in 0..<r {
    let mut j = i + 1
    while j < r {
      if vals[idx[j]] > vals[idx[i]] {
        let t = idx[i]
        idx[i] = idx[j]
        idx[j] = t
      }
      j = j + 1
    }
  }
  let sigma : Array[Double] = []
  let v : Array[Array[Cx7]] = []
  for i in 0..<r {
    let s = if vals[idx[i]] > 0.0 { vals[idx[i]].sqrt() } else { 0.0 }
    sigma.push(s)
    v.push(vcols[idx[i]])
  }
  // V 為 n₂×r（行 = 右奇異向量）
  let vm : Array[Array[Cx7]] = []
  for i in 0..<n2 {
    let row : Array[Cx7] = []
    for j in 0..<r {
      row.push(v[j][i])
    }
    vm.push(row)
  }
  // U = A V Σ⁻¹
  let av = b7_cmat_mul(a, vm)
  let um : Array[Array[Cx7]] = []
  for i in 0..<n1 {
    let row : Array[Cx7] = []
    for j in 0..<r {
      let s = sigma[j]
      if s > 1.0e-12 {
        row.push(b7_cx(av[i][j].re / s, av[i][j].im / s))
      } else {
        row.push(b7_cx(0.0, 0.0))
      }
    }
    um.push(row)
  }
  (um, sigma, vm)
}

///|
/// 單一切片的重建誤差 ||A − UΣVᴴ||_F。
pub fn b7_csvd_check(a : Array[Array[Cx7]]) -> Double {
  let (u, s, v) = b7_csvd(a)
  let n1 = a.length()
  let n2 = a[0].length()
  let r = s.length()
  let mut err = 0.0
  for i in 0..<n1 {
    for j in 0..<n2 {
      let mut acc = b7_cx(0.0, 0.0)
      for t in 0..<r {
        acc = b7_cx_add(
          acc,
          b7_cx_mul(
            b7_cx(u[i][t].re * s[t], u[i][t].im * s[t]),
            b7_cx_conj(v[j][t]),
          ),
        )
      }
      let d = b7_cx_add(a[i][j], b7_cx(-acc.re, -acc.im))
      err = err + b7_cx_norm2(d)
    }
  }
  err.sqrt()
}

// ───────────────────────── t-SVD、核範數、Eckart–Young ─────────────────────────

///|
/// t-SVD 的奇異值表：σ(f, j)，f = 頻率、j = 奇異值序。回傳 (σ 表, 頻域奇異向量)。
pub fn b7_t_svd_sigmas(t : T3) -> Array[Array[Double]] {
  let s = b7_leaf_transform(t, true)
  let out : Array[Array[Double]] = []
  for f in 0..<t.n3 {
    let (_, sig, _) = b7_csvd(s[f])
    out.push(sig)
  }
  out
}

///|
/// 張量核範數（t-SVD 版）：TNN(A) = (1/n₃) Σ_f Σ_j σ_j(Â_f)。
pub fn b7_tnn(t : T3) -> Double {
  let sig = b7_t_svd_sigmas(t)
  let mut s = 0.0
  for f in 0..<t.n3 {
    for v in sig[f] {
      s = s + v
    }
  }
  s / t.n3.to_double()
}

///|
/// 秩 r 截斷的殘差範數：既用 Eckart–Young 公式 (1/n₃)Σ_f Σ_{j>r}σ_j² 預測，
/// 也用實際截斷 t-SVD 重建後量測，並回傳 (公式值, 實測值)。
pub fn b7_rank_r_error(t : T3, r : Int32) -> (Double, Double) {
  let s = b7_leaf_transform(t, true)
  let n1 = t.n1
  let n2 = t.n2
  let mut formula = 0.0
  for f in 0..<t.n3 {
    let (_, sig, _) = b7_csvd(s[f])
    for j in 0..<sig.length() {
      if j >= r {
        formula = formula + sig[j] * sig[j]
      }
    }
  }
  formula = (formula / t.n3.to_double()).sqrt()
  // 實測：逐頻率截斷後逆變換
  let recon : Array[Array[Array[Cx7]]] = []
  for f in 0..<t.n3 {
    let (u, sig, v) = b7_csvd(s[f])
    let m : Array[Array[Cx7]] = []
    for i in 0..<n1 {
      let row : Array[Cx7] = []
      for j in 0..<n2 {
        let mut acc = b7_cx(0.0, 0.0)
        for k in 0..<r {
          if k < sig.length() {
            let uu = b7_cx(u[i][k].re * sig[k], u[i][k].im * sig[k])
            acc = b7_cx_add(acc, b7_cx_mul(uu, b7_cx_conj(v[j][k])))
          }
        }
        row.push(acc)
      }
      m.push(row)
    }
    recon.push(m)
  }
  let tr = b7_leaf_inverse(recon, n1, n2, t.n3)
  (formula, b7_ten3_dist(t, tr))
}

///|
/// Parseval 恆等式：||A||_F² = (1/n₃) Σ_f ||Â_f||_F²。
pub fn b7_parseval_error(t : T3) -> Double {
  let s = b7_leaf_transform(t, true)
  let mut acc = 0.0
  for f in 0..<t.n3 {
    for i in 0..<t.n1 {
      for j in 0..<t.n2 {
        acc = acc + b7_cx_norm2(s[f][i][j])
      }
    }
  }
  acc = acc / t.n3.to_double()
  let l2 = b7_ten3_frob(t)
  (acc - l2 * l2).abs()
}

///|
/// 快葉與直算的運算量比：naive DFT = n² 複乘、FFT = (n/2)·log₂n 蝶形。
/// 回傳 (naive 次數, fft 次數, 比值)。
pub fn b7_leaf_cost_ratio(n3 : Int32) -> (Int32, Int32, Double) {
  let naive = n3 * n3
  let bits = b7_log2i(n3)
  let fast = n3 / 2 * bits
  (naive, fast, naive.to_double() / fast.to_double())
}

///|
/// 由外積 u ∘ v ∘ w 建構秩 1 張量（管方向為 w）。
pub fn b7_tensor_rank1(
  u : Array[Double],
  v : Array[Double],
  w : Array[Double],
) -> T3 {
  let t = b7_t3_new(u.length(), v.length(), w.length())
  for i in 0..<u.length() {
    for j in 0..<v.length() {
      for k in 0..<w.length() {
        b7_ten3_set(t, i, j, k, u[i] * v[j] * w[k])
      }
    }
  }
  t
}

///|
/// 主導葉（dominant leaf）：使 Σ_j σ_j(Â_f) 最大的頻率 f。
/// 這是「快葉」分解下的譜峰定位演算法。
pub fn b7_dominant_leaf(t : T3) -> Int32 {
  let sig = b7_t_svd_sigmas(t)
  let mut best = 0
  let mut bestv = -1.0
  for f in 0..<t.n3 {
    let mut acc = 0.0
    for v in sig[f] {
      acc = acc + v
    }
    if acc > bestv {
      bestv = acc
      best = f
    }
  }
  best
}
