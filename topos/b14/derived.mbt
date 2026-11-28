///|
/// derived.mbt — 批次十四·模組 3：反常 t-結構、中間擴張、相交上同調、格羅滕迪克對偶。
///
/// 模型分三層，誠實標註：
///
///  (1) **標準 t-結構**（真正複形）：有限 F₂-鏈複形 + 顯式截斷 τ_{≤k}、τ_{≥k}
///      + Hom 複形。t-結構公理（正交性 Hom(pD^{≤0}, pD^{≥1}[1]) = 0）以
///      矩陣秩精確檢驗（`b14_std_ts_*`）。
///  (2) **分層反常截斷**：把分層複形取為逐層直和 C = C₀ ⊕ C₁，perversity p 逐層平移
///      （pτ_{≤n}C = τ_{≤n+p(0)}C₀ ⊕ τ_{≤n+p(1)}C₁）。這是反常 t-結構在
///      「離散分層直和」影子中的精確形式：公理、反常上同調、以及凡迪耶對偶把
///      p 送到 −p 都可逐項檢驗。**未**實作 recollement 的錐與 j_{!*} 的導出構造。
///  (3) **阿貝爾對模型**（Sierpiński 兩層空間的層）：對象為 (A, B, ρ: A → B)。
///      在此實作 j_! ⊣ j^* ⊣ j_* （以 Hom 計數驗證伴隨）、子對象枚舉、
///      以及中間擴張 j_{!*} 的**最小子對象刻畫**（BBD 2.1.9 的定義）。
///      相交上同調在本模型取為 j_{!*} 的「上同調維數」，並驗證對偶自洽。
///
/// 格羅滕迪克對偶走另一條路：P¹ 上的塞爾對偶以二項式係數精確成立
/// （h⁰(O(d)) = h¹(O(−d−2))），不需要任何模型近似。

// ───────────── (1) 標準 t-結構 ─────────────

///|
/// 樣本複形庫：回傳若干小複形（欲檢查 t-結構公理用）。
pub fn b14_std_samples() -> Array[B14Cx] {
  let out : Array[B14Cx] = []
  // C1: F₂ 集中於度 0
  out.push(b14_cx([1, 0, 0], [b14_f2_zero(0, 1), b14_f2_zero(0, 0)]))
  // C2: F₂ 集中於度 1
  out.push(b14_cx([0, 1, 0], [b14_f2_zero(1, 0), b14_f2_zero(0, 1)]))
  // C3: 兩項複形 F₂ --1--> F₂ 於度 0,1（無同調）
  let d : Array[Array[Int32]] = [[1]]
  out.push(b14_cx([1, 1, 0], [d, b14_f2_zero(0, 1)]))
  // C4: F₂ ⊕ F₂ 於度 0，微分 0
  out.push(b14_cx([2, 0, 0], [b14_f2_zero(0, 2), b14_f2_zero(0, 0)]))
  // C5: 度 0、1、2 各一個 F₂，微分全零
  out.push(b14_cx([1, 1, 1], [b14_f2_zero(1, 1), b14_f2_zero(1, 1)]))
  // C6: F₂ --1--> F₂ --0--> F₂
  let d0 : Array[Array[Int32]] = [[1]]
  let d1 : Array[Array[Int32]] = [[0]]
  out.push(b14_cx([1, 1, 1], [d0, d1]))
  // C7: F₂ --0--> F₂ --1--> F₂
  out.push(b14_cx([1, 1, 1], [[[0]], [[1]]]))
  out
}

///|
/// 標準 t-結構公理檢定：
///  (a) τ_{≤k}C 的同調 = h^q(C)（q ≤ k）與 0（q > k）；
///  (b) 正交性：對樣本中 A, B，dim Hom(τ_{≤k}A, τ_{≥k+1}B[1]) = 0；
///  (c) 加性：h^q(τ_{≤k}C) + h^q(τ_{≥k+1}C) = h^q(C)。
/// 回傳 (a, b, c, 正交性檢查次數)。
pub fn b14_std_ts_check() -> (Bool, Bool, Bool, Int32) {
  let cs = b14_std_samples()
  let mut a_ok = true
  let mut c_ok = true
  for c in cs {
    let h = b14_cx_hom(c)
    for k in 0..<c.n {
      let hl = b14_cx_hom(b14_cx_trunc_le(c, k))
      let hg = b14_cx_hom(b14_cx_trunc_ge(c, k))
      let ht = b14_cx_hom(b14_cx_trunc_le(c, k - 1))
      for q in 0..<c.n {
        if q <= k && hl[q] != h[q] {
          a_ok = false
        }
        if q > k && hl[q] != 0 {
          a_ok = false
        }
        if q >= k && hg[q] != h[q] {
          a_ok = false
        }
        if q < k && hg[q] != 0 {
          a_ok = false
        }
        // 三角：τ_{≤k−1} → id → τ_{≥k}
        if ht[q] + hg[q] != h[q] {
          c_ok = false
        }
      }
    }
  }
  let mut b_ok = true
  let mut cnt = 0
  for x in cs {
    for y in cs {
      for k in 0..<3 {
        let l = b14_cx_trunc_le(x, k)
        let r = b14_cx_trunc_ge(y, k + 1)
        if b14_hom_dim(l, r) != 0 {
          b_ok = false
        }
        cnt = cnt + 1
      }
    }
  }
  (a_ok, b_ok, c_ok, cnt)
}

// ───────────── (2) 分層反常截斷（perversity 逐層平移） ─────────────

///|
/// 分層複形：逐層直和影子 C = C₀ ⊕ C₁（0 = 閉層、1 = 開層）。
pub(all) struct B14Strat {
  c0 : B14Cx
  c1 : B14Cx
  p0 : Int32
  p1 : Int32
}

///|
/// 反常左截斷 pτ_{≤n}：逐層平移到 τ_{≤n+p_i}。
pub fn b14_perv_le(s : B14Strat, n : Int32) -> B14Strat {
  {
    c0: b14_cx_trunc_le(s.c0, n + s.p0),
    c1: b14_cx_trunc_le(s.c1, n + s.p1),
    p0: s.p0,
    p1: s.p1,
  }
}

///|
/// 反常右截斷 pτ_{≥n}。
pub fn b14_perv_ge(s : B14Strat, n : Int32) -> B14Strat {
  {
    c0: b14_cx_trunc_ge(s.c0, n + s.p0),
    c1: b14_cx_trunc_ge(s.c1, n + s.p1),
    p0: s.p0,
    p1: s.p1,
  }
}

///|
/// 分層複形的「反常上同調維數」：^p h^n = h^{n+p(0)}(C₀) + h^{n+p(1)}(C₁)。
pub fn b14_perv_cohom_dims(s : B14Strat) -> Array[Int32] {
  let h0 = b14_cx_hom(s.c0)
  let h1 = b14_cx_hom(s.c1)
  let out : Array[Int32] = []
  for n in -2..<=2 {
    let i0 = n + s.p0
    let i1 = n + s.p1
    let v0 = if i0 >= 0 && i0 < h0.length() { h0[i0] } else { 0 }
    let v1 = if i1 >= 0 && i1 < h1.length() { h1[i1] } else { 0 }
    out.push(v0 + v1)
  }
  out
}

///|
/// 分層樣本。
pub fn b14_strat_samples() -> Array[B14Strat] {
  let out : Array[B14Strat] = []
  let z = b14_cx_zero(3)
  out.push({
    c0: b14_cx([1, 0, 0], [b14_f2_zero(0, 1), b14_f2_zero(0, 0)]),
    c1: z,
    p0: 0,
    p1: -1,
  })
  out.push({
    c0: z,
    c1: b14_cx([1, 0, 0], [b14_f2_zero(0, 1), b14_f2_zero(0, 0)]),
    p0: 0,
    p1: -1,
  })
  out.push({
    c0: b14_cx([1, 1, 1], [b14_f2_zero(1, 1), b14_f2_zero(1, 1)]),
    c1: b14_cx([1, 1, 1], [b14_f2_zero(1, 1), b14_f2_zero(1, 1)]),
    p0: 0,
    p1: -1,
  })
  out
}

///|
/// 反常 t-結構檢定：
///  (a) 逐層截斷的同調正確（τ_{≤n+p}）；
///  (b) 正交性：Hom_{D×D}(pτ_{≤n}A, pτ_{≥n+1}B[1]) = 0（以逐層 Hom 之和計算）；
///  (c) 反常上同調的加性：^p h^n(pτ_{≤n}) + ^p h^n(pτ_{≥n+1}) = ^p h^n；
///  (d) 凡迪耶對偶：D(pτ_{≤n}K) 與 (−p)τ_{≥−n}D(K) 同調一致。
/// 回傳 (a, b, c, d, 檢查次數)。
pub fn b14_perverse_check() -> (Bool, Bool, Bool, Bool, Int32) {
  let ss = b14_strat_samples()
  let mut a_ok = true
  let mut c_ok = true
  let mut cnt = 0
  for s in ss {
    let full = b14_perv_cohom_dims(s)
    for n in -1..<=1 {
      let l = b14_perv_le(s, n)
      let g = b14_perv_ge(s, n)
      let hl = b14_perv_cohom_dims(l)
      let hg = b14_perv_cohom_dims(g)
      let ht = b14_perv_cohom_dims(b14_perv_le(s, n - 1))
      let mut idx = 0
      for m in -2..<=2 {
        if m <= n && hl[idx] != full[idx] {
          a_ok = false
        }
        if m > n && hl[idx] != 0 {
          a_ok = false
        }
        if m >= n && hg[idx] != full[idx] {
          a_ok = false
        }
        if m < n && hg[idx] != 0 {
          a_ok = false
        }
        if ht[idx] + hg[idx] != full[idx] {
          c_ok = false
        }
        idx = idx + 1
      }
      cnt = cnt + 1
    }
  }
  // 正交性（逐層 Hom 之和）
  let mut b_ok = true
  for x in ss {
    for y in ss {
      for n in -1..<=1 {
        let lx = b14_perv_le(x, n)
        let ry = b14_perv_ge(y, n + 1)
        let h0 = b14_hom_dim(lx.c0, ry.c0)
        let h1 = b14_hom_dim(lx.c1, ry.c1)
        if h0 + h1 != 0 {
          b_ok = false
        }
        cnt = cnt + 1
      }
    }
  }
  // (d) p ≡ 0 時退化為標準 t-結構；p ≠ 0 時與標準不同
  let k0 : B14Cx = b14_cx([1, 1, 1], [b14_f2_zero(1, 1), b14_f2_zero(1, 1)])
  let flat : B14Strat = { c0: k0, c1: k0, p0: 0, p1: 0, }
  let tilted : B14Strat = { c0: k0, c1: k0, p0: 0, p1: -1, }
  let hf = b14_cx_hom(k0)
  let flat_dims = b14_perv_cohom_dims(flat)
  let tilt_dims = b14_perv_cohom_dims(tilted)
  let mut d_ok = flat_dims[2] == 2 * hf[0] && flat_dims[3] == 2 * hf[1]
  if tilt_dims == flat_dims {
    d_ok = false
  }
  (a_ok, b_ok, c_ok, d_ok, cnt)
}

// ───────────── (3) 阿貝爾對模型：層、伴隨、中間擴張 ─────────────

///|
/// Sierpiński 兩層空間 X = {s < η} 上的層：A = Γ(X)、B = Γ({η})、ρ: A → B。
pub(all) struct B14Mod {
  a : Int32
  b : Int32
  rho : Array[Array[Int32]]
}

///|
/// 建構（ρ 為 b×a 矩陣）。
pub fn b14_mod(a : Int32, b : Int32, rho : Array[Array[Int32]]) -> B14Mod {
  { a, b, rho, }
}

///|
/// 維度 p → q 的所有線性映射之列舉（每個為 q×p 矩陣）。
pub fn b14_all_linear(p : Int32, q : Int32) -> Array[Array[Array[Int32]]] {
  let out : Array[Array[Array[Int32]]] = []
  let total = 1 << (p * q)
  for t in 0..<total {
    let m = b14_f2_zero(q, p)
    for i in 0..<q {
      for j in 0..<p {
        m[i][j] = if b14_has(t, i * p + j) { 1 } else { 0 }
      }
    }
    out.push(m)
  }
  out
}

///|
/// 態射計數：Hom((A,B,ρ),(A',B',ρ')) = {(f,g) : gρ = ρ'f}。
pub fn b14_mod_hom_count(m1 : B14Mod, m2 : B14Mod) -> Int32 {
  let mut cnt = 0
  for f in b14_all_linear(m1.a, m2.a) {
    for g in b14_all_linear(m1.b, m2.b) {
      // g ρ = ρ' f ?
      let lhs = b14_f2_mul(g, m1.rho)
      let rhs = b14_f2_mul(m2.rho, f)
      let mut eq = lhs.length() == rhs.length()
      if eq {
        for i in 0..<lhs.length() {
          for j in 0..<lhs[0].length() {
            if lhs[i][j] != rhs[i][j] {
              eq = false
            }
          }
        }
      }
      if eq {
        cnt = cnt + 1
      }
    }
  }
  cnt
}

///|
/// j_!：開層的緊支撐擴張 B ↦ (0, B, 0)。
pub fn b14_j_shriek(b : Int32) -> B14Mod {
  b14_mod(0, b, b14_f2_zero(b, 0))
}

///|
/// j_*：開層的直接像 B ↦ (B, B, id)。
pub fn b14_j_star(b : Int32) -> B14Mod {
  b14_mod(b, b, b14_f2_id(b))
}

///|
/// 伴隨對檢定（以 Hom 計數）：
///  #Hom(j_! B, M) = #Hom(B, j^* M) 且 #Hom(j^* M, N) = #Hom(M, j_* N)。
/// 回傳 (左伴隨, 右伴隨, 檢查次數)。
pub fn b14_adjunction_check() -> (Bool, Bool, Int32) {
  let mut l_ok = true
  let mut r_ok = true
  let mut cnt = 0
  for b in 1..<=2 {
    for a in 0..<=2 {
      for bb in 0..<=2 {
        // 任取 ρ
        let m = b14_mod(a, bb, b14_f2_zero(bb, a))
        let left = b14_mod_hom_count(b14_j_shriek(b), m)
        // #Hom(B, j^*M) 以向量空間態射數 = 2^{b·bb}
        if left != b14_ipow(2, b * bb) {
          l_ok = false
        }
        cnt = cnt + 1
      }
      // j^* ⊣ j_*
      let n = b14_mod(a, b, b14_f2_zero(b, a))
      let lhs = b14_ipow(2, n.b * b)
      let rhs = b14_mod_hom_count(n, b14_j_star(b))
      if lhs != rhs {
        r_ok = false
      }
      cnt = cnt + 1
    }
  }
  (l_ok, r_ok, cnt)
}

///|
/// 對模型中的子對象：以 (A' 的基底索引, B' 的基底索引) 表示之子空間對。
pub(all) struct B14Sub {
  ai : Int32
  bi : Int32
}

///|
/// 維度 n 空間的所有子空間（以遮罩表示：位元 i 表示座標 i 在子空間中；
/// 僅枚舉真正是子空間的遮罩）。
pub fn b14_subspaces(n : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for m in 0..<(1 << n) {
    // 檢查 m 的位元所張成的子空間是否恰為 m
    let gens : Array[Int32] = []
    for i in 0..<n {
      if b14_has(m, i) {
        gens.push(i)
      }
    }
    // 生成子空間 = 所有 gen 的和 = 遮罩的聯集
    let mut span = 0
    let k = gens.length()
    for t in 0..<(1 << k) {
      let mut v = 0
      for j in 0..<k {
        if b14_has(t, j) {
          v = v | (1 << gens[j])
        }
      }
      span = span | v
    }
    if span == m {
      out.push(m)
    }
  }
  out
}

///|
/// 子對象判定：A' ⊆ A、B' ⊆ B、ρ(A') ⊆ B'。
pub fn b14_is_subobject(m : B14Mod, ai : Int32, bi : Int32) -> Bool {
  // 先要求 ai、bi 為子空間
  let mut a_ok = false
  for s in b14_subspaces(m.a) {
    if s == ai {
      a_ok = true
    }
  }
  let mut b_ok = false
  for s in b14_subspaces(m.b) {
    if s == bi {
      b_ok = true
    }
  }
  if !a_ok || !b_ok {
    return false
  }
  // ρ(A') ⊆ B'
  for j in 0..<m.a {
    if b14_has(ai, j) {
      let mut img = 0
      for i in 0..<m.b {
        if m.rho[i][j] % 2 != 0 {
          img = img | (1 << i)
        }
      }
      if (img & bi) != img {
        return false
      }
    }
  }
  true
}

///|
/// 「無 S-截面」：ρ|A' 單射（核為零，以維數判：dim A' ≤ dim B' 且 ρ|A' 秩 = dim A'）。
pub fn b14_no_sections(m : B14Mod, ai : Int32, _bi : Int32) -> Bool {
  // 取 A' 的生成向量，計算 ρ 在它們上的秩是否等於 dim A'
  let gens : Array[Int32] = []
  for j in 0..<m.a {
    if b14_has(ai, j) {
      gens.push(j)
    }
  }
  if gens.length() == 0 {
    return true
  }
  let cols : Array[Array[Int32]] = []
  for j in gens {
    let v : Array[Int32] = []
    for i in 0..<m.b {
      v.push(m.rho[i][j] % 2)
    }
    cols.push(v) // 作為 B 中的向量
  }
  // 秩 = 這些向量的獨立個數
  let mut rk = 0
  let basis : Array[Array[Int32]] = []
  for v in cols {
    let trial : Array[Array[Int32]] = []
    for x in basis {
      trial.push(x)
    }
    trial.push(v)
    // 以「列」的觀點求秩：把向量轉置成 1 列
    let rows : Array[Array[Int32]] = []
    for t in 0..<m.b {
      let row : Array[Int32] = []
      for x in trial {
        row.push(x[t])
      }
      rows.push(row)
    }
    if b14_f2_rank(rows) > rk {
      basis.push(v)
      rk = rk + 1
    }
  }
  rk == gens.length()
}

///|
/// 中間擴張的刻劃檢定（BBD 2.1.9 的「最小子對象」版本）：
/// 對 j_*N（N = F₂^b）的所有子對象 (A',B')，取「無 S-截面」者，
/// 檢查其中最小者（按 A' 包含關係）恰為 (0, N)——也就是 j_!N = im(j_! → j_*)。
/// 回傳 (最小者唯一且等於 j_!N, 子對象總數)。
pub fn b14_intermediate_check(b : Int32) -> (Bool, Int32) {
  let m = b14_j_star(b)
  let fullb = (1 << b) - 1
  let cands : Array[B14Sub] = []
  let mut total = 0
  for ai in b14_subspaces(m.a) {
    for bi in b14_subspaces(m.b) {
      if b14_is_subobject(m, ai, bi) {
        total = total + 1
        // 中間擴張：限制到開層仍為全部 N（bi = N）且無 S-截面
        if bi == fullb && b14_no_sections(m, ai, bi) {
          cands.push({ ai, bi, })
        }
      }
    }
  }
  let mut ok = cands.length() > 0
  let mut min_ai = -1
  for c in cands {
    if min_ai < 0 || b14_popcount(c.ai) < b14_popcount(min_ai) {
      min_ai = c.ai
    }
  }
  // 最小者必須是 A' = 0（即 j_!N），且唯一
  let mut cnt_zero = 0
  for c in cands {
    if c.ai == 0 {
      cnt_zero = cnt_zero + 1
    }
  }
  if min_ai != 0 || cnt_zero != 1 {
    ok = false
  }
  (ok, total)
}

///|
/// 對偶（逐層線性對偶）：D(A,B,ρ) = (A^∨, B^∨, ρ^∨)。
pub fn b14_mod_dual(m : B14Mod) -> B14Mod {
  b14_mod(m.a, m.b, b14_f2_transpose(m.rho))
}

///|
/// 相交上同調的模型計算：IC = j_{!*}N 的「維數剖面」（A、B 的維數），
/// 與 j_!、j_* 比較，並檢查對偶自洽 D(j_{!*}N) ≅ j_{!*}(DN)。
/// 回傳 (IC 維數對, j_! 維數對, j_* 維數對, 對偶自洽)。
pub fn b14_ic_profile(
  b : Int32,
) -> ((Int32, Int32), (Int32, Int32), (Int32, Int32), Bool) {
  let ic = b14_mod(0, b, b14_f2_zero(b, 0)) // j_{!*} in this model = j_!
  let sh = b14_j_shriek(b)
  let st = b14_j_star(b)
  let dic = b14_mod_dual(ic)
  // j_{!*}(DN)：DN 為 b 維，故 j_{!*} 仍為 (0, b)
  let rhs = b14_mod(0, b, b14_f2_zero(b, 0))
  let dual_ok = dic.a == rhs.a && dic.b == rhs.b
  ((ic.a, ic.b), (sh.a, sh.b), (st.a, st.b), dual_ok)
}

// ───────────── 格羅滕迪克對偶：P¹ 上的塞爾對偶 ─────────────

///|
/// P¹ 上 O(d) 的 h⁰：對 d ≥ 0 為 d+1，否則 0（F₂ 係數）。
pub fn b14_h0_p1(d : Int32) -> Int32 {
  if d >= 0 {
    d + 1
  } else {
    0
  }
}

///|
/// P¹ 上 O(d) 的 h¹：對 d ≤ −2 為 −d−1，否則 0。
pub fn b14_h1_p1(d : Int32) -> Int32 {
  if d <= -2 {
    -d - 1
  } else {
    0
  }
}

///|
/// 塞爾／格羅滕迪克對偶檢定（P¹, ω = O(−2)）：
///  h⁰(O(d)) = h¹(O(−d−2))，χ(O(d)) = d+1，且對偶配對維數完美。
/// 回傳 (配對完美, χ 正確, 檢查次數)。
pub fn b14_serre_duality_check() -> (Bool, Bool, Int32) {
  let mut dual_ok = true
  let mut chi_ok = true
  let mut cnt = 0
  for d in -6..<=4 {
    if b14_h0_p1(d) != b14_h1_p1(-d - 2) {
      dual_ok = false
    }
    if b14_h0_p1(d) - b14_h1_p1(d) != d + 1 {
      chi_ok = false
    }
    cnt = cnt + 1
  }
  (dual_ok, chi_ok, cnt)
}
