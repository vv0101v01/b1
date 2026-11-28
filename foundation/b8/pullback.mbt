///|
/// pullback.mbt — 批次八·模組 2：拉回函子沿函子合成
///
/// 給有限範疇之間的函子 u : C → D，預層的**拉回**（pullback / 前推的反向）
///   u* : PSh(D) → PSh(C),  (u* X)(c) = X(u c),  (u* X)(m) = X(u m)
/// 滿足嚴格等式 (v∘u)* = u* ∘ v*（不是「差一個自然同構」，而是逐元素相等）。
///
/// 拉回 u* 的左伴隨是左 Kan 擴張 u_!，右伴隨是右 Kan 擴張 u_*；
/// 本模組以**餘端（coend）的顯式商集**實現 u_!：
///   (u_! X)(d) = colim_{(c, φ : u c → d)} X(c) = (⊔_{c,φ} X(c)) / ∼,
/// 其中 (c, φ, x) ∼ (c', φ', x') ⟺ ∃ψ: c → c'，X(ψ)(x') = x 且 φ' ∘ u(ψ) = φ。
/// 以併查集（union-find）求等價閉包，於是把伴隨關係變成可數的等式：
///   |Nat(u_! X, Y)| = |Nat(X, u* Y)|        （u_! ⊣ u*）
/// 以及複合律 (v∘u)_! X ≅ v_! (u_! X)。

// ───────────────────────── 範疇間的函子 ─────────────────────────

///|
/// 有限範疇之間的函子：物件映射 + 態射映射。
pub(all) struct B8Fun {
  src : B8Cat
  dst : B8Cat
  onobj : Array[Int32]
  onmor : Array[Int32]
}

///|
/// 建構函子。
pub fn b8_fun(
  src : B8Cat,
  dst : B8Cat,
  onobj : Array[Int32],
  onmor : Array[Int32],
) -> B8Fun {
  { src, dst, onobj, onmor, }
}

///|
/// 函子公理：保 dom/cod、保恆等、保合成。
pub fn b8_fun_ok(f : B8Fun) -> Bool {
  let c = f.src
  let d = f.dst
  for a in 0..<c.nob {
    if f.onmor[c.idm[a]] != d.idm[f.onobj[a]] {
      return false
    }
  }
  for m in 0..<c.nmor {
    if d.dom[f.onmor[m]] != f.onobj[c.dom[m]] ||
      d.cod[f.onmor[m]] != f.onobj[c.cod[m]] {
      return false
    }
  }
  for g in 0..<c.nmor {
    for h in 0..<c.nmor {
      if c.cod[h] == c.dom[g] {
        let lhs = f.onmor[c.cmp[g * c.nmor + h]]
        let rhs = d.cmp[f.onmor[g] * d.nmor + f.onmor[h]]
        if lhs != rhs {
          return false
        }
      }
    }
  }
  true
}

///|
/// 恆等函子。
pub fn b8_fun_id(c : B8Cat) -> B8Fun {
  let onobj : Array[Int32] = []
  let onmor : Array[Int32] = []
  for a in 0..<c.nob {
    onobj.push(a)
  }
  for m in 0..<c.nmor {
    onmor.push(m)
  }
  b8_fun(c, c, onobj, onmor)
}

///|
/// 合成 g ∘ f（f : A → B，g : B → C）。
pub fn b8_fun_comp(g : B8Fun, f : B8Fun) -> B8Fun {
  let onobj : Array[Int32] = []
  for a in 0..<f.src.nob {
    onobj.push(g.onobj[f.onobj[a]])
  }
  let onmor : Array[Int32] = []
  for m in 0..<f.src.nmor {
    onmor.push(g.onmor[f.onmor[m]])
  }
  b8_fun(f.src, g.dst, onobj, onmor)
}

///|
/// 預層的行距（與 catcore 的 b8_ps_make 一致）。
fn b8f_st(sz : Array[Int32]) -> Int32 {
  b8_ps_st(sz)
}

// ───────────────────────── 拉回 ─────────────────────────

///|
/// 拉回預層 u* X：(u* X)(c) = X(u c)。
pub fn b8_pull(u : B8Fun, x : B8PS) -> B8PS {
  let c = u.src
  let sz : Array[Int32] = []
  for a in 0..<c.nob {
    sz.push(x.sz[u.onobj[a]])
  }
  let st = b8f_st(sz)
  let res : Array[Int32] = []
  for _ in 0..<(c.nmor * st) {
    res.push(0)
  }
  for m in 0..<c.nmor {
    let b = c.cod[m]
    let um = u.onmor[m]
    for j in 0..<sz[b] {
      res[m * st + j] = x.res[um * x.mx + j]
    }
  }
  b8_ps_make(c, sz, res)
}

///|
/// 兩個同範疇預層的逐元素相等（忽略行距填充）。
pub fn b8_ps_eq(p : B8PS, q : B8PS) -> Bool {
  if p.cat.nob != q.cat.nob || p.cat.nmor != q.cat.nmor {
    return false
  }
  for c in 0..<p.cat.nob {
    if p.sz[c] != q.sz[c] {
      return false
    }
  }
  for m in 0..<p.cat.nmor {
    let b = p.cat.cod[m]
    for j in 0..<p.sz[b] {
      if p.res[m * p.mx + j] != q.res[m * q.mx + j] {
        return false
      }
    }
  }
  true
}

///|
/// 定理：拉回沿函子合成是嚴格的（(v∘u)* = u* ∘ v*）。
pub fn b8_pull_comp_check(u : B8Fun, v : B8Fun, x : B8PS) -> Bool {
  let lhs = b8_pull(b8_fun_comp(v, u), x)
  let rhs = b8_pull(u, b8_pull(v, x))
  b8_ps_eq(lhs, rhs)
}

// ───────────────────────── 左 Kan 擴張（餘端商集） ─────────────────────────

///|
/// 併查集的 find（含路徑壓縮）。
fn b8_uf_find(par : Array[Int32], i : Int32) -> Int32 {
  let mut r = i
  while par[r] != r {
    r = par[r]
  }
  let mut k = i
  while par[k] != k {
    let nxt = par[k]
    par[k] = r
    k = nxt
  }
  r
}

///|
/// 併查集的 union。
fn b8_uf_union(
  par : Array[Int32],
  rank : Array[Int32],
  i : Int32,
  j : Int32,
) -> Unit {
  let mut ri = b8_uf_find(par, i)
  let mut rj = b8_uf_find(par, j)
  if ri == rj {
    return
  }
  if rank[ri] < rank[rj] {
    let t = ri
    ri = rj
    rj = t
  }
  par[rj] = ri
  if rank[ri] == rank[rj] {
    rank[ri] = rank[ri] + 1
  }
}

///|
/// 左 Kan 擴張 u_! X（預層情形）：
///   (u_! X)(d) = ∫^{c} Hom_D(d, u c) × X(c) = colim_{(c, φ : d → u c)} X(c)
/// 元素為 (c, φ : d → u c, x ∈ X(c))，關係為
///   (c', φ', x') ∼ (c, φ, x)  ⟺  ∃ψ : c → c'，φ' = uψ ∘ φ 且 X(ψ)(x') = x。
/// 以併查集在「全部元素」上求等價閉包，再於每個 d 上把類編號。
pub fn b8_lan(u : B8Fun, x : B8PS) -> B8PS {
  let c = u.src
  let d = u.dst
  let elC : Array[Int32] = []
  let elPhi : Array[Int32] = []
  let elX : Array[Int32] = []
  let elD : Array[Int32] = []
  let start : Array[Int32] = []
  for dd in 0..<d.nob {
    start.push(elC.length())
    for cc in 0..<c.nob {
      let ud = u.onobj[cc]
      for phi in 0..<d.nmor {
        if d.dom[phi] == dd && d.cod[phi] == ud {
          for v in 0..<x.sz[cc] {
            elC.push(cc)
            elPhi.push(phi)
            elX.push(v)
            elD.push(dd)
          }
        }
      }
    }
  }
  start.push(elC.length())
  let n_el = elC.length()
  let par : Array[Int32] = []
  let rank : Array[Int32] = []
  for i in 0..<n_el {
    par.push(i)
    rank.push(0)
  }
  let rel = fn(i : Int32, j : Int32) -> Bool {
    if elD[i] != elD[j] {
      return false
    }
    let ci = elC[i]
    let cj = elC[j]
    let mut hit = false
    // ψ : ci → cj：x_i = X(ψ)(x_j) 且 φ_j = uψ ∘ φ_i
    for psi in 0..<c.nmor {
      if c.dom[psi] == ci && c.cod[psi] == cj {
        if x.res[psi * x.mx + elX[j]] == elX[i] &&
          d.cmp[u.onmor[psi] * d.nmor + elPhi[i]] == elPhi[j] {
          hit = true
        }
      }
      if c.dom[psi] == cj && c.cod[psi] == ci {
        if x.res[psi * x.mx + elX[i]] == elX[j] &&
          d.cmp[u.onmor[psi] * d.nmor + elPhi[j]] == elPhi[i] {
          hit = true
        }
      }
    }
    hit
  }

  for i in 0..<n_el {
    for j in (i + 1)..<n_el {
      if rel(i, j) {
        b8_uf_union(par, rank, i, j)
      }
    }
  }
  let clsOf : Array[Int32] = []
  for _ in 0..<n_el {
    clsOf.push(-1)
  }
  let sz : Array[Int32] = []
  for dd in 0..<d.nob {
    let s0 = start[dd]
    let s1 = start[dd + 1]
    let mut n = 0
    for i in s0..<s1 {
      let r = b8_uf_find(par, i)
      let mut found = -1
      for k in s0..<i {
        if b8_uf_find(par, k) == r {
          found = clsOf[k]
        }
      }
      if found >= 0 {
        clsOf[i] = found
      } else {
        clsOf[i] = n
        n = n + 1
      }
    }
    sz.push(n)
  }
  let st = b8f_st(sz)
  let res : Array[Int32] = []
  for _ in 0..<(d.nmor * st) {
    res.push(0)
  }
  for m in 0..<d.nmor {
    let a = d.dom[m]
    let b = d.cod[m]
    for j in 0..<sz[b] {
      let mut rep = -1
      for i in start[b]..<start[b + 1] {
        if clsOf[i] == j && rep < 0 {
          rep = i
        }
      }
      if rep >= 0 {
        // 限制沿 m : a → b：φ ↦ φ ∘ m
        let phi2 = d.cmp[elPhi[rep] * d.nmor + m]
        let mut idx = -1
        for i in start[a]..<start[a + 1] {
          if elC[i] == elC[rep] && elPhi[i] == phi2 && elX[i] == elX[rep] {
            idx = clsOf[i]
          }
        }
        res[m * st + j] = if idx >= 0 { idx } else { 0 }
      }
    }
  }
  b8_ps_make(d, sz, res)
}

// ───────────────────────── 伴隨與複合律的計數核對 ─────────────────────────

///|
/// 伴隨計數：|Nat(u_! X, Y)| 與 |Nat(X, u* Y)|。
pub fn b8_lan_adj_counts(u : B8Fun, x : B8PS, y : B8PS) -> (Int32, Int32) {
  let lhs = b8_nat_count(b8_lan(u, x), y)
  let rhs = b8_nat_count(x, b8_pull(u, y))
  (lhs, rhs)
}

///|
/// 伴隨計數是否成立（對單一 (X, Y)）。
pub fn b8_lan_adj_ok(u : B8Fun, x : B8PS, y : B8PS) -> Bool {
  let (lhs, rhs) = b8_lan_adj_counts(u, x, y)
  lhs == rhs
}

///|
/// 複合律：(v∘u)_! X 與 v_!(u_! X) 的元素個數（逐物件）相等。
pub fn b8_lan_comp_sz(
  u : B8Fun,
  v : B8Fun,
  x : B8PS,
) -> (Array[Int32], Array[Int32]) {
  let lhs = b8_lan(b8_fun_comp(v, u), x)
  let rhs = b8_lan(v, b8_lan(u, x))
  (lhs.sz, rhs.sz)
}

///|
/// 複合律的伴隨檢驗：(v∘u)_! ⊣ (v∘u)* 與 v_! u_! ⊣ u* v* 給出相同的 Nat 數。
pub fn b8_lan_comp_adj(
  u : B8Fun,
  v : B8Fun,
  x : B8PS,
  w : B8PS,
) -> (Int32, Int32) {
  let lhs = b8_nat_count(b8_lan(b8_fun_comp(v, u), x), w)
  let rhs = b8_nat_count(b8_lan(u, x), b8_pull(v, w))
  (lhs, rhs)
}
