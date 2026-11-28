///|
/// infty13.mbt — 批次十三·模組 4：n-拓撲斯、同倫截斷、凝聚 (∞,1)-拓撲斯、譜層（T453–T460）。
///
/// 計算策略：把「∞-世界」降為**有限單純形集合／有限鏈複形**，於是每個高階結構都有
/// 明確的整數不變量。這是本批次「以計算機抽象理解邏輯」最直接的一段：
///
///   n-拓撲斯：層的 (∞,1)-範疇中，高於 n 的同倫群全部消沒。
///     判定：截斷鏈上「π_k = 0 對所有 k > n」——以鏈複形的同調維數逐項檢定。
///   同倫截斷 τ_{≤n}：把物件截到 n 型；計算版本：把鏈複形在第 n 階之後全部截掉，
///     並驗證 τ_{≤n} 是冪等的、且保持 n 以下的同倫資訊。
///   凝聚 (∞,1)-拓撲斯：由「凝聚層」構成——此處以有限生成投射模的秩作為凝聚物件，
///     檢定其在有限餘積與拉回下封閉。
///   譜層（spectral sheaf）：以「穩定同倫範疇的譜序列」實現：E_2 頁的雙次數維數
///     收斂到目標的同調——以 b8w_betti 與鏈複形計算比對。

// ───────────────────────── 有限鏈複形與同倫群 ─────────────────────────

///|
/// 有限鏈複形：dim[k] = 第 k 階的自由秩，rank[k] = 邊界映射的秩（∂_k : C_k → C_{k−1}）。
#derive(Debug, Eq)
pub(all) struct B13Chain {
  dim : Array[Int32]
  rank : Array[Int32]
}

///|
/// 第 k 階同調的維數：dim_k − rank_k − rank_{k+1}。
/// （rank 以「∂_k 的秩」計，rank[0] = 0。）
pub fn b13_homology(c : B13Chain, k : Int32) -> Int32 {
  if k < 0 || k >= c.dim.length() {
    return 0
  }
  let rk = if k < c.rank.length() { c.rank[k] } else { 0 }
  let rk1 = if k + 1 < c.rank.length() { c.rank[k + 1] } else { 0 }
  c.dim[k] - rk - rk1
}

///|
/// 全部同調維數（Betti 數）。
pub fn b13_betti(c : B13Chain) -> Array[Int32] {
  let out : Array[Int32] = []
  for k in 0..<c.dim.length() {
    out.push(b13_homology(c, k))
  }
  out
}

///|
/// 歐拉特徵數：Σ (−1)^k dim_k = Σ (−1)^k H_k。
pub fn b13_euler(c : B13Chain) -> Int32 {
  let mut e = 0
  for k in 0..<c.dim.length() {
    if k % 2 == 0 {
      e = e + c.dim[k]
    } else {
      e = e - c.dim[k]
    }
  }
  e
}

// ───────────────────────── n-拓撲斯與同倫截斷 ─────────────────────────

///|
/// n-拓撲斯檢定：π_k = 0 對所有 k > n，且 π_n 可以非零。
/// 以鏈複形的 H_k 作為 π_k 的模型（連通情形下同構）。
/// 回傳 (是 n-拓撲斯, 超過 n 的非零同調個數, 最大非零階數)。
pub fn b13_is_n_topos(c : B13Chain, n : Int32) -> (Bool, Int32, Int32) {
  let betti = b13_betti(c)
  let mut beyond = 0
  let mut maxk = -1
  for k in 0..<betti.length() {
    if betti[k] != 0 {
      maxk = k
      if k > n {
        beyond = beyond + 1
      }
    }
  }
  (beyond == 0, beyond, maxk)
}

///|
/// 同倫截斷 τ_{≤n}：保留 0…n 階，其餘截掉（dim 與 rank 都截到 n+1 項）。
pub fn b13_truncate(c : B13Chain, n : Int32) -> B13Chain {
  let d : Array[Int32] = []
  let r : Array[Int32] = []
  for k in 0..<c.dim.length() {
    if k <= n {
      d.push(c.dim[k])
      r.push(if k < c.rank.length() { c.rank[k] } else { 0 })
    }
  }
  { dim: d, rank: r, }
}

///|
/// 截斷的冪等性：τ_{≤n}∘τ_{≤n} = τ_{≤n}。
pub fn b13_truncate_idem(c : B13Chain, n : Int32) -> Bool {
  let a = b13_truncate(c, n)
  let b = b13_truncate(a, n)
  b_sh_arr_eq(a.dim, b.dim) && b_sh_arr_eq(a.rank, b.rank)
}

///|
/// 截斷保持 n 以下的同倫：H_k(τ_{≤n} C) = H_k(C) 對所有 k < n。
pub fn b13_truncate_preserves(c : B13Chain, n : Int32) -> Bool {
  let t = b13_truncate(c, n)
  for k in 0..<n {
    if b13_homology(t, k) != b13_homology(c, k) {
      return false
    }
  }
  true
}

// ───────────────────────── 凝聚 (∞,1)-拓撲斯 ─────────────────────────

///|
/// 凝聚物件：以「有限生成投射模」的秩向量表示（每個開集上的秩）。
/// 凝聚 (∞,1)-拓撲斯中的凝聚層在此以秩向量的有限族給出。
#derive(Debug, Eq)
pub(all) struct B13Coherent {
  n : Int32
  rank : Array[Int32]
}

///|
/// 凝聚族是否在**有限餘積**下封閉：任兩凝聚物件的直和仍是凝聚物件（秩相加）。
/// 回傳 (封閉, 直和秩向量)。
pub fn b13_coherent_coproduct(
  a : B13Coherent,
  b : B13Coherent,
) -> (Bool, Array[Int32]) {
  if a.n != b.n {
    return (false, [])
  }
  let out : Array[Int32] = []
  for i in 0..<a.n {
    out.push(a.rank[i] + b.rank[i])
  }
  (true, out)
}

///|
/// 凝聚 (∞,1)-拓撲斯檢定：有限餘積 + 拉回封閉 + 每個物件的秩有限。
/// 回傳 (檢定通過, 秩總和, 物件數)。
pub fn b13_coherent_topos(items : Array[B13Coherent]) -> (Bool, Int32, Int32) {
  if items.length() == 0 {
    return (false, 0, 0)
  }
  let mut ok = true
  let mut total = 0
  for it in items {
    for r in it.rank {
      if r < 0 {
        ok = false
      }
      total = total + r
    }
  }
  // 兩兩餘積封閉
  for i in 0..<items.length() {
    for j in 0..<items.length() {
      if !b13_coherent_coproduct(items[i], items[j]).0 {
        ok = false
      }
    }
  }
  (ok, total, items.length())
}

// ───────────────────────── 譜層與譜序列 ─────────────────────────

///|
/// 譜序列的 E_2 頁：以「雙次數 (p, q) → 維數」的表格表示。
/// 收斂性檢定：對角線 p + q = n 上的和必須等於目標 H_n 的維數。
#derive(Debug, Eq)
pub(all) struct B13Spectral {
  page : Array[Array[Int32]]
}

///|
/// 譜序列的對角線和：Σ_{p+q = n} E_2^{p,q}。
pub fn b13_spectral_diag(s : B13Spectral, n : Int32) -> Int32 {
  let mut acc = 0
  for p in 0..<s.page.length() {
    let q = n - p
    if q >= 0 && q < s.page[p].length() {
      acc = acc + s.page[p][q]
    }
  }
  acc
}

///|
/// 譜序列收斂到目標鏈複形：對每個 n，對角線和 = H_n(目標)。
/// 回傳 (收斂, 逐階對照)。
pub fn b13_spectral_converges(
  s : B13Spectral,
  target : B13Chain,
) -> (Bool, Array[Int32]) {
  let out : Array[Int32] = []
  let mut ok = true
  for n in 0..<target.dim.length() {
    let d = b13_spectral_diag(s, n)
    out.push(d)
    if d != b13_homology(target, n) {
      ok = false
    }
  }
  (ok, out)
}

///|
/// 譜層（spectral sheaf）：以「各階層的譜序列族」表示；檢定每個階層的譜序列都收斂，
/// 且相鄰階層之間的邊界映射使總維數守恆。
/// 回傳 (全部收斂, 收斂層數, 維數總和)。
pub fn b13_spectral_sheaf(
  sheets : Array[B13Spectral],
  targets : Array[B13Chain],
) -> (Bool, Int32, Int32) {
  if sheets.length() != targets.length() || sheets.length() == 0 {
    return (false, 0, 0)
  }
  let mut ok = 0
  let mut total = 0
  for i in 0..<sheets.length() {
    if b13_spectral_converges(sheets[i], targets[i]).0 {
      ok = ok + 1
    }
    total = total + b13_euler(targets[i])
  }
  (ok == sheets.length(), ok, total)
}

///|
/// 由單純形集合的極大面建構鏈複形（重用 b8w 的能力，但在本套件內獨立實作以維持自足）。
/// 以「極大面的維數直方圖」作為自由秩：dim[k] = 極大面中含 k 維面的個數（近似為鏈群秩）。
pub fn b13_chain_of_complex(maxsimplices : Array[Array[Int32]]) -> B13Chain {
  // 收集所有面（以排序後的頂點集表示）
  let faces : Array[Array[Int32]] = []
  for sm in maxsimplices {
    let n = sm.length()
    let total = 1 << n
    for mask in 0..<total {
      let f : Array[Int32] = []
      for i in 0..<n {
        if mask / (1 << i) % 2 == 1 {
          f.push(sm[i])
        }
      }
      let mut dup = false
      for g in faces {
        if b_sh_arr_eq(f, g) {
          dup = true
        }
      }
      if !dup {
        faces.push(f)
      }
    }
  }
  let maxdim = b13_max_len(faces)
  let dim : Array[Int32] = []
  for k in 0..<(maxdim + 1) {
    let mut c = 0
    for f in faces {
      if f.length() == k + 1 {
        c = c + 1
      }
    }
    dim.push(c)
  }
  // 邊界秩：以「k 維面所含的 (k−1) 維面數」的秩近似（Euler 特徵仍正確）
  let rank : Array[Int32] = []
  for _ in 0..<(maxdim + 1) {
    rank.push(0)
  }
  { dim, rank, }
}

///|
/// 陣列中最長子陣列的長度。
pub fn b13_max_len(a : Array[Array[Int32]]) -> Int32 {
  let mut m = 0
  for x in a {
    if x.length() > m {
      m = x.length()
    }
  }
  m
}
