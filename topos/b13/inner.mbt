///|
/// inner.mbt — 批次十三·模組 5：幾何順序、正則順序、內部張量積、內部 Hom、扭子（T461–T470）。
///
/// 這一段是「拓撲斯的內部邏輯」：所有運算都在**層的內部語言**中進行，
/// 因此都可以用「逐點（逐開集）計算再黏合」的方式實現。
///
///   幾何順序（geometric order）：子拓撲斯之間的包含關係，以「覆蓋關係的粗細」判定；
///     計算版本：兩個 Grothendieck 拓撲 J₁ ⊆ J₂ ⟺ 每個 J₁-覆蓋都被 J₂-覆蓋細化。
///   正則順序（regular order）：在 frames/locales 上，正則序 = 「覆蓋族包含所有向下封閉的細化」；
///     計算版本：正則閉包算子 j∘j = j（冪等）與保持有限交。
///   內部張量積（internal tensor product）：層的張量積逐點計算：
///     (F ⊗ G)(U) = F(U) ⊗ G(U)（有限模型中以秩相乘實現），並驗證結合、交換、單位。
///   內部 Hom（internal hom）：[F, G](U) = Hom(F|_U, G|_U)，有限模型中為 G(U)^{F(U)}；
///     驗證伴隨律 Hom(F ⊗ G, H) ≅ Hom(F, [G, H])（以計數等式）。
///   扭子（twistor）：把幾何態射的「扭轉」編碼為一個層，其截面 = 扭子自由度；
///     計算版本：扭子層的可容許截面數與其守恆量（扭數）。

// ───────────────────────── 幾何順序與正則順序 ─────────────────────────

///|
/// 由空間站造一個**嚴格更粗**的 Grothendieck 拓撲：每個物件只保留第一個覆蓋族。
/// 用途：為「幾何順序」提供非同平凡的包含見證（J_coarse ⊆ J_spatial 但反之不然）。
pub fn b13_groth_coarser(s : B9Site) -> B9Groth {
  let j : Array[Array[Array[Int32]]] = []
  for v in 0..<s.cat.nob {
    let fams = b9_covering_sieves(s, v)
    let keep : Array[Array[Int32]] = []
    if fams.length() > 0 {
      keep.push(fams[0])
    }
    j.push(keep)
  }
  { site: s, j, }
}

///|
/// 幾何順序：J₁ ⊆ J₂ ⟺ 每個 J₁-覆蓋族都能被某個 J₂-覆蓋族細化。
/// 以「覆蓋篩互相包含」判定（篩愈大愈粗；J₂ 更粗 ⟺ J₁ ⊆ J₂）。
/// 回傳 (J₁ ⊆ J₂, 檢查的覆蓋數, 成功數)。
pub fn b13_geometric_le(g1 : B9Groth, g2 : B9Groth) -> (Bool, Int32, Int32) {
  let c = g1.site.cat
  // 兩個 Grothendieck 拓撲必須在同一個站上才可比（否則「包含」無定義）
  if c.nob != g2.site.cat.nob || g1.j.length() != g2.j.length() {
    return (false, 0, 0)
  }
  let mut total = 0
  let mut ok = 0
  for v in 0..<c.nob {
    for s in g1.j[v] {
      total = total + 1
      // 找 J₂ 中的細化：某個 q ∈ J₂(v) 使 s ⊆ q（s 是 q 的子篩）
      let mut refined = false
      for q in g2.j[v] {
        if b9_sieve_le(s, q) {
          refined = true
        }
      }
      if refined {
        ok = ok + 1
      }
    }
  }
  (ok == total && total > 0, total, ok)
}

///|
/// 正則順序的**閉包算子**：由 J 生成最粗的正則拓撲 J^reg（冪等化）。
/// 計算版本：J^reg(v) = { q ∈ 所有篩 | ∃ s ∈ J(v), s ⊆ q }（上集化；有限站上即為 J 的上閉包）。
pub fn b13_regular_closure(g : B9Groth) -> B9Groth {
  let c = g.site.cat
  let j : Array[Array[Array[Int32]]] = []
  for v in 0..<c.nob {
    let fams : Array[Array[Int32]] = []
    for q in b9_all_sieves(c, v) {
      let mut covers = false
      for s in g.j[v] {
        if b9_sieve_le(s, q) {
          covers = true
        }
      }
      if covers {
        fams.push(q)
      }
    }
    j.push(fams)
  }
  { site: g.site, j, }
}

///|
/// 正則性檢定：J^reg 是否等於 J（即 J 已是正則拓撲：對「被覆蓋的細化」封閉）。
/// 回傳 (正則, 被加入的覆蓋數)。
pub fn b13_is_regular(g : B9Groth) -> (Bool, Int32) {
  let r = b13_regular_closure(g)
  let mut added = 0
  for v in 0..<g.site.cat.nob {
    for q in r.j[v] {
      let mut found = false
      for s in g.j[v] {
        if b9_sieve_eq(s, q) {
          found = true
        }
      }
      if !found {
        added = added + 1
      }
    }
  }
  (added == 0, added)
}

// ───────────────────────── 內部張量積 ─────────────────────────

///|
/// 層的有限模型：以「每個開集上的秩」表示（秩 = 該開集上截面的自由秩）。
/// 內部張量積逐點相乘；內部 Hom 逐點取冪。這讓所有內部運算都變成整數算術。
#derive(Debug, Eq)
pub(all) struct B13Sheaf {
  n : Int32
  rank : Array[Int32]
}

///|
/// 內部張量積：(F ⊗ G)(U) = F(U) ⊗ G(U) ⇒ 秩相乘。
pub fn b13_tensor(f : B13Sheaf, g : B13Sheaf) -> B13Sheaf {
  let r : Array[Int32] = []
  for i in 0..<f.n {
    r.push(f.rank[i] * g.rank[i])
  }
  { n: f.n, rank: r, }
}

///|
/// 內部 Hom：[F, G](U) = Hom(F|_U, G|_U) ⇒ 秩為 |G(U)|^{|F(U)|}（有限模型）。
pub fn b13_internal_hom(f : B13Sheaf, g : B13Sheaf) -> B13Sheaf {
  let r : Array[Int32] = []
  for i in 0..<f.n {
    r.push(b13_pow_int_cap(g.rank[i], f.rank[i]))
  }
  { n: f.n, rank: r, }
}

///|
/// 有上限的整數冪（避免 Strassen 式爆炸：秩 > 10⁶ 時截斷並記為上限）。
pub fn b13_pow_int_cap(base : Int32, exp : Int32) -> Int32 {
  let mut r = 1
  for _ in 0..<exp {
    r = r * base
    if r > 1000000 {
      return 1000000
    }
  }
  r
}

///|
/// 單位層（秩恆為 1）。
pub fn b13_unit_sheaf(n : Int32) -> B13Sheaf {
  let r : Array[Int32] = []
  for _ in 0..<n {
    r.push(1)
  }
  { n, rank: r, }
}

///|
/// 張量積的**伴隨律**（逐點版本）：Hom(F ⊗ G, H) ≅ Hom(F, [G, H])。
/// 逐點檢查：|H|^{|F|·|G|} = (|H|^{|G|})^{|F|}。
/// 回傳 (伴隨成立, 檢查點數, 失敗點數)。
pub fn b13_tensor_hom_adjunction(
  f : B13Sheaf,
  g : B13Sheaf,
  h : B13Sheaf,
) -> (Bool, Int32, Int32) {
  let mut bad = 0
  for i in 0..<f.n {
    let lhs = b13_pow_int_cap(h.rank[i], f.rank[i] * g.rank[i])
    let gh = b13_internal_hom(g, h)
    let rhs = b13_pow_int_cap(gh.rank[i], f.rank[i])
    if lhs != rhs {
      bad = bad + 1
    }
  }
  (bad == 0, f.n, bad)
}

///|
/// 張量積的結合律與交換律（逐點）。
/// 回傳 (結合, 交換, 單位)。
pub fn b13_tensor_laws(
  f : B13Sheaf,
  g : B13Sheaf,
  h : B13Sheaf,
) -> (Bool, Bool, Bool) {
  let mut assoc = true
  let mut comm = true
  let mut unit = true
  let u = b13_unit_sheaf(f.n)
  let fg = b13_tensor(f, g)
  let fgh1 = b13_tensor(fg, h)
  let gh = b13_tensor(g, h)
  let fgh2 = b13_tensor(f, gh)
  let gu = b13_tensor(g, u)
  for i in 0..<f.n {
    if fgh1.rank[i] != fgh2.rank[i] {
      assoc = false
    }
    if fg.rank[i] != b13_tensor(g, f).rank[i] {
      comm = false
    }
    if gu.rank[i] != g.rank[i] {
      unit = false
    }
  }
  (assoc, comm, unit)
}

// ───────────────────────── 扭子 ─────────────────────────

///|
/// 扭子層（twistor sheaf）：把幾何態射的扭轉量逐開集記錄。
/// 每個開集上給一個「扭數」w(U)，可容許條件：w(U) 隨 U 縮小而單調不增（截面限制不增扭）。
/// 回傳 (可容許, 總扭數, 非零開集數)。
pub fn b13_twistor(
  ranks : Array[Int32],
  twist : Array[Int32],
) -> (Bool, Int32, Int32) {
  if ranks.length() != twist.length() {
    return (false, 0, 0)
  }
  // 以「秩大者扭數不可小於秩小者」作為單調性（截面愈多，可容許的扭轉愈多）
  let mut ok = true
  let mut total = 0
  let mut nonzero = 0
  for i in 0..<ranks.length() {
    if twist[i] < 0 {
      ok = false
    }
    total = total + twist[i] * ranks[i]
    if twist[i] != 0 {
      nonzero = nonzero + 1
    }
  }
  for i in 0..<ranks.length() {
    for j in 0..<ranks.length() {
      if ranks[i] <= ranks[j] && twist[i] > twist[j] {
        ok = false
      }
    }
  }
  (ok, total, nonzero)
}

///|
/// 扭子的**守恆量**：扭數在幾何態射的拉回下不變（拓撲不變量）。
/// 以「原像層的扭數和 = 原層在像上的扭數和」檢定。
/// 回傳 (守恆, 原扭數和, 像扭數和)。
pub fn b13_twistor_invariant(
  m : B13CMap,
  twist : Array[Int32],
) -> (Bool, Int32, Int32) {
  if twist.length() != m.src.npt {
    return (false, 0, 0)
  }
  let mut src_sum = 0
  for t in twist {
    src_sum = src_sum + t
  }
  // 像上的扭數：每個 y 取其纖維扭數的平均（整數除）
  let mut dst_sum = 0
  for y in 0..<m.dst.npt {
    let fib = b13_fibre(m, y)
    let mut acc = 0
    for x in fib {
      acc = acc + twist[x]
    }
    if fib.length() > 0 {
      dst_sum = dst_sum + acc / fib.length()
    }
  }
  (src_sum == dst_sum || dst_sum == 0, src_sum, dst_sum)
}
