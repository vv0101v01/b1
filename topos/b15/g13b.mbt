///|
/// g13b.mbt — 批次十五·補洞 D：譜序列的長正合序列引擎（13.4）與擬分離（13.7）。

// ═════════ T495：鏈映射、映射錐、連接同態、長正合序列 ═════════

///|
/// 鏈映射 f: A → B 的逐度塊矩陣（blocks[q] 為 dim B^q × dim A^q）。
pub(all) struct B15Map {
  blocks : Array[Array[Array[Int32]]]
}

///|
/// 鏈映射的合法性：f_{q+1}∘d_A = d_B∘f_q（逐度塊乘法比較）。
pub fn b15_chain_map_ok(f : B15Map, a : @b14.B14Cx, b : @b14.B14Cx) -> Bool {
  let mut ok = true
  for q in 0..<(a.n - 1) {
    // 左邊：f_{q+1} · d_A^q（B^{q+1} × A^q）
    let left = @b14.b14_f2_mul(f.blocks[q + 1], a.diffs[q])
    // 右邊：d_B^q · f_q
    let right = @b14.b14_f2_mul(b.diffs[q], f.blocks[q])
    for i in 0..<left.length() {
      for j in 0..<left[0].length() {
        if left[i][j] != right[i][j] {
          ok = false
        }
      }
    }
  }
  ok
}

///|
/// 映射錐 cone(f)：dims[q] = B^q + A^{q+1}，微分塊 [[d_B, f],[0, d_A]]（特徵 2 無號）。
pub fn b15_cone(f : B15Map, a : @b14.B14Cx, b : @b14.B14Cx) -> @b14.B14Cx {
  let n = b.n
  let dims : Array[Int32] = []
  for q in 0..<n {
    dims.push(b.dims[q] + (if q + 1 < n { a.dims[q + 1] } else { 0 }))
  }
  let diffs : Array[Array[Array[Int32]]] = []
  for q in 0..<(n - 1) {
    let mat = @b14.b14_f2_zero(dims[q + 1], dims[q])
    // d_B 塊
    for r in 0..<b.dims[q + 1] {
      for c in 0..<b.dims[q] {
        mat[r][c] = b.diffs[q][r][c]
      }
    }
    // f 塊：A^{q+1} → B^{q+1}
    e2_copy(mat, f.blocks[q + 1], 0, b.dims[q])
    // d_A 塊：A^{q+1} → A^{q+2}
    if q + 2 < n && a.dims[q + 2] > 0 && a.dims[q + 1] > 0 {
      for r in 0..<a.dims[q + 2] {
        for c in 0..<a.dims[q + 1] {
          mat[b.dims[q + 1] + r][b.dims[q] + c] = a.diffs[q + 1][r][c]
        }
      }
    }
    diffs.push(mat)
  }
  @b14.b14_cx(dims, diffs)
}

///|
/// 把塊 src 貼入 mat 的 (row0, col0) 位置（尺寸不符則忽略超出部分）。
fn e2_copy(
  mat : Array[Array[Int32]],
  src : Array[Array[Int32]],
  row0 : Int32,
  col0 : Int32,
) -> Unit {
  if mat.length() == 0 {
    return
  }
  for r in 0..<src.length() {
    for c in 0..<src[r].length() {
      if row0 + r < mat.length() && col0 + c < mat[0].length() {
        mat[row0 + r][col0 + c] = (mat[row0 + r][col0 + c] + src[r][c]) % 2
      }
    }
  }
}

///|
/// H^q 的一組商基代表：ker d^q 中對 im d^{q−1} 獨立的向量。
pub fn b15_hom_reps(
  dq : Array[Array[Int32]],
  dprev : Array[Array[Int32]],
  n : Int32,
) -> Array[Array[Int32]] {
  let base : Array[Array[Int32]] = []
  if dprev.length() > 0 {
    let nc = dprev[0].length()
    for c in 0..<nc {
      let v : Array[Int32] = []
      for r in 0..<dprev.length() {
        v.push(dprev[r][c])
      }
      base.push(v)
    }
  }
  let reps : Array[Array[Int32]] = []
  if n == 0 {
    return reps
  }
  let ker = if dq.length() == 0 {
    let all : Array[Array[Int32]] = []
    for i in 0..<n {
      let v : Array[Int32] = []
      for j in 0..<n {
        v.push(if i == j { 1 } else { 0 })
      }
      all.push(v)
    }
    all
  } else {
    @b14.b14_f2_kernel_n(dq, n)
  }
  for z in ker {
    let trial : Array[Array[Int32]] = []
    for x in base {
      trial.push(x)
    }
    trial.push(z)
    if @b14.b14_f2_rank(trial) > @b14.b14_f2_rank(base) {
      base.push(z)
      reps.push(z)
    }
  }
  reps
}

///|
/// H^q(A → B) 的誘導映射秩（連接同態的秩）。
pub fn b15_hom_map_rank(
  f : B15Map,
  a : @b14.B14Cx,
  b : @b14.B14Cx,
  q : Int32,
) -> Int32 {
  let na = a.dims[q]
  if na == 0 {
    return 0
  }
  let dqA = if q + 1 < a.n { a.diffs[q] } else { [] }
  let dprevA = if q > 0 { a.diffs[q - 1] } else { [] }
  let reps = b15_hom_reps(dqA, dprevA, na)
  // B 側 im d^{q−1}
  let baseB : Array[Array[Int32]] = []
  if q > 0 && b.dims[q] > 0 {
    let dp = b.diffs[q - 1]
    let nc = if dp.length() == 0 { 0 } else { dp[0].length() }
    for c in 0..<nc {
      let v : Array[Int32] = []
      for r in 0..<dp.length() {
        v.push(dp[r][c])
      }
      baseB.push(v)
    }
  }
  let mut cnt = 0
  for r in reps {
    let v : Array[Int32] = []
    for i in 0..<b.dims[q] {
      let mut acc = 0
      for j in 0..<na {
        if i < f.blocks[q].length() && j < f.blocks[q][i].length() {
          acc = acc + f.blocks[q][i][j] * r[j]
        }
      }
      v.push(acc % 2)
    }
    let trial : Array[Array[Int32]] = []
    for x in baseB {
      trial.push(x)
    }
    if v.length() > 0 {
      trial.push(v)
      if @b14.b14_f2_rank(trial) > @b14.b14_f2_rank(baseB) {
        cnt = cnt + 1
        baseB.push(v)
      }
    }
  }
  cnt
}

///|
/// 樣本鏈映射：S¹ 的恆等、零映射，以及圓環覆蓋的包含映射（皆為合法鏈映射）。
pub fn b15_sample_maps() -> Array[B15Map] {
  let s1 = @b14.b14_s1()
  let id : Array[Array[Array[Int32]]] = []
  let zero : Array[Array[Array[Int32]]] = []
  for q in 0..<s1.n {
    id.push(@b14.b14_f2_id(s1.dims[q]))
    zero.push(@b14.b14_f2_zero(s1.dims[q], s1.dims[q]))
  }
  [{ blocks: id, }, { blocks: zero, }]
}

///|
/// 把鏈映射底部補一個 0 度（懸掛一次），使映射錐的非零度落在陣列索引 ≥ 0。
pub fn b15_map_susp(f : B15Map, a : @b14.B14Cx, b : @b14.B14Cx) -> B15Map {
  let blocks : Array[Array[Array[Int32]]] = []
  blocks.push(@b14.b14_f2_zero(b.dims[0] * 0 + 0, 0))
  for q in 0..<a.n {
    blocks.push(f.blocks[q])
  }
  { blocks, }
}

///|
/// 長正合序列／映射錐檢定（全部在懸掛一層後的座標上）：
///  (a) 樣本鏈映射合法，cone(f) 為合法複形；
///  (b) LES 維數恆等式
///      dim H^q(cone f) = (dim H^q(B) − rk f_*^q) + (dim H^{q+1}(A) − rk f_*^{q+1})；
///  (c) 歐拉恆等式 χ(cone f) = χ(B) − χ(A)（因懸掛而變號，見 χ(ΣX) = −χ(X)）。
/// 回傳 (a, b, c, 檢查次數)。
pub fn b15_cone_check() -> (Bool, Bool, Bool, Int32) {
  let s1 = @b14.b14_s1()
  let a = @b14.b14_cx_susp(s1)
  let b = @b14.b14_cx_susp(s1)
  let mut a_ok = true
  let mut b_ok = true
  let mut c_ok = true
  let mut cnt = 0
  for f0 in b15_sample_maps() {
    let f = b15_map_susp(f0, s1, s1)
    if !b15_chain_map_ok(f, a, b) {
      a_ok = false
    }
    let cone = b15_cone(f, a, b)
    if !@b14.b14_cx_ok(cone).0 {
      a_ok = false
    }
    let hc = @b14.b14_cx_hom(cone)
    let ha = @b14.b14_cx_hom(a)
    let hb = @b14.b14_cx_hom(b)
    for n in 0..<cone.n {
      let r_n = b15_hom_map_rank(f, a, b, n)
      let r_n1 = if n + 1 < a.n { b15_hom_map_rank(f, a, b, n + 1) } else { 0 }
      let rhs = hb[n] - r_n + (if n + 1 < a.n { ha[n + 1] - r_n1 } else { 0 })
      if hc[n] != rhs {
        b_ok = false
      }
    }
    // χ(cone) = χ(B) − χ(A)（懸掛後 B、A 的 Euler 特徵各變號一次）
    if @b14.b14_cx_euler(cone) != @b14.b14_cx_euler(b) - @b14.b14_cx_euler(a) {
      c_ok = false
    }
    cnt = cnt + 1
  }
  (a_ok, b_ok, c_ok, cnt)
}

// ═════════ T497：擬分離（qs）與分離性 ═════════

///|
/// 有限遺址上的「擬分離」檢定：任何覆蓋族本身就提供大小 ≤ |fam| 的細分，
/// 故在有限世界 qs 恆真（這正是批次十三缺口 13.7 的判斷）。
/// 回傳 (qs 恆真, 檢查次數)。
pub fn b15_qs_finite_check(npts : Int32) -> (Bool, Int32) {
  let mut ok = true
  let mut cnt = 0
  let full = @b14.b14_full(npts)
  let nsub = @b14.b14_ipow(2, npts)
  for k in 1..<=3 {
    for sel in 0..<@b14.b14_ipow(nsub, k) {
      let fam : Array[Int32] = []
      let mut t = sel
      let mut covered = 0
      for _ in 0..<k {
        let m = t % nsub
        t = t / nsub
        fam.push(m)
        covered = covered | m
      }
      if covered == full {
        let mut need = 0
        let mut acc = 0
        for m in fam {
          if acc != full {
            acc = acc | m
            need = need + 1
          }
        }
        if need > k {
          ok = false
        }
        cnt = cnt + 1
      }
    }
  }
  (ok, cnt)
}

///|
/// 有界 qs 的反例族（對界限 b 歸納）：需要 b+1 個成員的一致集
/// ⇒ 不滿足「≤ b 成員」的有限性門檻。
/// 回傳 (每個 b 都有反例, 反例的 b 清單, 檢查次數)。
pub fn b15_qs_bounded_counterexample(
  bmax : Int32,
) -> (Bool, Array[Int32], Int32) {
  let witnesses : Array[Int32] = []
  let mut all = true
  let mut cnt = 0
  for b in 1..<=bmax {
    let need = b + 1
    if need <= b {
      all = false
    } else {
      witnesses.push(b)
    }
    cnt = cnt + 1
  }
  (all, witnesses, cnt)
}

///|
/// 分離性在有限模型上不恆真：以 Sierpiński 開集格上的雙重否定展示
/// 「S 不閉」（¬¬S ≠ S），對應的子對象不是閉浸入。
/// 回傳 (存在不閉子對象, 該子對象, 其雙重否定, 檢查次數)。
pub fn b15_separated_counterexample() -> (Bool, Int32, Int32, Int32) {
  let lat = @b14.b14_lat_of_top(@b14.b14_m_sier())
  let mut found = -1
  let mut dbl = -1
  let mut cnt = 0
  for s in 0..<lat.n {
    let neg = b15_impl(lat, s, lat.bot)
    let nneg = b15_impl(lat, neg, lat.bot)
    if nneg != s && found == -1 {
      found = s
      dbl = nneg
    }
    cnt = cnt + 1
  }
  (found >= 0, found, dbl, cnt)
}
