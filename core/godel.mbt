///|
/// go: 哥德爾編碼基礎（批次十二的地基）。
///
/// 為什麼需要這一層：批次十二要討論「可證性、不可證性、自洽性」這些**元數學**概念。
/// 計算引擎不能空口說「此句不可證」，所有論斷都必須落在真正可執行的整數算術上，
/// 因此先把形式系統的語法降為**哥德爾編碼**（整數），把「證明」降為「有限整數序列」：
///
///   符號 → 數字： 0 ↦ 1（零）、S ↦ 2（後繼）、+ ↦ 3、× ↦ 4、= ↦ 5、
///                 ¬ ↦ 6、→ ↦ 7、∀ ↦ 8、v_i ↦ 11 + i
///   式子 → 哥德爾數： ⌜s_0 … s_{k−1}⌝ = ∏ p_i^{c_i}（p_i 為第 i 個質數）
///
/// 有了它，本批次所有「自指」「一致性」「不可判定」的敘述都可以變成
/// **對整數的計算**（質數分解、指數大小、模算術），而不是對語言的空話。

///|
/// 前 n 個質數（供哥德爾編碼使用；由 core/arith.mbt 的 primes_upto 取得再截斷）。
pub fn go_primes(n : Int32) -> Array[Int64] {
  let ps = primes_upto(64)
  let out : Array[Int64] = []
  for i in 0..<n {
    if i < ps.length() {
      out.push(ps[i].to_int64())
    }
  }
  out
}

///|
/// 符號編碼：回傳 [名稱, 代碼] 的對照表（報告與測試共用同一份，避免兩處各寫一次）。
pub fn go_symbol_table() -> Array[(String, Int32)] {
  [
    ("0", 1),
    ("S", 2),
    ("+", 3),
    ("×", 4),
    ("=", 5),
    ("¬", 6),
    ("→", 7),
    ("∀", 8),
    ("v(0)", 11),
    ("v(1)", 12),
    ("v(2)", 13),
    ("v(3)", 14),
    ("v(4)", 15),
    ("v(5)", 16),
    ("v(6)", 17),
    ("v(7)", 18),
    ("v(8)", 19),
    ("v(9)", 20),
  ]
}

///|
/// 單一符號的代碼查表（找不到回傳 0）。
pub fn go_code(name : String) -> Int32 {
  for (n, c) in go_symbol_table() {
    if n == name {
      return c
    }
  }
  0
}

///|
/// 哥德爾數：⌜s_0 … s_{k−1}⌝ = ∏ p_i^{c_i}（Int64；測試用的式子都很短，不會溢位）。
pub fn go_godel(codes : Array[Int32]) -> Int64 {
  let ps = go_primes(codes.length())
  let mut acc : Int64 = 1L
  for i in 0..<codes.length() {
    acc = acc * pow64(ps[i], codes[i])
  }
  acc
}

///|
/// 反解：把哥德爾數拆回符號代碼序列（質數分解，指數 > 0 的部分才輸出）。
pub fn go_ungodel(n : Int64) -> Array[Int32] {
  let out : Array[Int32] = []
  let p = factorize(n)
  for i in 0..<p.length() {
    out.push(p[i].1)
  }
  out
}

///|
/// 由符號名稱序列直接編碼（報告用；例：["S","0"] ↦ ⌜S0⌝）。
pub fn go_godel_of_names(names : Array[String]) -> Int64 {
  let codes : Array[Int32] = []
  for nm in names {
    codes.push(go_code(nm))
  }
  go_godel(codes)
}

///|
/// 逐元素整數比較（與 common 的泛型版本分開，避免 core 反向依賴 common）。
pub fn[T : Eq] go_arr_eq(a : Array[T], b : Array[T]) -> Bool {
  if a.length() != b.length() {
    return false
  }
  for i in 0..<a.length() {
    if a[i] != b[i] {
      return false
    }
  }
  true
}

///|
/// 康托配對函數 π(a, b) = (a+b)(a+b+1)/2 + b（可逆，用於把「序對」編成單一自然數）。
pub fn go_cantor_pair(a : Int32, b : Int32) -> Int32 {
  let s = a + b
  s * (s + 1) / 2 + b
}

///|
/// 康托配對的反解：回傳 (a, b)，使 π(a, b) = n。
pub fn go_cantor_unpair(n : Int32) -> (Int32, Int32) {
  let mut w = 0
  while w * (w + 1) / 2 <= n {
    w = w + 1
  }
  w = w - 1
  let t = w * (w + 1) / 2
  (w - (n - t), n - t)
}

///|
/// 哥德爾 β 函數（初等函數編碼有限序列的關鍵）：β(c, d, i) = c mod (1 + (i+1)·d)。
/// 有了它，任一個有限整數序列都能用兩個數 (c, d) 表示——這是「證明即有限對象」的算術化。

///|
/// 數學意義上的取模（恆為非負）：MoonBit 的 `%` 對負數回傳負餘數，CRT 需要非負代表元。
pub fn go_mod(a : Int64, m : Int64) -> Int64 {
  let r = a % m
  if r < 0L {
    r + m
  } else {
    r
  }
}

///|
/// 中國剩餘定理編碼：找出 (c, d) 使 β(c, d, i) = seq[i]（i = 0 … k−1）。
///
/// 關鍵細節：β 的模數**必須**是 m_i = 1 + (i+1)·d（這是 β 的定義，不能自由挑），
/// 因此 d 只能取 k!（保證 m_i 兩兩互質）。k ≥ 6 時 ∏m_i 遠超 2⁶³，
/// 所以 c 用 BigInt 承載；β 的還原也走 BigInt 版本 `go_beta_big`。
/// 這樣「證明即有限整數序列」的算術化對任意長度都成立，而不再受限於 Int64。
pub fn go_beta_encode(seq : Array[Int32]) -> (@bigint.BigInt, Int64) {
  let k = seq.length()
  let mut d : Int64 = 1L
  for i in 1..<=k {
    d = d * i.to_int64()
  }
  let mut c = @bigint.BigInt::from_int(0)
  let mut modprod = @bigint.BigInt::from_int(1)
  for i in 0..<k {
    let m = 1L + (i.to_int64() + 1L) * d
    let target = go_mod(seq[i].to_int64(), m)
    // 解 c + modprod·x ≡ target (mod m)
    let mut x : Int64 = 0L
    while go_bigmod_big(c.add(modprod.mul(go_big_of(x))), go_big_of(m)) !=
          go_big_of(target) {
      x = x + 1L
      if x > m {
        break
      }
    }
    let newmod = modprod.mul(go_big_of(m))
    c = go_bigmod_big(c.add(modprod.mul(go_big_of(x))), newmod)
    modprod = newmod
  }
  (c, d)
}

///|
/// β 函數的 BigInt 版本：β(c, d, i) = c mod (1 + (i+1)·d)，回傳非負餘數。
pub fn go_beta_big(c : @bigint.BigInt, d : Int64, i : Int32) -> @bigint.BigInt {
  go_bigmod_big(c, go_big_of(1L + (i.to_int64() + 1L) * d))
}

///|
/// 把 β 還原結果轉回 Int64（值必為 0 … 2³¹，安全）。
pub fn go_beta_val(c : @bigint.BigInt, d : Int64, i : Int32) -> Int64 {
  @bigint.BigInt::to_int(go_beta_big(c, d, i)).to_int64()
}

///|
/// Int64 → BigInt（以 10⁹ 為基分段累加，避開 from_int 只收 Int 的限制）。
pub fn go_big_of(x : Int64) -> @bigint.BigInt {
  let mut v = @bigint.BigInt::from_int(0)
  let base = @bigint.BigInt::from_int(1000000000)
  let mut rest = if x < 0L { -x } else { x }
  let parts : Array[Int32] = []
  while rest > 0L {
    parts.push((rest % 1000000000L).to_int())
    rest = rest / 1000000000L
  }
  if parts.length() == 0 {
    parts.push(0)
  }
  for i in 0..<parts.length() {
    let idx = parts.length() - 1 - i
    v = v.mul(base).add(@bigint.BigInt::from_int(parts[idx]))
  }
  if x < 0L {
    v = @bigint.BigInt::from_int(0).sub(v)
  }
  v
}

///|
/// BigInt 取模（回傳非負餘數）。
pub fn go_bigmod_big(a : @bigint.BigInt, m : @bigint.BigInt) -> @bigint.BigInt {
  let r = a % m
  if r < go_big_of(0L) {
    r + m
  } else {
    r
  }
}
