///|
/// scan.mbt — 極簡詞法器：把 .mbt 原始碼切成 token，並標記「是否位於 test 區塊」。
///
/// 目的只有一個：讓 `cmd/tools` 能在**不呼叫外部程式**的前提下做靜態分析
/// （原 `tools/regen_deps.py` 與 `tools/qualify_test_uses.py` 靠解析 `moon check` 的文字輸出，
/// 那是不可能在 MoonBit 裡乾淨重現的介面）。本詞法器只需要正確處理三種遮蔽：
/// 行註解 `//`、字串 `"…"`、字元 `'…'`。
///
/// 設計原則：只認 ASCII 識別字（本專案所有標識符皆為 ASCII），其餘一律視為符號。

///|
#derive(Eq)
pub enum Tok {
  Ident(String)
  At(String)
  Sym(Char)
}

///|
pub struct Source {
  /// 套件目錄（相對於倉庫根）
  pkg : String
  /// 檔名（相對於倉庫根）
  file : String
  toks : Array[Tok]
  /// 每個 token 是否落在 test 區塊內
  in_test : Array[Bool]
}

///|
fn is_digit(c : Int32) -> Bool {
  c >= 48 && c <= 57
}

///|
fn is_upper(c : Int32) -> Bool {
  c >= 65 && c <= 90
}

///|
fn is_lower(c : Int32) -> Bool {
  c >= 97 && c <= 122
}

///|
fn is_ident_start(c : Int32) -> Bool {
  is_lower(c) || is_upper(c) || c == 95
}

///|
fn is_ident_char(c : Int32) -> Bool {
  is_ident_start(c) || is_digit(c)
}

///|
/// 以碼位逐一比較的字串排序（不依賴 locale，保證 CI 與本機一致）
pub fn s_cmp(a : String, b : String) -> Int32 {
  let ca = a.to_array()
  let cb = b.to_array()
  let n = if ca.length() < cb.length() { ca.length() } else { cb.length() }
  let mut i = 0
  while i < n {
    let x = ca[i].to_int()
    let y = cb[i].to_int()
    if x != y {
      return if x < y { -1 } else { 1 }
    }
    i = i + 1
  }
  if ca.length() < cb.length() {
    -1
  } else if ca.length() > cb.length() {
    1
  } else {
    0
  }
}

///|
/// 插入排序（穩定的字典序），刻意不用內建 sort 以免版本差異
pub fn sort_strs(a : Array[String]) -> Array[String] {
  let out : Array[String] = []
  for x in a {
    let mut pos = out.length()
    let mut j = 0
    let mut placed = false
    while j < out.length() {
      if !placed && s_cmp(x, out[j]) < 0 {
        pos = j
        placed = true
      }
      j = j + 1
    }
    out.insert(pos, x)
  }
  out
}

///|
pub fn uniq_strs(a : Array[String]) -> Array[String] {
  let s = sort_strs(a)
  let out : Array[String] = []
  for x in s {
    let mut dup = false
    for y in out {
      if y == x {
        dup = true
      }
    }
    if !dup {
      out.push(x)
    }
  }
  out
}

///|
pub fn tok_text(t : Tok) -> String {
  match t {
    Ident(s) => s
    At(s) => "@" + s
    Sym(c) => c.to_string()
  }
}

///|
fn substr(cs : Array[Char], from : Int32, to : Int32) -> String {
  let sb = StringBuilder()
  let mut i = from
  while i < to && i < cs.length() {
    sb.write_char(cs[i])
    i = i + 1
  }
  sb.to_string()
}

///|
/// 詞法切分
pub fn tokenize(src : String) -> Array[Tok] {
  let cs = src.to_array()
  let n = cs.length()
  let out : Array[Tok] = []
  let mut i = 0
  while i < n {
    let c = cs[i].to_int()
    // 空白（含換行）
    if c <= 32 {
      i = i + 1
      continue
    }
    // 行註解
    if c == 47 && i + 1 < n && cs[i + 1].to_int() == 47 {
      while i < n && cs[i].to_int() != 10 {
        i = i + 1
      }
      continue
    }
    // 字串（含轉義）
    if c == 34 {
      // 字串：內容以 "$…" 形式保留（讓「只差字面量」的函式不再被誤判為重複），
      // 插值 `\{ … }` 內的運算式照常遞迴切分。
      let sb = StringBuilder()
      i = i + 1
      let mut closed = false
      while i < n && !closed {
        let d = cs[i].to_int()
        if d == 92 {
          if i + 1 < n && cs[i + 1].to_int() == 123 {
            let mut j = i + 2
            let mut depth = 1
            while j < n && depth > 0 {
              let e = cs[j].to_int()
              if e == 123 {
                depth = depth + 1
              } else if e == 125 {
                depth = depth - 1
              }
              if depth > 0 {
                j = j + 1
              }
            }
            out.push(Ident("$" + sb.to_string()))
            sb.reset()
            for t in tokenize(substr(cs, i + 2, j)) {
              out.push(t)
            }
            i = j + 1
            continue
          }
          if i + 1 < n {
            sb.write_char(cs[i + 1])
          }
          i = i + 2
        } else if d == 34 {
          i = i + 1
          closed = true
        } else {
          sb.write_char(cs[i])
          i = i + 1
        }
      }
      out.push(Ident("$" + sb.to_string()))
      continue
    }
    // 字元字面量
    if c == 39 {
      i = i + 1
      let mut closed = false
      while i < n && !closed {
        let d = cs[i].to_int()
        if d == 92 {
          i = i + 2
        } else if d == 39 {
          i = i + 1
          closed = true
        } else {
          i = i + 1
        }
      }
      out.push(Sym('\''))
      continue
    }
    if is_ident_start(c) {
      let sb = StringBuilder()
      while i < n && is_ident_char(cs[i].to_int()) {
        sb.write_char(cs[i])
        i = i + 1
      }
      out.push(Ident(sb.to_string()))
      continue
    }
    if is_digit(c) {
      // 數值字面量保留原文（前面加 '#'），否則「同構但常數不同」的函式會誤判為重複
      let sb = StringBuilder()
      sb.write_char('#')
      while i < n && (is_ident_char(cs[i].to_int()) || cs[i].to_int() == 46) {
        sb.write_char(cs[i])
        i = i + 1
      }
      out.push(Ident(sb.to_string()))
      continue
    }
    if c == 64 {
      // '@'
      i = i + 1
      let sb = StringBuilder()
      while i < n && is_ident_char(cs[i].to_int()) {
        sb.write_char(cs[i])
        i = i + 1
      }
      out.push(At(sb.to_string()))
      continue
    }
    out.push(Sym(cs[i]))
    i = i + 1
  }
  out
}

///|
/// 標記 test 區塊：頂層 `test … {` 之後到對應 `}` 之間的全部 token。
pub fn mark_tests(toks : Array[Tok]) -> Array[Bool] {
  let n = toks.length()
  let flags : Array[Bool] = []
  for _ in 0..<n {
    flags.push(false)
  }
  let mut depth = 0
  let mut pending = false
  let mut in_test = false
  let mut i = 0
  while i < n {
    match toks[i] {
      Ident(s) => if s == "test" && depth == 0 && !in_test { pending = true }
      Sym(c) =>
        if c == '{' {
          if pending && depth == 0 {
            in_test = true
            pending = false
          }
          depth = depth + 1
        } else if c == '}' {
          depth = depth - 1
          if depth == 0 && in_test {
            in_test = false
            flags[i] = true
            i = i + 1
            continue
          }
        }
      _ => ()
    }
    if in_test || pending {
      flags[i] = true
    }
    i = i + 1
  }
  flags
}

///|
pub fn make_source(pkg : String, file : String, text : String) -> Source {
  let toks = tokenize(text)
  { pkg, file, toks, in_test: mark_tests(toks), }
}

///|
/// 讀檔（失敗回空字串，交由呼叫端決定是否致命）
pub fn read_text(path : String) -> String {
  @fs.read_file_to_string(path) catch {
    @fs.IOError(_) => ""
  }
}

///|
pub fn write_text(path : String, text : String) -> Unit {
  @fs.write_string_to_file(path, text) catch {
    @fs.IOError(m) => println("寫入失敗 " + path + ": " + m)
  }
}

///|
pub fn list_dir(path : String) -> Array[String] {
  try {
    if !@fs.is_dir(path) {
      return []
    }
    let v = @fs.read_dir(path)
    let out : Array[String] = []
    for x in v {
      out.push(x)
    }
    sort_strs(out)
  } catch {
    @fs.IOError(_) => []
  }
}

///|
pub fn has_suffix(s : String, suf : String) -> Bool {
  let a = s.to_array()
  let b = suf.to_array()
  if b.length() > a.length() {
    return false
  }
  let mut i = 0
  let mut ok = true
  while i < b.length() {
    if a[a.length() - b.length() + i] != b[i] {
      ok = false
    }
    i = i + 1
  }
  ok
}
