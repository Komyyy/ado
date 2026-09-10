以下は Claude により非形式的に考え出された反例。形式化は人力で行う。

# 正標数における nilradical の非不変性:$\mathfrak{n}(\mathfrak{a}) = \mathfrak{n}(\mathfrak{r})$ の反例

Tao の Ado の定理の証明(定理 9、可解の場合)では、可解 Lie 代数 $\mathfrak{r}$ とその nilradical $\mathfrak{n}(\mathfrak{r})$ を含む余次元 1 のイデアル $\mathfrak{a}$ に対して

> $\mathfrak{a}$ の nilradical は $\mathfrak{a}$ 上 characteristic(すべての derivation で不変)であり、その帰結として $\mathfrak{n}(\mathfrak{a}) = \mathfrak{n}(\mathfrak{r})$

が使われる。標数 0 ではこれは正しいが、標数 $p > 0$ では両方とも破綻する。本文書はその明示的な反例($\dim = p + 3$、任意の素数 $p$ で一様に機能)をまとめたものである。

**主張(反例の内容)。** $\operatorname{char} k = p$ のとき、以下で構成する可解 Lie 代数 $\mathfrak{r}$ とその余次元 1 のイデアル $\mathfrak{a} \supseteq \mathfrak{n}(\mathfrak{r})$ について:

1. $\mathfrak{a}$ の derivation $D$ で $D\,\mathfrak{n}(\mathfrak{a}) \not\subseteq \mathfrak{n}(\mathfrak{a})$ となるものが存在する(nilradical は characteristic でない)。
2. $\mathfrak{n}(\mathfrak{a}) \supsetneq \mathfrak{n}(\mathfrak{r})$(等式が偽)。

---

## 1. 構成

$k$ を標数 $p > 0$ の(任意の)体とする。

**加群 $V$。** $V := k^p$、基底 $v_0, \dots, v_{p-1}$、添字は $\mathbb{Z}/p$ で読む。$V$ 上の線型作用素として

- $z := \operatorname{id}_V$
- $A := $ 巡回シフト、$A v_i = v_{i+1}$($i \in \mathbb{Z}/p$)

をとる。$z$ と $A$ は可換。

**Lie 代数 $\mathfrak{a}$($\dim = p+2$)。** $\mathfrak{h} := k z \oplus k A$(可換)とし、表現 $\mathfrak{h} \to \mathfrak{gl}(V)$($z \mapsto \operatorname{id}$, $A \mapsto A$;可換な作用素の組なので Lie 代数準同型)による半直積

$$\mathfrak{a} := \mathfrak{h} \ltimes V.$$

構造定数(零でないもののみ、および反対称性による分):

| ブラケット | 値 |
|---|---|
| $[z, v_i]$ | $v_i$ |
| $[A, v_i]$ | $v_{i+1}$ |
| $[z, A]$ | $0$ |
| $[v_i, v_j]$ | $0$ |

$[\mathfrak{a}, \mathfrak{a}] \subseteq V$ が可換なので $\mathfrak{a}$ は metabelian、特に可解。

**derivation $D$。** $\deg z = 0$、$\deg A = 1$、$\deg v_i = i$ とおくと $\mathfrak{a}$ は $\mathbb{Z}/p$-次数付き Lie 代数になる。標数 $p$ なので次数 $\mathbb{Z}/p$ は $k$ のスカラーとして意味を持ち、grading derivation

$$D(z) = 0, \qquad D(A) = A, \qquad D(v_i) = i\, v_i$$

が定義できる(検証は §3)。

**Lie 代数 $\mathfrak{r}$($\dim = p+3$)。** $D$ による 1 次元拡大

$$\mathfrak{r} := \mathfrak{a} \rtimes_D k B, \qquad [B, X] := D(X) \ (X \in \mathfrak{a})$$

すなわち $[B, z] = 0$、$[B, A] = A$、$[B, v_i] = i\, v_i$。$[\mathfrak{r}, \mathfrak{r}] \subseteq kA \oplus V$、$[kA \oplus V, kA \oplus V] \subseteq V$、$[V, V] = 0$ より $\mathfrak{r}$ は可解(導来長 $\le 3$)。$\mathfrak{a}$ は $\mathfrak{r}$ の余次元 1 のイデアル($[B, \mathfrak{a}] = D\mathfrak{a} \subseteq \mathfrak{a}$)。

---

## 2. 鍵となる標数 $p$ の計算

**(K1)** $A^p = \operatorname{id}$(周期 $p$ の巡回シフト)。

**(K2)** 可換な作用素に対する Frobenius(freshman's dream)より、$\alpha, \gamma \in k$ に対し
$$(\alpha \operatorname{id} + \gamma A)^p = \alpha^p \operatorname{id} + \gamma^p A^p = (\alpha^p + \gamma^p)\operatorname{id} = (\alpha + \gamma)^p \operatorname{id}.$$
$k$ は体なので:$\alpha \operatorname{id} + \gamma A$ が冪零 $\iff \alpha + \gamma = 0$。
(冪零なら $\dim V = p$ より $p$ 乗で消えることに注意:$(\alpha+\gamma)^p = 0 \Rightarrow \alpha + \gamma = 0$。)

**(K3)** 特に $\operatorname{id} - A$ は冪零:$(\operatorname{id} - A)^p = 0$。実際 $V \cong k[t]/(t^p - 1) = k[t]/((t-1)^p)$($A = t$ 倍)とみると $\operatorname{id} - A$ は単一 Jordan ブロックで、冪零指数はちょうど $p$($(\operatorname{id}-A)^{p-1} \ne 0$)。

標数 $p$ 特有の現象:「可逆な $z$ と可逆な $A$ の差 $z - A$ が冪零」。これが反例の核心である。

---

## 3. $\mathfrak{a}$、$\mathfrak{r}$、$D$ の well-definedness

**$\mathfrak{a}$、$\mathfrak{r}$ が Lie 代数であること。** どちらも「可換とは限らない Lie 代数 $\mathfrak{h}'$ + その表現 $\rho: \mathfrak{h}' \to \mathfrak{gl}(V)$ + 可換イデアル $V$」の半直積 $\mathfrak{h}' \ltimes_\rho V$ であり、Jacobi 恒等式は表現の公理から従う。

- $\mathfrak{a}$:$\mathfrak{h} = kz \oplus kA$ 可換、$\rho(z) = \operatorname{id}$, $\rho(A) = A$ は可換なので準同型。
- $\mathfrak{r}$:$\mathfrak{h}' = kB \oplus kz \oplus kA$、ブラケットは $[B, A] = A$、他は $0$(2 次元非可換 Lie 代数 $\oplus$ 中心 $kz$;3 元の Jacobi は直接確認できる)。$\rho(B) = \Delta$($\Delta v_i := i\, v_i$)、$\rho(z) = \operatorname{id}$、$\rho(A) = A$。準同型の確認は $[\Delta, A] = A$ に帰着:
  $$\Delta A v_i - A \Delta v_i = (i+1) v_{i+1} - i\, v_{i+1} = v_{i+1} = A v_i. \checkmark$$

**$D$ が derivation であること。** 基底の組ごとに Leibniz 則 $D[X,Y] = [DX, Y] + [X, DY]$ を確認する:

- $(z, A)$:左辺 $D(0) = 0$;右辺 $[0, A] + [z, A] = 0$。✓
- $(z, v_i)$:左辺 $D v_i = i v_i$;右辺 $[0, v_i] + [z, i v_i] = i v_i$。✓
- $(A, v_i)$:左辺 $D v_{i+1} = (i+1) v_{i+1}$;右辺 $[A, v_i] + [A, i v_i] = (1 + i) v_{i+1}$。✓
  (添字は $\mathbb{Z}/p$、係数は $k$ の元。$i = p-1$ のとき左辺 $= D v_0 = 0 \cdot v_0 = 0$、右辺 $= p\, v_0 = 0$ となり、**係数が mod $p$ で読めることが本質的に使われる**。標数 0 ではこの $D$ は存在しない。)
- $(v_i, v_j)$:両辺とも $0$($[V,V] = 0$、$DV \subseteq V$)。✓

なお $[B, -] = D$ なので、$\mathfrak{r}$ の Jacobi のうち $B$ を含む分は「$D$ が derivation」と同値であり、上の確認がそのまま流用できる。

---

## 4. 補題:冪零イデアルの元は ad-冪零(標数不問)

**補題 L1。** $\mathfrak{g}$ を Lie 代数、$\mathfrak{j} \trianglelefteq \mathfrak{g}$ を冪零イデアル、$X \in \mathfrak{j}$ とすると $\operatorname{ad}_{\mathfrak{g}}(X)$ は冪零。

*証明。* 降中心列を $\mathfrak{j}^1 = \mathfrak{j}$, $\mathfrak{j}^{m+1} = [\mathfrak{j}, \mathfrak{j}^m]$ とする。$\operatorname{ad}(X)(\mathfrak{g}) \subseteq \mathfrak{j}$($\mathfrak{j}$ はイデアル)、$\operatorname{ad}(X)(\mathfrak{j}^m) \subseteq \mathfrak{j}^{m+1}$ より $\operatorname{ad}(X)^m(\mathfrak{g}) \subseteq \mathfrak{j}^m$。$\mathfrak{j}$ 冪零より或る $m$ で $\mathfrak{j}^m = 0$。∎

以下では対偶の形で使う:**$\operatorname{ad}(X)$ が冪零でない元 $X$ は、いかなる冪零イデアルにも属さない。** また $[X, V] \subseteq V$ のとき、$\operatorname{ad}(X)|_V$ が冪零でなければ $\operatorname{ad}(X)$ も冪零でない。

---

## 5. $\mathfrak{n}(\mathfrak{a}) = k(z - A) \oplus V$

$$\mathfrak{i} := k(z - A) \oplus V \subseteq \mathfrak{a}.$$

**(a) $\mathfrak{i}$ は $\mathfrak{a}$ のイデアル。** $[z, z-A] = [A, z-A] = 0$、$[z-A, v] = (\operatorname{id} - A)v \in V$、$[\mathfrak{h}, V] \subseteq V$、$[V, V] = 0$。✓

**(b) $\mathfrak{i}$ は冪零(類はちょうど $p$)。** 降中心列は
$$\mathfrak{i}^2 = [\mathfrak{i}, \mathfrak{i}] = \operatorname{im}(\operatorname{id} - A), \qquad \mathfrak{i}^{m+1} = \operatorname{im}(\operatorname{id} - A)^m \ (m \ge 1)$$
($\mathfrak{i}$ の中で $V$ どうし、および $z - A$ どうしのブラケットは消えるため)。(K3) より $\mathfrak{i}^{p+1} = 0$、$\mathfrak{i}^{p} \ne 0$。✓

**(c) 最大性。** $\mathfrak{j} \trianglelefteq \mathfrak{a}$ を任意の冪零イデアル、$X = \alpha z + \gamma A + w \in \mathfrak{j}$($w \in V$)とする。$[X, V] \subseteq V$ かつ $\operatorname{ad}(X)|_V = \alpha \operatorname{id} + \gamma A$。補題 L1 よりこれは冪零でなければならず、(K2) より $\alpha + \gamma = 0$、すなわち $X \in \mathfrak{i}$。よってすべての冪零イデアルは $\mathfrak{i}$ に含まれ、(a)(b) と合わせて

$$\boxed{\mathfrak{n}(\mathfrak{a}) = k(z - A) \oplus V.}$$

**(d) characteristic でないこと。**
$$D(z - A) = 0 - A = -A \notin \mathfrak{i}$$
($-A = \delta(z-A) + u$ とすると $z$ 成分の比較で $\delta = 0$、すると $-A \in V$ となり矛盾)。よって $D\,\mathfrak{n}(\mathfrak{a}) \not\subseteq \mathfrak{n}(\mathfrak{a})$。**これが主張 1 の反例である。**

*(補足:標数 0 の証明が通らない理由。この grading に対応するスケーリング自己同型 $v_i \mapsto t^i v_i$, $A \mapsto tA$ は $t^p = 1$ を要求するが、標数 $p$ では $t^p - 1 = (t-1)^p$ より $t = 1$ しか存在しない。すなわち $D$ は積分不能な derivation であり、「$e^{tD}$ が自己同型」という char 0 の論法の破れ方が正確にここに現れている。)*

---

## 6. $\mathfrak{n}(\mathfrak{r}) = V$

$V$ は $\mathfrak{r}$ の可換イデアルなので $V \subseteq \mathfrak{n}(\mathfrak{r})$。逆向きに、$\mathfrak{j} \trianglelefteq \mathfrak{r}$ を冪零イデアル、$X = \beta B + \alpha z + \gamma A + w \in \mathfrak{j}$($w \in V$)とし、$X \in V$ を 3 段階で示す。

**Step 1($\beta = 0$)。** $\mathfrak{j}$ はイデアルなので
$$[X, A] = \beta [B, A] - [A, w] = \beta A - Aw \in \mathfrak{j}.$$
$\beta \ne 0$ と仮定すると、$Y := \beta A - Aw$($V$ 成分 $-Aw$ は $V$ 上自明に作用)について $\operatorname{ad}(Y)|_V = \beta A$ であり、$(\beta A)^p = \beta^p \operatorname{id} \ne 0$ かつすべての冪も非零なので冪零でない。補題 L1 に矛盾。よって $\beta = 0$。

**Step 2($\alpha + \gamma = 0$)。** $X = \alpha z + \gamma A + w$ に §5(c) と同じ議論:$\operatorname{ad}(X)|_V = \alpha \operatorname{id} + \gamma A$ が冪零 $\Rightarrow$ (K2) より $\alpha + \gamma = 0$。

**Step 3($\alpha = \gamma = 0$)。** $X = \delta(z - A) + w$($\delta := \alpha$)と書ける。$\mathfrak{j}$ はイデアルなので
$$[B, X] = \delta([B,z] - [B,A]) + [B, w] = -\delta A + \underbrace{[B,w]}_{\in V} \in \mathfrak{j}.$$
$\delta \ne 0$ なら Step 1 と同じ議論($\operatorname{ad}(-\delta A + u)|_V = -\delta A$ は冪零でない)で矛盾。よって $\delta = 0$、$X = w \in V$。

以上より任意の冪零イデアルは $V$ に含まれ、

$$\boxed{\mathfrak{n}(\mathfrak{r}) = V.}$$

*(注:Step 3 が必要な理由。$\operatorname{ad}_{\mathfrak{r}}(z-A)$ 自体は冪零($B \mapsto A \mapsto 0$、$V \mapsto (\operatorname{id}-A)V \to 0$)なので、ad-冪零性だけでは $z - A$ を排除できない。排除するのは「$\mathfrak{j}$ がイデアル」という条件、すなわち $[B, z-A] = -A$ が $\mathfrak{j}$ に入ってしまうことである。)*

---

## 7. 結論

$\mathfrak{r}$ は可解、$\mathfrak{a} \trianglelefteq \mathfrak{r}$ は余次元 1 のイデアルで $\mathfrak{n}(\mathfrak{r}) = V \subseteq \mathfrak{a}$ を満たす(Tao の定理 9 の設定そのもの)。しかし

$$\mathfrak{n}(\mathfrak{a}) = k(z-A) \oplus V \supsetneq V = \mathfrak{n}(\mathfrak{r}).$$

**これが主張 2 の反例である。** なお両者の食い違いを与える元 $z - A$ はまさに $D(z-A) = -A \notin \mathfrak{n}(\mathfrak{a})$ を通じて characteristic 性を破る元であり、主張 1 と 2 が(前の議論の通り)同じ現象の二つの顔であることが具体的に見える。$\mathfrak{n}(\mathfrak{a})$ の冪零類はちょうど $p$ で、「冪零類 $< p-1$ なら characteristic 性が回復する(nilregular)」という既知の閾値とも整合する。

---

## 8. 最小例($p = 2$;$\dim \mathfrak{a} = 4$, $\dim \mathfrak{r} = 5$)

Lean での動作確認・デバッグ用に、$p = 2$、$k = \mathbb{F}_2$(または標数 2 の任意の体)の場合の全構造定数を列挙する。基底:$B, z, A, v_0, v_1$。

零でないブラケット(反対称で閉じる):

| | 値 |
|---|---|
| $[B, A]$ | $A$ |
| $[B, v_1]$ | $v_1$ |
| $[z, v_0]$ | $v_0$ |
| $[z, v_1]$ | $v_1$ |
| $[A, v_0]$ | $v_1$ |
| $[A, v_1]$ | $v_0$ |

($[B,z] = [B,v_0] = [z,A] = [v_i,v_j] = 0$。)

- $\mathfrak{a} = \operatorname{span}(z, A, v_0, v_1)$、$\mathfrak{n}(\mathfrak{a}) = \operatorname{span}(z + A,\ v_0,\ v_1)$(標数 2 なので $z - A = z + A$)。
- $D = [B, -]|_{\mathfrak{a}}$:$Dz = 0$, $DA = A$, $Dv_0 = 0$, $Dv_1 = v_1$。$D(z+A) = A \notin \mathfrak{n}(\mathfrak{a})$。
- $\mathfrak{n}(\mathfrak{r}) = \operatorname{span}(v_0, v_1)$。
- 検算:$(z+A)$ の $V$ への作用は $\begin{pmatrix} 1 & 1 \\ 1 & 1 \end{pmatrix}$、その 2 乗は標数 2 で $0$。✓

---

## 9. 行列実現(半直積を避けたい場合)

$W := V \oplus k = k^{p+1}$ とし、$(M, u) \mapsto \begin{pmatrix} M & u \\ 0 & 0 \end{pmatrix}$ で $\mathfrak{gl}(V) \ltimes V \hookrightarrow \mathfrak{gl}_{p+1}(k)$ と埋め込むと、行列の交換子が
$$[(M, u), (N, w)] = ([M, N],\ Mw - Nu)$$
となり半直積のブラケットを実現する。よって

$$\mathfrak{r} \cong \operatorname{span}\{(\Delta, 0),\ (\operatorname{id}, 0),\ (A, 0),\ (0, v_0), \dots, (0, v_{p-1})\} \subseteq \mathfrak{gl}_{p+1}(k)$$

($\Delta v_i = i v_i$)。$p = 2$ なら $3 \times 3$ 行列で:

$$B = \begin{pmatrix} 0&0&0\\0&1&0\\0&0&0 \end{pmatrix},\quad z = \begin{pmatrix} 1&0&0\\0&1&0\\0&0&0 \end{pmatrix},\quad A = \begin{pmatrix} 0&1&0\\1&0&0\\0&0&0 \end{pmatrix},\quad v_0 = E_{13},\ v_1 = E_{23}.$$

Lean では `LieSubalgebra` として `Matrix (Fin (p+1)) (Fin (p+1)) k` の中に span で定義でき、Jacobi 恒等式の検証が不要になる(ブラケットで閉じていることの確認だけで済む)。

---

## 10. Lean 形式化ノート

**(i) nilradical を対象化しない定式化を推奨(注意:`LieAlgebra.maxNilpotentIdeal` は nilradical ではない)。** Mathlib(`Mathlib.Algebra.Lie.Nilpotent`)には

```
def maxNilpotentIdeal := sSup { I : LieIdeal R L | LieModule.IsNilpotent L I }
```

が存在するが、ここでの冪零性は **$L$-加群としての冪零性**(降中心列 $[L,[L,\dots,I]]$、括弧を $L$ 全体でとる)であり、イデアル $I$ 自身の Lie 代数としての冪零性 `LieRing.IsNilpotent ↥I`($I$ の内部だけで括弧をとる)より真に強い(Mathlib には片方向の instance `[LieModule.IsNilpotent L I] : LieRing.IsNilpotent ↥I` があるが逆は不成立)。実際 `maxNilpotentIdeal` は「$L$ が冪零に作用する最大イデアル」= hypercenter(上中心列 `LieSubmodule.ucs` の極限)に一致し、教科書的 nilradical とは **char 0 でも一般に異なる**:2 次元非可換可解代数 $\langle h, a\rangle$, $[h,a]=a$ では nilradical $= ka$ だが `maxNilpotentIdeal` $= \bot$。本反例でも $\mathfrak{a}, \mathfrak{r}$ とも中心が $0$ なので `maxNilpotentIdeal` は両方 $\bot$ となり、「等式」がこの不変量では自明に成立してしまう(= 反例が見えない)。したがって Tao の証明・本反例の形式化では `LieRing.IsNilpotent` に基づく冪零イデアルを使うこと。nilradical を対象として `sSup { I : LieIdeal R L | LieRing.IsNilpotent ↥I }` と自前定義する場合は、「冪零イデアル 2 つの和は冪零」(Fitting 型の補題)が Mathlib に無ければ補う必要がある(`maxNilpotentIdeal` が加群版で定義されているのは、加群版なら sup 閉性が自明に出るためと思われる)。反例の主張自体は nilradical を対象化せずに次の 3 つで完結する:

- **Thm A**:$\forall\, \mathfrak{j} : \text{LieIdeal } k\ \mathfrak{r}$, `LieRing.IsNilpotent ↥𝔧` $\to \mathfrak{j} \le V$(§6)。この(強い)形で示せば、上述の instance 経由で加群版冪零性のイデアルも自動的にカバーされる。
- **Thm B**:$\mathfrak{i} = k(z-A) \oplus V$ は $\mathfrak{a}$ の LieIdeal であり `LieRing.IsNilpotent ↥𝔦`(§5 (a)(b))。**必ずこの notion で述べること**:加群版 `LieModule.IsNilpotent 𝔞 ↥𝔦` は $[z, V] = V$ のため偽である。
- **Thm C**:$\neg(\mathfrak{i} \le V)$(witness: $z - A$)。

これで「$\mathfrak{a}$ の冪零イデアルは $\mathfrak{r}$ の冪零イデアルに含まれるとは限らない」= $\mathfrak{n}(\mathfrak{a}) \le \mathfrak{n}(\mathfrak{r})$ の反例、が nilradical の定義の選び方によらず得られる。derivation 版(主張 1)を独立に述べるなら追加で:

- **Thm D**:$D$ は `LieDerivation k 𝔞 𝔞`、$z - A \in \mathfrak{i}$、$D(z-A) \notin \mathfrak{i}$(§5 (d);最大性 §5 (c) も付ければ「nilradical が不変でない」の完全版)。

**(ii) 台となる型の選択。** 二案:

- **行列実現(§9)**:`LieSubalgebra k (Matrix (Fin (p+1)) (Fin (p+1)) k)`。Jacobi が自動で、ブラケット計算は行列計算。$p = 2$ を `Fin 3` の行列で先に通すのが楽。
- **$V = k[t]/(t^p - 1)$ 実現**:$A$ = $t$ 倍写像とすると (K1) が環の等式 $t^p = 1$、(K3) が `sub_pow_char`(freshman's dream)から直ちに出る。$\operatorname{id} - A$ の冪零性まわりはこちらが圧倒的に扱いやすい。基底 $v_i$ は $t^i$ に対応。

**(iii) 事前に用意する補題。**

- 補題 L1(冪零イデアルの元は ad-冪零)。Mathlib に対応物があるか要確認(`LieIdeal` / `LieModule.IsNilpotent` 周辺);なければ §4 の 6 行の証明をそのまま形式化。
- (K2):`add_pow_char`(可換部分環内での計算)+「体では $x^p = 0 \to x = 0$」。
- 「$[X, V] \subseteq V$ かつ $\operatorname{ad}(X)|_V$ 非冪零 $\Rightarrow \operatorname{ad}(X)$ 非冪零」(不変部分空間への制限)。
- 半直積を自前で組む場合:Lie 代数の半直積構成が Mathlib にあるか要確認。なければ §9 の行列実現で回避するのが早い。

**(iv) 証明の依存関係(すべて初等的)。** Engel・Lie・トレース論法・Jacobson 公式は一切使っていない。使うのは:イデアルの定義、降中心列、L1、(K1)–(K3) のみ。標数 $p$ が本質的に効く箇所は §2(K2, K3)と §3 の $(A, v_{p-1})$ の Leibniz 検証($p \equiv 0$)の 2 箇所である。
