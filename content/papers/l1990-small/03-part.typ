#import "../../main-defs.typ": *
#import "../../statements.typ": *

=== #[ ] <sec:l1990-small-f4-perfect>

#source(16, printed: 155)Пусть $K$ — совершенное кольцо характеристики 2,
$phi in Aut N F_4(K)$. Здесь $C_("mod" Z_1) lr((Z_4)) = T(p_(32)) + T(q_(32))$ —
характеристическая подгруппа. Если $H = T(p_(32))^phi$ или $T(q_(32))^phi$, то
произведение $p_(32)$-проекции подгруппы $H$ на её $q_(32)$-проекцию совпадает с
$p_(42)$-проекцией множества $[[[H,p_(21)],q_(21)],H]$ и, следовательно, равно
нулю, так как $[H,H] subset Z_3 subset L_6$. По лемме
@lem:l1983-peirce-decomposition [@bib:l1990-small-Levchuk1983], умножая $phi$ на
идемпотентно-графовый автоморфизм, можно добиться $phi$-инвариантности по модулю
$L_2$ подгрупп $T(q_(32))$, $T(p_(32))$, а также подгруппы $T(p_(21))$, в силу
соотношения $[T(p_(21)),T(q_(32))]^phi subset T(q_(20)) = C lr((Z_3))$, и
аналогично подгруппы $T(q_(21))$.

Из равенств $C lr((Z_2)) = T(p_(21)) + T(q_(21))$,
$L_2 = Z_7 = C lr((Z_3)) + [q_(32)^phi,C lr((Z_2))] +
[p_(32)^phi,C lr((Z_2))]$ следует, что $q_(32)^phi = b q_(32)$ $("mod" L_2)$,
где $b in K$ — обратимый элемент; аналогично рассматриваем $q_(21)^phi$,
$q_(10)^phi$, $p_(32)^phi$. Используя также, что координаты коммутатора
$[x q_(32),y q_(21)]^phi$ есть функции от $x y$, устанавливаем тождественность
$phi$ на $T(q_(32)) + T(q_(21))$ по модулю $L_2$ с точностью до умножения на
диагональный и кольцевой автоморфизмы; на $T(p_(32)) + T(p_(21))$ по модулю
$L_2$ $phi$ индуцируется автоморфизмом кольца $K$, скажем, $pi$. Умножая $phi$
на $T(q_(31))$-сопряжение, добиваемся тождественности $phi$ на $q_(32)$ по
модулю $T(p_(31)) + T(q_(3,-2))$. Тогда
$
  [x q_(21),y q_(10)]^phi = x y^pi q_(20) + x (y^pi)^2 q_(2,-1),
$
$
  [x q_(21),y q_(10)]^phi compose [x y^2 q_(21),q_(10)]^phi
  &= (x(y^2+y) q_(20))^phi \
  &= x(y^2+y^pi) q_(20) + x(y^2+(y^2)^pi) q_(2,-1), \
  quad q_(31)^phi = q_(31) quad ("mod" Z_6);
$
$
  0 = [q_(31)^phi,((y^2+y) q_(20))^phi]
  = (y^2+(y^2)^pi) q_(3,-2) quad "mod" L_6,
  quad (y^2)^pi = y^2 quad (y in K).
$
Отсюда $phi = 1 "mod" L_2$, а на $T(q_(20))$ $phi$ единичен по модулю
$Z_6 (= T(q_(30)) + T(p_(3,-1)))$.

Из изоморфизма $(K q_(i,i-1))^phi approx K^+$ следует $phi$-инвариантность
подгрупп $T(q_(i,i-1))$, $i = 1,2$. Если $x^mu$ есть $p_(31)$-координата
элемента $(x q_(32))^phi$, то $p_(3,-1)$- и $q_(43)$-координаты элемента
$[x q_(32),y q_(21)]^phi$ равны соответственно $y x^mu$ и $y(x^mu)^2$. В силу их
симметричности, $x^mu = 1^mu x$, $1^mu(x^2-x) = 0$, $x in K$. При условии
$Ann_K cal(J)_2 = 0$ должны иметь $1^mu = 0$, $mu = 0$. То же самое верно и
когда $cal(J)_2 = 0$; действительно, умножая $phi$ на внутренний автоморфизм,
можем добиться условий $q_(32)^phi = q_(32) + 1^mu p_(31) "mod" T(q_(3,-2))$,
$q_(21)^phi = q_(21) "mod" L_4$ и, следовательно,
$
  q_(31)^phi = [q_(32)^phi,q_(21)^phi]
  = q_(31) compose 1^mu p_(3,-1) compose (1^mu)^2 q_(43)
  quad "mod" T(p_(42)),
$
$
  #source(17, printed: 156)0 = q_(31)^phi compose q_(31)^phi
  = (1^mu)^2 q_(41), quad 1^mu = 0.
$
В обоих случаях с помощью изоморфизма $(K q_(32))^phi approx K^+$ приходим к
$phi$-инвариантности подгруппы $T(q_(32))$. Аналогично $T(p_(32))$ —
$phi$-инвариантная подгруппа. Далее вычисления показывают, что при условии
$Ann_K cal(J)_2 = 0$ умножением на внутренний и центральный автоморфизмы $phi$
приводится к автоморфизму вида:
$
  cases(
    reverse: #true,
    t q_(10) -> t q_(10) + (a t^2 + b t) q_(4,-1),
    t q_(21) -> t q_(21) + d sqrt(t^2-t) p_(4,-1) quad (t in K),
    t q_(20) -> t(q_(20) + b q_(4,-2) + d p_(4,-2)),
    t q_(2,-1) -> t(q_(2,-1) + a q_(4,-2)) + d sqrt(t) p_(4,-2),
    t q_(30) -> t(q_(30) + b q_(4,-3)),
    t q_(3,-1) -> t(q_(3,-1) + a q_(4,-3)),
    t p_(3,-1) -> t(p_(3,-1) + d p_(4,-3)),
  )
$ <eq:l1990-small-f4-exceptional>
который определён для любых параметров $a,b,d in K$. С другой стороны, когда
$cal(J)_2 = 0$ или, равносильно, $x^2 = x$ $(x in K)$, умножением на стандартный
и вида @eq:l1990-small-f4-exceptional автоморфизмы $phi$ приводится к
автоморфизму вида:
$
  t q_(32) -> t(q_(32) + k q_(4,-1)),
  quad t q_(31) -> t(q_(31) + k q_(4,-1) + k q_(4,-3)) \
  quad (t in K), \
  t p_(32) -> t(p_(32) + m q_(41)),
  quad t p_(31) -> t(p_(31) + m q_(40) + m q_(4,-1)), \
  t p_(3,-3) = t q_(43) -> t(q_(43) + m q_(4,-2)),
  quad t q_(42) -> t(q_(42) + m q_(4,-3)).
$ <eq:l1990-small-f4-boolean>
Легко убедиться, что отображение @eq:l1990-small-f4-boolean при
$k,m in Ann_K cal(J)_2$ всегда определяет автоморфизм. Итак, доказана

#theorem[
  Пусть $phi$ — автоморфизм группы $N F_4(K) approx U F_4(K)$, где $K$ —
  совершенное кольцо характеристики 2. Если аннулятор множества
  $lr({x^2-x | x in K})$ в $K$ нулевой, то $phi$ есть произведение
  идемпотентно-графового, стандартного и вида @eq:l1990-small-f4-exceptional
  автоморфизмов. Когда $x^2 = x$ $(x in K)$, в разложение добавляется лишь
  автоморфизм вида @eq:l1990-small-f4-boolean.
] <th:l1990-small-f4-perfect>

=== #[ ] <sec:l1990-small-twisted-f4>

Пусть $K$ — кольцо с автоморфизмом $overline(quad)$ таким, что
$overline(overline(x))^2 = x$, $x in K$. Исходя из основных соотношений в группе
$N F_4(K)$, находим основные соотношения в её подгруппе
$N twisted(2, F_4)(K) approx U twisted(2, F_4)(K)$, порождаемой элементами:
$
  R_(i j) lr((t)) = overline(t) p_(i j) compose t q_(i j),
  quad (i,j) = (2,-1),(3,2),(3,-2)
  "или" -2 <= -j < i = 4, quad j != 0,
$ <pass:l1990-small-twisted-f4-elements>
$
  #source(18, printed: 157)R_(i j) lr((t))
  = overline(t) p_(i j) compose t q_(i j) compose overline(t) t p_(i,-j),
  quad (i,j) = (2,1) "или" (4,3),
$
$
  R_(3 sigma) lr((t))
  = overline(t) p_(3 sigma) compose t q_(3 sigma)
  compose overline(t) t p_(4,2sigma),
  quad abs(sigma) = 1, quad t in K;
$
$m$-й член стандартного центрального ряда группы $N twisted(2, F_4)(K)$
порождается элементами, соответствующими в таблице #table(
  columns: 8,
  align: center,
  stroke: none,
  $R_(21)$, $R_(2,-1)$, $R_(3,-1)$, $R_(3,-2)$, [], [], [], [],
  $R_(32)$,
  $R_(31)$,
  $R_(43)$,
  $R_(42)$,
  $R_(41)$,
  $R_(4,-1)$,
  $R_(4,-2)$,
  $R_(4,-3)$,
) <pass:l1990-small-twisted-f4-series>
«корням» $R_(i j)$ из столбцов с номерами $>= m$ (нумерация слева направо).

#lemma[
  Группа $N twisted(2, F_4)(K)$ изоморфна группе $U twisted(2, F_4)(K)$.
  Основные соотношения в ней следующие:

  + $
      R_(i j) lr((a)) compose R_(i j) lr((b))
      = R_(i j) lr((a+b)) compose R_(i,-j) lr((a overline(b)^2)),
      quad (i,j) = (2,1),(4,3),
    $
    $
      R_(3 sigma) lr((a)) compose R_(3 sigma) lr((b))
      = R_(3 sigma) lr((a+b)) compose R_(4,2sigma) lr((a overline(b)^2)),
      quad abs(sigma) = 1,
    $
    $R_(i j) lr((a)) compose R_(i j) lr((b)) = R_(i j) lr((a+b))$ — в остальных
    случаях;

  + $[R_(i k) lr((a)),R_(j m) lr((b))] = 0$ в случаях: а)
    $lr({i,abs(k),abs(m),j}) = lr({1,2,3,4})$; б) $i = j != 3$, $k != m$, в)
    $i = j = 3$, $k m = -1$ или $2$, г) $i = 4$, $j = 3$, $k = m$, д) $k < 0$,
    $m < 0$, $(i,k) != (3,-1)$, е) $k = -j$;

  + $
      [R_(i sigma) lr((a)),R_(j,-sigma) lr((b))]
      = R_(i,-j) lr((a b)),
      quad 1 <= abs(sigma) < j < i <= 4, quad (i,sigma) != (3,1);
    $

  + $
      [R_(31) lr((a)),R_(2,-1) lr((b))]
      = R_(3,-2) lr((a b)) compose R_(4,-2) lr((a overline(a b)^2))
      compose R_(4,-3) lr(((overline(a) a)^2 b)),
    $
    $
      [R_(32) lr((a)),R_(3,-2) lr((b))]
      = R_(41) lr((overline(a)^2 b))
      compose R_(4,-1) lr((a overline(b)^2));
    $

  + $
      [R_(32) lr((a)),R_(3,-1) lr((b))]
      = R_(42) lr((overline(a)^2 b))
      compose R_(41) lr((a overline(b)^2))
      compose R_(4,-3) lr((a overline(b)^2 b)),
    $
    $
      [R_(3,-2) lr((a)),R_(31) lr((b))]
      = R_(4,-2) lr((overline(a)^2 b))
      compose R_(4,-1) lr((a overline(b)^2))
      compose R_(4,-3) lr((overline(b)^2 a b));
    $

  + $
      [R_(31) lr((a)),R_(21) lr((b))]
      = R_(3,-2) lr((a b overline(b)^2))
      compose R_(43)^(-1) lr((overline(a)^2 b))
      compose R_(3,-1) lr((a overline(b)^2))
      compose R_(41) lr((overline(a)^2 a b));
    $

  + $
      [R_(41) lr((a)),R_(21) lr((b))]
      = R_(4,-1) lr((a overline(b)^2))
      compose R_(4,-2) lr((a b overline(b)^2))
      compose R_(4,-3) lr((overline(a)^2 b));
    $

  + $
      [R_(43) lr((a)),R_(3 sigma) lr((b))]
      = R_(4 sigma) lr((a b)), quad 1 <= abs(sigma) <= 2;
    $

  + $
      [R_(42) lr((a)),R_(21) lr((b))]
      = R_(41) lr((a b)) compose R_(4,-2) lr((a(b overline(b))^2))
      compose R_(4,-3) lr((overline(a b)^2 b)),
    $
    $
      [R_(42) lr((a)),R_(2,-1) lr((b))]
      = R_(4,-1) lr((a b)) compose R_(4,-2) lr((a overline(b)^2))
      compose R_(4,-3) lr((overline(a)^2 b));
    $

  + $
      #source(19, printed: 158) [R_(32) lr((a)),R_(21) lr((b))]
      = R_(43) lr((b overline(a b)^2)) compose R_(31)^(-1) lr((a b))
      compose R_(3,-2) lr((a(overline(b) b)^2)) \
      compose R_(4,-1) lr((a overline(a)^2 b^2 overline(b)^4))
      compose R_(4,-2) lr((a overline(a)^2 b^3 overline(b)^4));
    $

  + $
      [R_(32) lr((a)),R_(2,-1) lr((b))]
      = R_(3,-1) lr((a b)) compose R_(43)^(-1) lr((overline(a)^2 b))
      compose R_(3,-2) lr((a overline(b)^2)) \
      compose R_(41) lr((a overline(a b)^2))
      compose R_(42) lr((overline(a)^2 a b)).
    $
] <lem:l1990-small-twisted-f4-relations>

С помощью леммы @lem:l1990-small-twisted-f4-relations легко устанавливается
стандартность верхнего и нижнего центрального рядов группы
$N twisted(2, F_4)(K)$ над полем $K$ (см. лемму
@lem:l1990-small-twisted-central-series). Произвольный её автоморфизм $phi$
индуцирует автоморфизм фактор-группы
$frac(N twisted(2, F_4) lr((K)), C lr((Z_3)))$, которая изоморфна унитреугольной
группе $UT(3, K)$, в силу леммы @lem:l1990-small-twisted-f4-relations и равенств
$
  C lr((Z_2)) = R_(21) lr((K)) compose Gamma_2,
  quad C lr((Z_3)) = R_(2,-1) lr((K)) compose Gamma_3,
  quad C_("mod" Z_1) lr((Z_3)) = R_(32) lr((K)) compose Gamma_2.
$
В силу этих же равенств и теоремы @th:l1983-rank-three
[@bib:l1990-small-Levchuk1983], $phi$ единичен по модулю коммутанта $Gamma_2$ с
точностью до умножения на диагональный и кольцевой автоморфизмы. Далее,
используя инвариантность основных соотношений, умножением на внутренний
автоморфизм удаётся добиться тождественности $phi$ по модулю центра. Таким
образом, справедлива

#theorem[
  Всякий автоморфизм группы $U twisted(2, F_4)(K)$ над полем $K$ (с
  нетривиальным автоморфизмом $overline(quad)$) разложим в произведение
  диагонального, кольцевого, внутреннего и центрального автоморфизмов.
] <th:l1990-small-twisted-f4>

=== #[ ] <sec:l1990-small-d4>

Пусть $Phi$ — система корней типа $D_4$; $q$ — её простой корень, неподвижный
относительно всех симметрий графа Кокстера; $r_1$, $r_2$, $r_3$ — остальные
простые корни. Знаки структурных констант здесь можем выбрать с помощью
тождества Якоби так, что при $1 <= i,j <= 3$, $i != j$,
$
  1 = c_(q,r_i) = c_(q+r_i,r_j) = c_(q+r_i,s-r_i)
  = c_(s-r_i,r_i) = c_(s q) quad (s = q+r_1+r_2+r_3).
$
Группа $UT(4, K)$ изоморфна фактор-группам $frac(U D_4 lr((K)), T lr((r_i)))$, и
методы [@bib:l1990-small-Levchuk1983] её исследования переносятся на группу
$U D_4(K)$. В последней подгруппа $T(q)$ характеристична, поскольку она есть
единственная максимальная абелева по модулю центра нормальная подгруппа,
содержащая коммутант. Кроме того, $C lr((Z_2)) = T(r_1) T(r_2) T(r_3)$. Как и в
доказательстве леммы 14 и теоремы @th:l1983-rank-four
[@bib:l1990-small-Levchuk1983], для автоморфизма $phi$ группы $U D_4(K)$, с
точностью до его умножения на диагональный, внутренний и кольцевой автоморфизмы,
существуют матрицы $beta = norm(b_(u v)) in "SL"(3,K)$ и $lambda_i in End K^+$
такие, что $1^(lambda_i) = 0$ $(i = 1,2,3)$ и
$
  #source(20, printed: 159)x_(r_i)^phi lr((t))
  = product_(m=1)^3 x_(r_m) lr((b_(i m) t)) quad "mod" Gamma_2,
  quad x_q^phi lr((t))
  = x_q lr((t)) product_(k=1)^3 x_(q+r_k) lr((t^(lambda_k)))
  quad "mod" Gamma_3;
$
$q+r_m+r_k$-координата элемента $x_(q+r_i)^phi lr((z t))$ равна
$t^(lambda_k) b_(i m) z + t^(lambda_m) b_(i k) z + b_(i m) b_(i k) z^2 t$
и является функцией от произведения $z t$. Отсюда
$t^(lambda_k) = (t^2-t) sum_(i=1)^3 A_(i m) b_(i m) b_(i k)$
($A_(i m)$ — алгебраическое дополнение к $b_(i m)$ в матрице $beta$) и
$b_(i m) b_(i k) cal(J)_2 cal(J)_2 = 0$, $m != k$. Если $K$ — область
целостности и $beta$ — немономиальная матрица, то должны иметь $cal(J)_2 = 0$ и
$K = GF(2)$. Изоморфизм $X_(q+r_i) approx K^+$ и перестановочность друг с другом
элементов $x_(q+r_i) lr((t))$ $(i = 1,2,3)$ дают:
$
  0 & = b_(i 1) b_(i 2) b_(i 3) \
    & = b_(i 1) b_(j 2) b_(j 3) + b_(i 2) b_(j 3) b_(j 1)
      + b_(i 3) b_(j 1) b_(j 2) \
    & + b_(j 1) b_(i 2) b_(i 3)
      + b_(j 2) b_(i 3) b_(i 1) + b_(j 3) b_(i 1) b_(i 2) quad (i != j).
$ <eq:l1990-small-d4-matrix-condition>

С другой стороны, матрице $beta in "SL"(3,2)$ с условием
@eq:l1990-small-d4-matrix-condition соответствует автоморфизм $tilde(beta)$
группы $U D_4(K)$, оставляющий на месте $x_q lr((t))$ и переводящий
$x_(r_i) lr((t))$ в
$
  product_(m=1)^3 x_(r_m) lr((b_(i m) t))
  product_(1 <= m < k <= 3) x_(q+r_k+r_m) lr((b_(i m) b_(i k) t)),
  quad i = 1,2,3.
$
Очевидно, матрицы $beta$ из $"SL"(3,2)$ с условием
@eq:l1990-small-d4-matrix-condition образуют подгруппу, изоморфную
симметрической группе подстановок степени 4. Несложно описываются автоморфизмы
группы $U D_4(K)$, единичные по модулю коммутанта. Отсюда вытекает

#theorem[
  Всякий автоморфизм группы $U D_4(2)$ есть произведение внутреннего и
  центрального автоморфизмов на автоморфизм
  $tilde(beta) dot ell_1 lr((d_1)) dot ell_2 lr((d_2)) times
  ell_3 lr((d_3))$ для некоторых $d_1,d_2,d_3 in GF(2)$ и матрицы
  $beta = norm(b_(u v)) in "SL"(3,2)$ с условием
  @eq:l1990-small-d4-matrix-condition, где
  $
    ell_i lr((d)) colon x_q lr((t)) -> x_q lr((t)) x_(s-r_i) lr((d t)),
    quad x_(q+r_i) lr((t))
    -> x_(q+r_i) lr((t)) x_s lr((d t)) x_(s+q) lr((d t^2)),
  $
  $t in K$, $s = q+r_1+r_2+r_3$. Всякий автоморфизм группы $U D_4(K)$ над
  областью целостности $K$, $abs(K) > 2$, есть произведение стандартного и (при
  $2K != 0$) вида @eq:l1990-small-extremal-automorphism автоморфизмов.
] <th:l1990-small-d4-group>

#source(21, printed: 160)Аналогично описываются автоморфизмы лиева кольца
$N D_4(K)$.

#theorem[
  Всякий автоморфизм лиева кольца $N D_4(K)$ над коммутативным кольцом $K$ с 1
  есть произведение диагонального, кольцевого, внутреннего и центрального
  автоморфизмов на автоморфизм
  $
    t e_q -> t(e_q + c e_s + sum_(m=1)^3 d_m e_(s-r_m)),
    quad t e_(q+r_i) -> t(e_(q+r_i) + d_i e_s), quad t in K,
  $
  для произвольных $c,d_i in K$, $2d_i = 0$, $i = 1,2,3$, и на автоморфизм
  $
    t e_(r_i) -> t sum_(m=1)^3 b_(i m) e_(r_m),
    quad t e_(q+r_i+r_j) -> t dot per mat(
      delim: "[",
      b_(i 1), b_(i 2), b_(i 3);
      b_(j 1), b_(j 2), b_(j 3);
      e_(s-r_1), e_(s-r_2), e_(s-r_3),
    ),
  $
  $
    t e_q -> t e_q,
    quad t e_(q+r_i) -> t sum_(m=1)^3 b_(i m) e_(q+r_m),
    quad A -> (per beta) A quad (A in L_2, quad t in K, quad i != j)
  $
  для произвольной матрицы $beta = norm(b_(u v)) in "SL"(3,K)$ с условием
  $2b_(m j) b_(m i) = 0$, $1 <= i,j,m <= 3$, $i != j$ ($per beta$ — перманент
  матрицы $beta$).
] <th:l1990-small-d4-lie>
