#import "../../main-defs.typ": source, twisted
#import "defs.typ": *

=== Финитарные унипотентные группы <sec:l2009-finitary-finitary>
По аналогии с унитреугольными группами рассмотрим финитарные обобщения
унипотентных групп $U G(K)$ классических типов.

Классическая присоединенная группа кольца $NT(n, K)$ нильтреугольных
$n times n$-матриц над $K$ с присоединенным умножением
$alpha compose beta = alpha + beta + alpha beta$ допускает изоморфизм
$alpha arrow e+alpha$ на унитреугольную группу $UT(n, K)$, где $e$~— единичная
матрица. Пусть $Gamma$~— произвольная цепь (линейно упорядоченное множество) с
отношением порядка $<=$. Обобщенная унитреугольная группа $UT(Gamma, K)$
исследуется в [@bib:l2009-finitary-Levchuk1987, @bib:l2009-finitary-Levchuk1992,
@bib:l2009-finitary-Levchuk2005] как присоединенная группа финитарного кольца
$NT(Gamma, K)$, которое взаимосвязано с ассоциированным кольцом Ли, а в
[@bib:l2009-finitary-Merzlyakov1994] она изучается как подгруппа
мультипликативной группы $GL(Gamma, K)$ обратимых финитарных $Gamma$-матриц над
$K$. Подгруппу $SL(Gamma, K)$ в $GL(Gamma, K)$ образуют $Gamma$-матрицы, равные
единичной $Gamma$-матрице, за исключением элементов из какой-либо клетки
$lr(‖a_(i j)‖) in SL(Gamma_1, K)$ с подходящей конечной подцепью $Gamma_1$ в
$Gamma$. Для бесконечной цепи $Gamma$ группа $SL(Gamma, K)$ имеет единичный
центр и является простой группой при любом выборе основного поля.

Обобщенные классические (унитарные, симплектические и ортогональные) группы
естественно выделяются в группах $GL(Gamma, K)$ и $SL(Gamma, K)$.

Пусть $Gamma$~— произвольная цепь (линейно упорядоченное множество) с
фиксированной антиизометрией $'$ на новую цепь. Образуем новую цепь
$tilde(Gamma) = Gamma' union Gamma$, полагая $i'' = i$ и $i' <= j$ для всех
$i, j in Gamma$. Если $Gamma$ и $Gamma'$ содержат общий элемент, то он
единствен. Его обозначаем через 0 (или $0'$), а через $N B_Gamma lr((K))$~—
$K$-модуль с базисом
$ {e_(i m) | i in Gamma, m in tilde(Gamma), i' < m < i}. $
При $Gamma' inter Gamma = emptyset$ обозначим $K$-модуль с такой же записью
базиса через $N D_Gamma lr((K))$, а $K$-модуль с базисом
${e_(i m) | i in Gamma, m in tilde(Gamma), i' <= m < i}$~— через
$N C_Gamma lr((K))$. Умножение $*$ определяет произведения базисных элементов:
$
  e_(i j) * e_(j v) = e_(i v); quad e_(i j) * e_(k t) = 0,
  quad j != k, i != t, t != j';
  \ e_(i 0) * e_(j 0) = 2e_(i j') quad (G = B_Gamma);
  quad e_(i j) * e_(i j') = 2e_(i i') quad (G = C_Gamma),
  quad i > j in Gamma;
  \ e_(i m) * e_(j m') = e_(i j'), quad j' < m < j < i,
  quad j != 0, quad e_(i m) * e_(i m') = 0 quad (G = B_Gamma, D_Gamma);
  \ e_(j k) * e_(i k') = e_(i k) * e_(j k') = e_(i j'),
  quad i > j > k in Gamma quad (G = C_Gamma).
$

#lemma[
  $K$-модули $N G(K)$ типа $G = B_Gamma$, $C_Gamma$ или $D_Gamma$ с умножением
  $*$ являются алгебрами Ли. Для конечной цепи $Gamma$ с условиями
  $|Gamma without (Gamma' inter Gamma)| = n$ алгебра $N G(K)$ изоморфна лиевой
  алгебре, соответственно, $N B_n lr((K))$, $N C_n lr((K))$ или $N D_n lr((K))$.
] <lem:l2009-finitary-classical-lie-algebras>

#proof[
  Поскольку всякое конечное множество элементов, скажем, $K$-модуля
  $N B_Gamma lr((K))$ лежит в подмодуле того же типа $N B_(Gamma_1) lr((K))$ для
  подходящей конечной подцепи $Gamma_1$ в $Gamma$, то достаточно доказать второе
  утверждение леммы. Заметим, что любая конечная #source(5, printed: 137) цепь
  $Gamma$ с условиями $|Gamma without (Gamma' inter Gamma)| = n$ и $i' <= j$
  $(i, j in Gamma)$ изоморфна цепи целых чисел ${0, 1, 2, dots, n}$ или
  ${1, 2, dots, n}$ с антиизометрией $i' = -i$ в обоих случаях.

  Системы корней классического типа $A_(n-1)$, $B_n$, $C_n$ и $D_n$ выберем, как
  обычно, в евклидовом пространстве с ортонормированным базисом
  $epsilon_1, epsilon_2, dots, epsilon_n$, см.
  табл.~@tab:l2009-finitary-classical-roots.

  Положительные корни систем классических типов записываются в виде
  $
    epsilon_i - m epsilon_j = p_(i, m j), quad 1 <= j <= i <= n,
    quad m in {0, -1, +1}.
  $
  Сумма корней $p_(i v) + p_(k t)$ есть корень в тех случаях, когда $v = k$ или
  $t = i$, или $v = -t$; в последнем случае требуем еще $i != k$ или
  $Phi = C_n$.

  #figure(
    table(
      columns: (auto, 1fr, 1fr),
      table.header($Phi$, $Phi^+$, $Pi$),
      $A_n$,
      $epsilon_i-epsilon_j quad (1 <= j < i <= n+1)$,
      $epsilon_(j+1)-epsilon_j quad (1 <= j <= n)$,

      $B_n$,
      $epsilon_i quad (1 <= i <= n),
      epsilon_i plus.minus epsilon_j quad (1 <= j < i <= n)$,
      $epsilon_1, epsilon_(j+1)-epsilon_j quad (1 <= j < n)$,

      $C_n$,
      $2epsilon_i quad (1 <= i <= n),
      epsilon_i plus.minus epsilon_j quad (1 <= j < i <= n)$,
      $2epsilon_1, epsilon_(j+1)-epsilon_j quad (1 <= j < n)$,

      $D_n$,
      $epsilon_i plus.minus epsilon_j quad (1 <= j < i <= n)$,
      $epsilon_2+epsilon_1, epsilon_(j+1)-epsilon_j quad (1 <= j < n)$,
    ),
    kind: table,
    caption: [Системы корней классического типа],
  ) <tab:l2009-finitary-classical-roots>

  Полагая для элементов $e_r$ базиса Шевалле $psi(e_r) = e_(i, m j)$ при
  $r = p_(i, m j)$ (где $e_(i, m j)$~— элемент базиса алгебры $N G(K)$) и
  выбирая знаки структурных констант согласно [@bib:l2009-finitary-Carter1972,
  предложение 4.2.2], получаем требуемый во втором утверждении изоморфизм
  $K$-алгебр. Это завершает доказательство леммы.
]

Далее, всякий элемент $K$-алгебры $N Phi(K)$ отождествляем с его образом
относительно изоморфизма $psi$ и распространяем групповую операцию $compose$ на
алгебры $N G(K)$ типа $G = B_Gamma$, $C_Gamma$ или $D_Gamma$ с любой цепью
$Gamma$.

Записывая элемент алгебры $N Phi(K)$ типа $B_n$, $C_n$ или $D_n$ суммой
$sum a_(i v) e_(i v)$, представляем его $Phi^+$-матрицей $lr(‖a_(i v)‖)$ над
$K$. Так, $B_n^+$-матрица имеет вид
$
  a_(1 0)
  \ a_(2,-1) quad a_(2 0) quad a_(2 1)
  \ dots quad dots quad dots
  \ a_(n,-n+1) dots a_(n,-1) quad a_(n 0) quad a_(n 1) dots a_(n,n-1).
$
Отбрасывая здесь нулевой столбец, получаем $D_n^+$-матрицу.

Скрученная группа, как присоединенная группа $ker(1-sigma)$-модуля $N G(K)$,
представлена в [@bib:l2009-finitary-Levchuk1990] при $G = twisted(2, D_(n+1))$
или $twisted(2, A_(2n-1))$, соответственно, $B_n^+$-матрицами или
$C_n^+$-матрицами. При $G = twisted(2, A_(2n))$ она представлена
$B C_n^+$-матрицами
$
  a_(1,-1) quad a_(1 0)
  \ a_(2,-2) quad a_(2,-1) quad a_(2 0) quad a_(2 1)
  \ #source(6, printed: 138) dots quad dots quad dots
  \ a_(n,-n) dots a_(n,-2) quad a_(n,-1) quad a_(n 0)
  quad a_(n 1) dots a_(n,n-1).
$
($C_n^+$-матрицу получаем, отбрасывая здесь нулевой столбец.)

Таким образом, $K_sigma$-модули $N G(K)$ типа $G = twisted(2, D_Gamma)$ или
$twisted(2, A_(tilde(Gamma)))$ и их присоединенные группы построены для любой
конечной цепи $Gamma$. Это означает, как и выше, что они определены и для
произвольной цепи $Gamma$.

Используя [@bib:l2009-finitary-Levchuk1990, леммы
@lem:l1990-chevalley-classical-commutators,
@lem:l1990-chevalley-twisted-d-relations и
@lem:l1990-chevalley-twisted-a-relations] (см. также
[@bib:l2009-finitary-Levchuk1992]), находим описание определяющих соотношений
присоединенных групп в терминах порождающих «корневых» элементов:
$
  N twisted(2, A_Gamma) lr((K)) = chevron.l x e_(i v), z e_(i i') |
  x in K, z in ker(1+sigma), i, v in tilde(Gamma), i' < v < i chevron.r,
  \ N twisted(2, D_Gamma) lr((K)) = chevron.l x e_(i 0), z e_(i v) |
  x in K, z in ker(1-sigma), i, v in tilde(Gamma),
  i' < v < i, v != 0 chevron.r.
$

#theorem[
  Всякое соотношение в присоединенной группе $chevron.l N G(K), compose
  chevron.r$ типа $G = B_Gamma$, $C_Gamma$, $D_Gamma$ или $twisted(2, D_Gamma)$
  есть следствие соотношений в $K$ и следующих соотношений:
  $ x e_(i v) compose y e_(i v) = (x+y)e_(i v); $
  <eq:l2009-finitary-root-addition>
  $ [x e_(i k), y e_(j t)] = 0, quad j != k, i != t, t != k'; $
  <eq:l2009-finitary-disjoint-commutator>
  $ [x e_(i j), y e_(j v)] = x y e_(i v), quad v != 0, v != j'; $
  <eq:l2009-finitary-chain-commutator>
  $
    G = B_Gamma, D_Gamma, twisted(2, D_Gamma): quad
    [x e_(j v), y e_(i v')] = cases(
      x y e_(i j') & i > j comma v != 0,
      0 & i = j,
    )
  $
  $
    G = B_Gamma: quad [x e_(i j), y e_(j 0)]
    = x y e_(i 0) + x y^2 e_(i j'),
    quad [x e_(i 0), y e_(j 0)] = 2x y e_(i j');
  $
  $
    G = twisted(2, D_Gamma): quad [x e_(i j), y e_(j 0)]
    = x y e_(i 0) + x y overline(y) e_(i,-j),
    \ [x e_(i 0), y e_(j 0)] = (x overline(y)+overline(x)y)e_(i,-j),
    quad i > j > 0;
  $
  $
    G = C_Gamma: quad [x e_(i k), y e_(j k')]
    = [x e_(j k), y e_(i k')] = x y e_(i j'), quad i > j > k in Gamma,
    \ [x e_(i j), y e_(j j')] = x y e_(i j')-x^2 y e_(i i'),
    quad [x e_(i j), y e_(i j')] = 2x y e_(i i'), quad i > j in Gamma.
  $
  Определяющими в группе $N twisted(2, A_(tilde(Gamma))) lr((K))$ являются
  соотношения @eq:l2009-finitary-root-addition при $v != 0$,
  @eq:l2009-finitary-disjoint-commutator, @eq:l2009-finitary-chain-commutator и
  следующие соотношения:
  $
    x e_(i 0) compose y e_(i 0) = (x+y)e_(i 0) compose
    (tilde(x)+tilde(y)-tilde(x+y)+overline(x)y)e_(i,-i), quad i > 0;
    \ [x e_(j v), y e_(i,-v)] = overline(x)y e_(i,-j),
    \ [x e_(i j), y e_(j 0)] = x y e_(i 0) compose
    (-x overline(tilde(y)))e_(i,-j) compose
    (x overline(x) overline(tilde(y))-x y)e_(i,-i),
    \ [x e_(i j), y e_(i,-j)] = (overline(x)y-x overline(y))e_(i,-i),
    \ [x e_(i j), z e_(j,-j)] = x z e_(i,-j)-overline(x)x z e_(i,-i),
    quad i > j > 0.
  $
] <th:l2009-finitary-defining-relations>

В случае финитарной унитреугольной группы $UT(Gamma, K)$ обобщение диагональных
и внутренних автоморфизмов дает переход к сопряжениям слабо финитарными
обратимыми треугольными $Gamma$-матрицами над $K$
[@bib:l2009-finitary-Levchuk1987, @bib:l2009-finitary-Levchuk1992,
@bib:l2009-finitary-Levchuk2005], в том числе, к локально внутренним
автоморфизмам [@bib:l2009-finitary-Gorchakov1978]. Аналогично расширяется
понятие стандартного автоморфизма финитарной унипотентной подгруппы $U G(K)$
типа $G = B_Gamma$ и так далее.

Выделенные в разд.~@sec:l2009-finitary-preliminaries гиперцентральные
автоморфизмы несложно переносятся сначала на построенный матричный язык, а затем
и на финитарный случай, когда их высота определяется наименьшим числом $m$ с
точностью до умножения на локально внутренние автоморфизмы.

Перенесение описания автоморфизмов на финитарный случай основываем на том, что
всякое конечное множество элементов финитарного модуля $N G(K)$ лежит в
подмодуле того же типа соответствующего подходящей конечной подцепи $Gamma_1$ в
$Gamma$. Таким образом, приходим к следующей теореме.

#source(7, printed: 139)
#theorem[
  Всякий автоморфизм финитарной унипотентной группы $U G(K)$ над полем $K$ типа
  $G = A_Gamma$, $B_Gamma$, $C_Gamma$, $D_Gamma$, $twisted(2, A_Gamma)$ или
  $twisted(2, D_Gamma)$ равен произведению $mu chi$, где $mu$~— стандартный
  автоморфизм, а $chi$~— локально гиперцентральный автоморфизм, когда $2K = 0$
  при $G = B_Gamma$ или $C_Gamma$, и гиперцентральный автоморфизм высоты $<=5$ в
  остальных случаях.
] <th:l2009-finitary-automorphisms>
